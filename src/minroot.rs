extern crate belllady as bellman;
extern crate rand;
extern crate ff;

use ff::{Field,ScalarEngine};


// For randomness (during paramgen and proof generation)
use self::rand::{thread_rng, Rng};

// We'll use these interfaces to construct our circuit.
use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError,
    bls::{Bls12,Engine},
};

use bellman::groth16::{
    self, create_random_proof_batch, generate_random_parameters,
    prepare_verifying_key, verify_proof, Proof,
    create_random_proof,
};

use std::time::{Duration,Instant};

pub const MINROOT_ROUNDS: usize = 10000;

//
pub fn minroot<E: Engine>(mut xl: E::Fr, mut xr: E::Fr) -> (E::Fr, E::Fr) {

//    println!(" x1 = {:?}, y1 = {:?}", xl, xr);
    for _ in 0..MINROOT_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&xr);

    //    power equals (2 * p - 1) / 5.  Don't delete this, was very hard to figure out.
        let tmp2 = tmp1.pow([
            0x33333332CCCCCCCD,
            0x217F0E679998F199,
            0xE14A56699D73F002,
            0x2E5F0FBADD72321C,
        ]);

        xr = xl;
        xl = tmp2;
    }

//    println!("x3 = {:?}, y3 = {:?}", xl, xr);

    (xl,xr)
}

fn fifth_root<E: Engine>(x: E::Fr) -> Option<E::Fr> {

    Some(x.pow([   0x33333332CCCCCCCD,
                       0x217F0E679998F199,
                       0xE14A56699D73F002,
                       0x2E5F0FBADD72321C,]))

}

// proving that I know x1, y1 such that x2^3  == (x1 + y1)
#[derive(Clone)]
pub struct MinRoot<E: Engine> {
    pub xl: Option<E::Fr>,
    pub xr: Option<E::Fr>,
}

/// Our circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<E: Engine> Circuit<E> for MinRoot<E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc_input(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;


        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc_input(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        for i in 0..MINROOT_ROUNDS {
            // xL, xR := (xL + xR)^(1/5), xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // power equals (2 * p - 1) / 5.

            let mut new_xl_value = None;
            if xl_value.is_none() {
            } else {
                let mut tmp1 = xl_value.unwrap();
                tmp1.add_assign( &xr_value.unwrap());
                new_xl_value = fifth_root::<E>(tmp1);
            }

            let new_xl = if i == (MINROOT_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
               cs.alloc_input(
                   || "image_xl",
                   || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
           } else {
               cs.alloc(
                   || "new_xl",
                   || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
               )?
           };

            // tmp2 = (xl_(i+1))^2
            let tmp2 = new_xl_value.map(|mut e| {
                e.square();
                e
            });

            // tmp3 = (xl_(i+1))^4
            let tmp3 = tmp2.map(|mut e| {
                e.square();
                e
            });


            let tmp2 = cs.alloc(
                || "tmp2",
                || tmp2.ok_or(SynthesisError::AssignmentMissing),
            )?;

            let tmp3 = cs.alloc(
                || "tmp3",
                || tmp3.ok_or(SynthesisError::AssignmentMissing),
            )?;

            let new_xr = if i == (MINROOT_ROUNDS - 1) {
                // This is the last round, xR is our image and so
                // we allocate a public input.
                cs.alloc_input(
                    || "image_xr",
                    || xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            } else {
                cs.alloc(
                    || "new_xr",
                    || xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            };

            // enforce that tmp2 = tmp1^2
            cs.enforce(
                || "tmp2 = new_xl^2",
                |lc| lc + new_xl,
                |lc| lc + new_xl,
                |lc| lc + tmp2,
            );

            // enforce that tmp3 = tmp2^2
            cs.enforce(
                || "tmp3 = tmp2^2",
                |lc| lc + tmp2,
                |lc| lc + tmp2,
                |lc| lc + tmp3,
            );

            // tmp3 * new_xl = new_xl^5 = xl + xr
            cs.enforce(
                || "new_xL^5 = xl + xr",
                |lc| lc + tmp3,
                |lc| lc + new_xl,
                |lc| lc + xl + xr,
            );

            // think this constraint isn't actually necessary because can just take in same witness wire.
            // new_xr = xl
    //        cs.enforce(
    //            || "new_xr = xl",
    //            |lc| lc + new_xr,
    //            |lc| lc + CS::one(),
    //            |lc| lc + xl,
    //        );

            // update xl and xr for next round
            xr = new_xr;
            xr_value = xl_value;

            xl = new_xl;
            xl_value = new_xl_value;

        }

        Ok(())
    }
}

// #[test]

fn _minroot_test() {
    fil_logger::init();

    let rng = &mut rand_core::OsRng;

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MinRoot::<Bls12> {
            xl: None,
            xr: None,
        };

        generate_random_parameters(c, rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    let mut proof_vec = vec![];
    let mut proofs = vec![];
    let mut images = vec![];

    for _ in 0..SAMPLES {

        // Generate a random preimage and compute the image
        let xl = <Bls12 as ScalarEngine>::Fr::random(rng);
        let xr = <Bls12 as ScalarEngine>::Fr::random(rng);
        let (image_xl, image_xr) = minroot::<Bls12>(xl, xr);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
        // Create an instance of our circuit (with the
        // witness)
            let c = MinRoot::<Bls12> {
                xl: Some(xl),
                xr: Some(xr),
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();
        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();

        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[xl, xr, image_xl, image_xr]).unwrap());
        total_verifying += start.elapsed();
        proofs.push(proof);
        images.push(vec![xl, xr, image_xl, image_xr]);
    }

    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
    proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
    verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:08}s", proving_avg);
    println!("Average verifying time: {:08}s", verifying_avg);

}
