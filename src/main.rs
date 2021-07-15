#![allow(unused_imports)]
#![allow(unused_variables)]
extern crate belllady as bellman;
extern crate rand;
extern crate ff;
extern crate log;
extern crate memmap;
extern crate csv;
extern crate itertools;

use std::fs::OpenOptions;

use std::time::{Duration,Instant};

use ff::{Field,ScalarEngine};

use bellman::bls::{Bls12, Engine, Fr, FrRepr};
use rand::thread_rng;

use memmap::MmapOptions;
use std::fs::File;
use std::io::{Seek, SeekFrom, Write};
use rand_core::{SeedableRng, RngCore};
use rayon::iter::{ParallelIterator,IntoParallelRefIterator};
use serde::Serialize;

use itertools::Itertools;

use bellman::groth16::{
    aggregate::{
        aggregate_proofs_and_instances, setup_fake_srs, verify_aggregate_proof,
        verify_aggregate_proof_and_aggregate_instances, AggregateProof, GenericSRS,
    },
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    verify_proofs_batch, Parameters, Proof,
};

use log::*;

mod minroot;

fn main(){

//    minroot::minroot_test();

    let n_average = 1; // number of times we do the benchmarking to average out results
    let nb_proofs: usize = 128;
    let public_inputs = 4; // roughly what a prove commit needs
    let mut rng = rand_chacha::ChaChaRng::seed_from_u64(0u64);
    let niterations = minroot::MINROOT_ROUNDS * nb_proofs;

    // CRS for aggregation
    let generic: GenericSRS<Bls12> = setup_fake_srs(&mut rng, nb_proofs);
    // Create parameters for our circuit

    let params = {
        let c = minroot::MinRoot::<Bls12> {
            xl: None,
            xr: None,
        };

        generate_random_parameters(c, &mut rng).unwrap()
    };

    println!("params len {}", params.a.len());

    // verification key for indivdual verification of proof
    let pvk = prepare_verifying_key(&params.vk);



    let mut xl = <Bls12 as ScalarEngine>::Fr::random(&mut rng);
    let mut xr = <Bls12 as ScalarEngine>::Fr::random(&mut rng);

    println!("Computing VDF function for {} iterations", minroot::MINROOT_ROUNDS * nb_proofs);
    let start = Instant::now();

    let mut xl_cp = xl.clone();
    let mut xr_cp = xl.clone();


    for i in 0..nb_proofs {
        let xl_xr_new =  minroot::minroot::<Bls12>(xl_cp.clone(), xr_cp.clone()) ;
        xl_cp = xl_xr_new.0;
        xr_cp = xl_xr_new.1;
    }

    let vdf_compute_time = start.elapsed().as_millis();

    println!("Generating {} Groth16 proofs...", nb_proofs);
    let start = Instant::now();

    let public_inputs = [xl.clone(), xr.clone()].to_vec();

    let mut proofs: Vec<Proof<Bls12>> = Vec::new();
    let mut statements: Vec<Vec<Fr>> = Vec::new();

    let mut statement_circuit: (Vec<Fr>,minroot::MinRoot<Bls12>);

    for i in 0..nb_proofs {
        statement_circuit = generate_proof( xl, xr );

        xl = statement_circuit.0[2];
        xr = statement_circuit.0[3];

        proofs.push(create_random_proof(statement_circuit.1 , &params, &mut rng).unwrap());
        statements.push(statement_circuit.0);
    }

    let public_outputs = [xl.clone(), xr.clone()].to_vec();

    let groth16_prover_time = start.elapsed().as_millis();

    let file = OpenOptions::new().write(true).create(true).append(true).open("aggregation.csv").unwrap();
    let mut writer = csv::Writer::from_writer(file);
    // let mut writer = csv::Writer::from_path("aggregation.csv").expect("unable to open csv writer");

    let mut buf = Vec::new();
    proofs[0].write(&mut buf).expect("buffer");
    let proof_size = buf.len();
    let inclusion = vec![1, 2, 3];
    let mut records = Vec::new();
    for _ in 0..n_average {
        println!("Proofs {}", nb_proofs);
        let (pk, vk) = generic.specialize(nb_proofs);
        // Aggregate proofs using inner product proofs
        let start = Instant::now();
        println!("\t-Aggregation...");
        let mut aggregate_proof_and_instance = aggregate_proofs_and_instances::<Bls12>(
            &pk, &inclusion, &statements[..nb_proofs].to_vec(), &proofs[..nb_proofs])
            .expect("failed to aggregate proofs");
        let aggregate_proof = aggregate_proof_and_instance.pi_agg.clone();
        let prover_time = start.elapsed().as_millis();
        println!("\t-Aggregate Verification ...");

        let mut buffer = Vec::new();
        aggregate_proof.write(&mut buffer).unwrap();
        let start = Instant::now();
        let deserialized =
            AggregateProof::<Bls12>::read(std::io::Cursor::new(&buffer)).unwrap();

        let deserialized_time = start.elapsed().as_millis();
        println!("deserialized_time = {:?}", deserialized_time);

        aggregate_proof_and_instance.pi_agg = deserialized;
        let result = verify_aggregate_proof_and_aggregate_instances(
            &vk,
            &pvk,
            &mut rng,
            &public_inputs,
            &public_outputs,
            &aggregate_proof_and_instance,
            &inclusion,
        );

        let verifier_time = start.elapsed().as_millis();
        println!("result = {:?}, verifier_time = {:?}", result, verifier_time);

        println!("\t-Batch per 10 packets verification...");
        let batches: Vec<_> = proofs
            .iter()
            .cloned()
            .take(nb_proofs)
            .zip(statements.iter().cloned().take(nb_proofs))
            .chunks(10)
            .into_iter()
            .map(|s| s.collect())
            .collect::<Vec<Vec<(Proof<Bls12>, Vec<Fr>)>>>();
        let start = Instant::now();
        batches.par_iter().for_each(|batch| {
            let batch_proofs = batch.iter().by_ref().map(|(p, _)| p).collect::<Vec<_>>();
            let batch_statements = batch
                .iter()
                .map(|(_, state)| state.clone())
                .collect::<Vec<_>>();
            let mut rng = rand_chacha::ChaChaRng::seed_from_u64(0u64);
            assert!(
                verify_proofs_batch(&pvk, &mut rng, &batch_proofs, &batch_statements).unwrap()
            )
        });
        let batch_verifier_time = start.elapsed().as_millis();

        println!("\t-Batch all-in verification...");
        let proofs_serialized: Vec<Vec<_>> = proofs
            .iter()
            .take(nb_proofs)
            .map(|p| {
                let mut buff = Vec::new();
                p.write(&mut buff).unwrap();
                buff
            })
            .collect::<Vec<Vec<_>>>();
        let start = Instant::now();
        let proofs: Vec<_> = proofs_serialized
            .into_iter()
            .map(|buff| Proof::<Bls12>::read(std::io::Cursor::new(&buff)).unwrap())
            .collect::<Vec<_>>();
        let proofs_ref: Vec<_> = proofs.iter().collect();

        assert!(verify_proofs_batch(&pvk, &mut rng, &proofs_ref, &statements[..nb_proofs]).unwrap());
        let batch_all_time = start.elapsed().as_millis();
        let agg_size = buffer.len();
        records.push(Record {
            nproofs: nb_proofs as u32,
            niterations: niterations as u32,
            vdf_compute_ms: vdf_compute_time as u32,
            groth16_create_ms: groth16_prover_time as u32,
            aggregate_create_ms: prover_time as u32,
            aggregate_verify_ms: verifier_time as u32,
            aggregate_size_bytes: agg_size as u32,
            batch_verify_ms: batch_verifier_time as u32,
            batch_size_bytes: (proof_size * nb_proofs) as u32,
            batch_all_ms: batch_all_time as u32,
        });
    }
    let average = Record::average(&records);
    writer
        .serialize(average)
        .expect("unable to write result to csv");

    writer.flush().expect("failed to flush");

}

fn generate_proof(
    xl_old: <Bls12 as ScalarEngine>::Fr,
    xr_old: <Bls12 as ScalarEngine>::Fr,
) -> (Vec<Fr>, minroot::MinRoot<Bls12>) {


    let (image_xl, image_xr) = minroot::minroot::<Bls12>(xl_old, xr_old);

    // Create an instance of our circuit (with the
    // witness)
    let c = minroot::MinRoot::<Bls12> {
            xl: Some(xl_old),
            xr: Some(xr_old),
    };

    (vec![xl_old, xr_old, image_xl, image_xr], c)
}

// structure to write to CSV file
#[derive(Debug, Serialize, Default)]
struct Record {
    nproofs: u32,              // number of proofs that have been verified
    niterations: u32,           // number of iterations of delay function
    vdf_compute_ms: u32,     // time to create groth16 proofs
    groth16_create_ms: u32,     // time to create groth16 proofs
    aggregate_create_ms: u32,  // time to create the aggregated proof
    aggregate_verify_ms: u32,  // time to verify the aggregate proof
    batch_verify_ms: u32,      // time to verify all proofs via batching of 10
    batch_all_ms: u32,         // time ot verify all proofs via batching at once
    aggregate_size_bytes: u32, // size of the aggregated proof
    batch_size_bytes: u32,     // size of the batch of proof
}

impl Record {
    pub fn average(records: &[Record]) -> Record {
        let mut agg: Record = records.iter().fold(Default::default(), |mut acc, r| {
            acc.nproofs += r.nproofs;
            acc.niterations += r.niterations;
            acc.vdf_compute_ms += r.vdf_compute_ms;
            acc.groth16_create_ms += r.groth16_create_ms;
            acc.aggregate_create_ms += r.aggregate_create_ms;
            acc.aggregate_verify_ms += r.aggregate_verify_ms;
            acc.batch_verify_ms += r.batch_verify_ms;
            acc.batch_all_ms += r.batch_all_ms;
            acc.aggregate_size_bytes += r.aggregate_size_bytes;
            acc.batch_size_bytes += r.batch_size_bytes;
            acc
        });
        let n = records.len() as u32;
        agg.nproofs /= n;
        agg.niterations /= n;
        agg.vdf_compute_ms /= n;
        agg.groth16_create_ms /= n;
        agg.aggregate_create_ms /= n;
        agg.aggregate_verify_ms /= n;
        agg.batch_verify_ms /= n;
        agg.batch_all_ms /= n;
        agg.aggregate_size_bytes /= n;
        agg.batch_size_bytes /= n;
        agg
    }
}
