use std::marker::PhantomData;

use ff::{Field, PrimeField};
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::bls::Engine;

const PREFIX: &str = "snarkpack-v1";

#[derive(Debug)]
pub struct Transcript<E: Engine> {
    hasher: Sha256,
    pub buffer: Vec<u8>,
    _e: PhantomData<E>,
}

/// A challenge derived from the transcript.
#[derive(Debug, Clone)]
pub struct Challenge<E: Engine>(E::Fr);

impl<E: Engine> Copy for Challenge<E> {}

impl<E: Engine> PartialEq for Challenge<E> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<E: Engine> Eq for Challenge<E> {}

impl<E: Engine> std::ops::Deref for Challenge<E> {
    type Target = E::Fr;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Engine> Serialize for Challenge<E> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<E: Engine> Transcript<E> {
    pub fn new(application_tag: &str) -> Self {
        let mut hasher = sha2::Sha256::new();
        hasher.update(PREFIX);
        hasher.update(application_tag);

        Transcript {
            hasher,
            buffer: Vec::new(),
            _e: Default::default(),
        }
    }

    pub fn write<S: Serialize>(mut self, el: &S) -> Self {
        bincode::serialize_into(&mut self.buffer, el).expect("vec");
        self.hasher.update(&self.buffer);
        self.buffer.clear();
        self
    }

    /// Generate a challenge from the transcript.
    pub fn into_challenge(mut self) -> Challenge<E> {
        let mut counter_nonce: usize = 0;
        let one = E::Fr::one();
        let r = loop {
            counter_nonce += 1;
            self.hasher.update(&counter_nonce.to_be_bytes()[..]);
            let curr_state = self.hasher.clone();
            let digest = curr_state.finalize();
            if let Some(c) = E::Fr::from_random_bytes(&digest) {
                if c == one {
                    continue;
                }
                if let Some(_) = c.inverse() {
                    break c;
                }
            }
        };

        Challenge(r)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bls::{Bls12, Engine, Fr, G1Affine, G2Affine, PairingCurveAffine};

    use ff::Field;
    use groupy::CurveAffine;

    #[test]
    fn test_transcript() {
        let mut t = Transcript::<Bls12>::new("test");
        let g1 = G1Affine::one();
        let g2 = G2Affine::one();
        let gt = <Bls12 as Engine>::final_exponentiation(&<Bls12 as Engine>::miller_loop(&[(
            &g1.prepare(),
            &g2.prepare(),
        )]))
        .expect("pairing failed");
        t = t.write(&g1).write(&g2).write(&gt).write(&Fr::one());

        let c1 = t.into_challenge();

        let t2 = Transcript::new("test")
            .write(&g1)
            .write(&g2)
            .write(&gt)
            .write(&Fr::one());

        let c12 = t2.into_challenge();
        assert_eq!(c1, c12);
    }
}
