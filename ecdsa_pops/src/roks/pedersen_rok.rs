//! RoK  of opening of Pedersen Commitment
//!     - RPedersen -> Rtrivial

use ark_std::{end_timer, start_timer};
use ff::PrimeField;
use halo2curves::{
    ff::Field,
    group::Curve,
    secp256r1::Secp256r1Affine,
    serde::{endian::EndianRepr, SerdeObject},
    CurveAffine,
};
use merlin::Transcript;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    errors::PopError,
    relations::rpedersen::{
        RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness,
    },
};

#[derive(Serialize, Deserialize, Debug)]
pub struct PedersenRoKProof<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the verifier's challenge
    challenge: C::Scalar,
    /// the prover's response
    response: Vec<C::Scalar>,
}

#[derive(Clone)]
/// The Pedersen [RoK] which reduces [RelPedersen] --> [RelTrivial]
pub struct PedersenRoK<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the commitment key used
    pub(crate) ck: Vec<C>,
}

impl<C> PedersenRoK<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// helper function to samples a random statement/witness pair for this commitment key
    fn sample_random_pair<R>(
        &self,
        pp: &RelPedersenParams<C>,
        rng: &mut R,
    ) -> (RelPedersenStatement<C>, RelPedersenWitness<C>)
    where
        R: RngCore + CryptoRng,
    {
        let opening: Vec<_> =
            pp.ck.iter().map(|_g| <C::Scalar as Field>::random(&mut *rng)).collect();

        let commitment = msm_function(&opening, &pp.ck).to_affine();

        let statement = RelPedersenStatement { C: commitment };
        let witness = RelPedersenWitness { m: opening };
        (statement, witness)
    }
}

impl<C> RoK for PedersenRoK<C>
where
    C: CurveAffine + SerdeObject,
    C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    type RelationSource = RelPedersen<C>;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = PedersenRoKProof<C>;
    type Error = PopError;

    fn label() -> String {
        "Pedersen Opening RoK".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters and the statement
        self.ck.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        transcript.append_point(b"statement", &rs.statement().C);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelPedersen<C>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| format!("Pedersen Opening RoK ({}) Prover", rs.params().ck.len()));

        self.initialize(rs, transcript);

        // sample a random statement
        let (x_r, w_r) = self.sample_random_pair(rs.params(), rng);

        // append the random statement
        transcript.append_point(b"first message", &x_r.C);

        // get challenge
        let c: C::ScalarExt = transcript.challenge_scalar(b"verifier's challenge");

        // compute response
        let w = rs.witness().clone();
        if w.is_none() {
            return Err(PopError::MissingWitness(RelPedersen::<C>::label()));
        };
        let w = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelPedersen::<C>::label()))?;

        let s =
            w.m.iter()
                .zip(w_r.m.iter())
                .enumerate()
                .map(|(i, (&w, &w_r))| {
                    let s = w_r + c * w;
                    // append the response to allow composition
                    transcript.append_u64(b"response", i as u64);
                    transcript.append_scalar(b"scalar", &s);
                    s
                })
                .collect::<Vec<_>>();
        end_timer!(t);

        let proof = PedersenRoKProof {
            challenge: c,
            response: s,
        };
        Ok((RelTrivial::default(), proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t =
            start_timer!(|| format!("Pedersen Opening RoK ({}) verifier", rs.params().ck.len()));

        if self.ck != rs.params().ck {
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }
        self.initialize(rs, transcript);

        // recompute x_R from the proof
        let mut scalars = proof.response.clone();
        scalars.push(-proof.challenge);
        let mut bases = rs.params().ck.clone();
        bases.push(rs.statement().C);
        let x_r = msm_function(&scalars, &bases).to_affine();

        // append random statement
        transcript.append_point(b"first message", &x_r);

        // get challenge
        let c: C::ScalarExt = transcript.challenge_scalar(b"verifier's challenge");

        if c != proof.challenge {
            end_timer!(t);
            return Err(PopError::RoKError(Self::label() + "computed c != c"));
        }

        // append_responses to allow composing
        proof.response.iter().enumerate().for_each(|(i, s)| {
            transcript.append_u64(b"response", i as u64);
            transcript.append_scalar(b"scalar", s);
        });

        end_timer!(t);
        Ok(RelTrivial::default())
    }
}

#[cfg(test)]
mod tests {

    use ff::Field;
    use halo2curves::t256::T256Affine;
    use merlin::Transcript;
    use r1csipa::msm_function;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::rpedersen::{
            RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness,
        },
        roks::pedersen_rok::PedersenRoK,
        utils::Fr,
    };

    #[test]
    fn test_pedersen_rok() {
        let len = 16;
        // parameters
        let ck: Vec<T256Affine> = (0..len).map(|_| T256Affine::random(OsRng)).collect();
        let pp = RelPedersenParams { ck: ck.clone() };

        // random opening
        let m: Vec<Fr> = (0..len).map(|_| <Fr as Field>::random(OsRng)).collect();
        let w = RelPedersenWitness::<T256Affine> { m: m.clone() };

        // commitment
        let x = RelPedersenStatement {
            C: msm_function(&m, &ck).into(),
        };

        let r_pedersen_prover = RelPedersen::new(pp.clone(), x.clone(), Some(w.clone()));
        let r_pedersen_verifier = RelPedersen::new(pp.clone(), x.clone(), None);

        let rok = PedersenRoK {
            ck: r_pedersen_verifier.params().ck.clone(),
        };

        let mut transcript_prover = Transcript::new(b"pedersen_rok test");
        let (_r_trivial, proof) =
            rok.reduce(&mut transcript_prover, &r_pedersen_prover, &mut OsRng).unwrap();

        let mut transcript_verifier = Transcript::new(b"pedersen_rok test");
        let result = rok.reduce_statement(&mut transcript_verifier, &r_pedersen_verifier, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
