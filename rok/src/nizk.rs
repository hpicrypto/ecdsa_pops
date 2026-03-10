//! Trait representing a non-interactive zero knowledge proof [Nizk] and blanket
//! implementation from any [RoK] with [RoK::RelationTarget] being [RelTrivial]

// TODO: Make a trait for the trivial relation and a nizk implementation from
// any composition of roks that leads to a relation that implements the trivial
// relation

use std::error::Error;

use ark_std::rand::{CryptoRng, RngCore};
use merlin::Transcript;

use crate::{
    relation::{RelTrivial, Relation},
    rok::RoK,
};

/// A trait represnting a nizk
pub trait Nizk {
    /// The [Relation] to be proven
    type Relation: Relation + Clone;
    /// NIZK proof
    type Proof;
    /// The [Error] type.
    type Error: Error + From<<Self::Relation as Relation>::Error>;

    /// Description of the [Nizk]
    // TODO: Maybe use a &'static str (?)
    fn label() -> String;

    /// intialize the prover/verifier. Add domain separation and hash statement
    fn initialize(&self, r: &Self::Relation, transcript: &mut Transcript) {
        transcript.append_message(b"NIZK:", Self::label().into_bytes().as_slice());
        self.hash_statement(r, transcript);
    }

    /// Adds the statement to the transcript.
    fn hash_statement(&self, r: &Self::Relation, transcript: &mut Transcript);

    /// Prove [Relation] R
    fn prove<R>(
        &self,
        transcript: &mut Transcript,
        r: &Self::Relation,
        rng: &mut R,
    ) -> Result<Self::Proof, Self::Error>
    where
        R: RngCore + CryptoRng;

    /// Verify proof for [Relation] R
    fn verify(
        &self,
        transcript: &mut Transcript,
        rs: &Self::Relation,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}

impl<R, E> Nizk for R
where
    R: RoK<RelationTarget = RelTrivial<E>, Error = E>,
    E: Error + From<<R::RelationSource as Relation>::Error>,
{
    type Relation = R::RelationSource;
    type Proof = R::Proof;
    type Error = E;

    fn label() -> String {
        R::label()
    }

    fn hash_statement(&self, r: &Self::Relation, transcript: &mut Transcript) {
        <R as RoK>::hash_statement(self, r, transcript);
    }
    fn prove<Rng>(
        &self,
        transcript: &mut Transcript,
        r: &Self::Relation,
        rng: &mut Rng,
    ) -> Result<Self::Proof, Self::Error>
    where
        Rng: RngCore + CryptoRng,
    {
        // simply do the reduction to the trivial relation
        let (_rel_trivial, proof) = self.reduce(transcript, r, rng)?;
        Ok(proof)
    }
    fn verify(
        &self,
        transcript: &mut Transcript,
        r: &Self::Relation,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        // simply verify the reduction to the trivial relation
        self.reduce_statement(transcript, r, proof).map(|_| ())
    }
}
