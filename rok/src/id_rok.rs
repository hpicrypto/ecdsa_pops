//! A generic implementation of the identity [RoK] where the prover and verifier simply output their
//! corresponding statements.

use std::{error::Error, marker::PhantomData};

use crate::{relation::Relation, rok::RoK};

/// The identity RoK over some generic [Relation] R
pub struct IDRoK<R: Relation, E: Error>(PhantomData<(R, E)>);

impl<R: Relation, E: Error> Default for IDRoK<R, E> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<R: Relation, E: Error> Clone for IDRoK<R, E> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<R, E> RoK for IDRoK<R, E>
where
    R: Relation + Clone,
    E: Error + From<R::Error>,
{
    type RelationSource = R;
    type RelationTarget = R;
    type Error = E;
    type Proof = ();

    fn label() -> String {
        [String::from("ID RoK for  "), R::label()].concat()
    }

    fn initialize(&self, _rs: &Self::RelationSource, _transcript: &mut merlin::Transcript) {}

    fn hash_statement(&self, _rs: &Self::RelationSource, _transcript: &mut merlin::Transcript) {}

    fn reduce<Rng>(
        &self,
        _transcript: &mut merlin::Transcript,
        rs: &Self::RelationSource,
        _rng: &mut Rng,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        Rng: ark_std::rand::RngCore + ark_std::rand::CryptoRng,
    {
        Ok((rs.clone(), ()))
    }

    fn reduce_statement(
        &self,
        _transcript: &mut merlin::Transcript,
        rs: &Self::RelationSource,
        _proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        Ok(rs.clone())
    }
}
