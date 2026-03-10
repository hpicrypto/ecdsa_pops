//! Traits for ternary relations containing parameters, statement, witness
use std::{error::Error, fmt::Debug, marker::PhantomData};

use serde::Serialize;

/// A trait represnting a relation
pub trait Relation {
    /// The parameters of the relation
    type Params: Debug + Clone;
    /// The statement of the relation
    type Statement: Debug + Clone;
    /// The witness of the relation
    type Witness: Debug + Clone;
    /// The error type
    type Error: Error;

    /// Creates a new relation with an optional witness
    fn new(pp: Self::Params, x: Self::Statement, w: Option<Self::Witness>) -> Self;

    /// Description of the relation
    fn label() -> String;

    /// Parameters of the relation
    fn params(&self) -> &Self::Params;

    /// Statement of the relation
    fn statement(&self) -> &Self::Statement;

    /// Witness of the relation
    fn witness(&self) -> &Option<Self::Witness>;

    /// checks if (pp, x, w) in R
    fn in_relation(&self) -> Result<(), Self::Error>;
}

/// Struct representing a relation product.
#[derive(Debug)]
pub struct RelationProduct<R1, R2, E>
where
    R1: Relation + Clone,
    R2: Relation + Clone,

    E: Error,
{
    /// the first [Relation]
    r1: R1,
    /// the second [Relation]
    r2: R2,
    /// the parameters
    params: (R1::Params, R2::Params),
    /// the statements
    statement: (R1::Statement, R2::Statement),
    /// the witnesses
    witness: Option<(R1::Witness, R2::Witness)>,
    /// Phantom
    _phantom: PhantomData<E>,
}

impl<R1, R2, E> RelationProduct<R1, R2, E>
where
    R1: Relation + Clone,
    R2: Relation + Clone,
    E: Error + From<<R1 as Relation>::Error> + From<<R2 as Relation>::Error>,
{
    /// Given two relations, creates the product relation
    pub fn from_parts(r1: R1, r2: R2) -> Self {
        Self {
            r1: r1.clone(),
            r2: r2.clone(),
            params: (r1.params().clone(), r2.params().clone()),
            statement: (r1.statement().clone(), r2.statement().clone()),
            witness: (r1.witness().clone().zip(r2.witness().clone())),
            _phantom: PhantomData,
        }
    }

    /// Returns the first relation
    pub fn r1(&self) -> &R1 {
        &self.r1
    }

    /// Returns the second relation
    pub fn r2(&self) -> &R2 {
        &self.r2
    }
}

impl<R1, R2, E> Clone for RelationProduct<R1, R2, E>
where
    R1: Relation + Clone,
    R2: Relation + Clone,
    E: Error + From<<R1 as Relation>::Error> + From<<R2 as Relation>::Error>,
{
    fn clone(&self) -> Self {
        Self::from_parts(self.r1.clone(), self.r2.clone())
    }
}

impl<R1, R2, E> Relation for RelationProduct<R1, R2, E>
where
    R1: Relation + Clone,
    R2: Relation + Clone,
    E: Error + From<<R1 as Relation>::Error> + From<<R2 as Relation>::Error>,
{
    type Params = (R1::Params, R2::Params);
    type Statement = (R1::Statement, R2::Statement);
    type Witness = (R1::Witness, R2::Witness);
    type Error = E;

    fn label() -> String {
        format!("{} x {}", R1::label(), R2::label())
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }

    fn statement(&self) -> &Self::Statement {
        &self.statement
    }

    fn witness(&self) -> &Option<Self::Witness> {
        &self.witness
    }

    fn new(pp: Self::Params, x: Self::Statement, w: Option<Self::Witness>) -> Self {
        let r1 = R1::new(pp.0, x.0, w.clone().map(|w| w.0));
        let r2 = R2::new(pp.1, x.1, w.map(|w| w.1));
        Self::from_parts(r1, r2)
    }

    fn in_relation(&self) -> Result<(), Self::Error> {
        // check that both relations are valid
        self.r1.in_relation()?;
        self.r2.in_relation()?;
        Ok(())
    }
}

/// The always true relation
#[derive(Serialize, Debug)]
pub struct RelTrivial<E: Error>(pub PhantomData<E>);

impl<E: Error> Clone for RelTrivial<E> {
    fn clone(&self) -> Self {
        RelTrivial(PhantomData)
    }
}

impl<E: Error> Default for RelTrivial<E> {
    fn default() -> Self {
        RelTrivial(PhantomData)
    }
}

impl<E: Error> Relation for RelTrivial<E> {
    type Params = ();
    type Statement = ();
    type Witness = ();
    type Error = E;

    fn label() -> String {
        "True".into()
    }

    fn params(&self) -> &Self::Params {
        &()
    }

    fn statement(&self) -> &Self::Statement {
        &()
    }

    fn witness(&self) -> &Option<Self::Witness> {
        &None
    }

    fn new(_pp: Self::Params, _x: Self::Statement, _w: Option<Self::Witness>) -> Self {
        RelTrivial(PhantomData)
    }

    fn in_relation(&self) -> Result<(), E> {
        Ok(())
    }
}
