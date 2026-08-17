//! This module defines Reductions of Knowledge ([RoK]s) and generically
//! implements parallel and sequential composition
use std::{error::Error, marker::PhantomData};

use ark_std::{
    end_timer,
    rand::{CryptoRng, RngCore},
    start_timer,
};
use merlin::Transcript;

use crate::relation::{Relation, RelationProduct};

/// A trait represnting a reduction of knowledge
pub trait RoK {
    /// The relation to be reduced
    type RelationSource: Relation + Clone;
    /// The reduced relation
    type RelationTarget: Relation + Clone;
    /// reduction proof
    type Proof: Clone;
    /// the [Error] type of the RoK
    type Error: Error
        + From<<Self::RelationSource as Relation>::Error>
        + From<<Self::RelationTarget as Relation>::Error>;

    /// Description of the RoK
    fn label() -> String;

    /// intialize the prover/verifier. Add domain separation and hash statement
    fn initialize(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        transcript.append_message(b"RoK:", Self::label().into_bytes().as_slice());
        self.hash_statement(rs, transcript);
    }

    /// Adds the statement to the transcript.
    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript);

    /// Prove reduction of knowledge RelationSource -> RelationTarget
    ///
    /// Returns the reduced statement/witness and a proof
    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng;

    /// Given a statement and proof, it reduces a statement RelationSource ->
    /// RelationTarget
    ///
    /// Returns the reduced statement
    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error>;
}

/// Struct representing parallel composition: RoK1 x RoK2
pub struct ParallelRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    /// the first [RoK]
    rok1: RoK1,
    /// the second [RoK]
    rok2: RoK2,
    /// phantom data
    _phantom: PhantomData<E>,
}

// TODO: Check why the compiler complains with derive(clone)
impl<RoK1, RoK2, E> Clone for ParallelRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    fn clone(&self) -> Self {
        Self {
            rok1: self.rok1.clone(),
            rok2: self.rok2.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<RoK1, RoK2, E> ParallelRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    /// Returns the first reduction of knowledge
    pub fn rok1(&self) -> &RoK1 {
        &self.rok1
    }

    /// Returns the second reduction of knowledge
    pub fn rok2(&self) -> &RoK2 {
        &self.rok2
    }

    /// creates a new parallel composition from two roks
    pub fn new(rok1: RoK1, rok2: RoK2) -> Self {
        Self {
            rok1,
            rok2,
            _phantom: PhantomData,
        }
    }
}

impl<RoK1, RoK2, E> RoK for ParallelRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK + Clone,
    E: Error
        + From<RoK1::Error>
        + From<RoK2::Error>
        + From<<RoK1::RelationSource as Relation>::Error>
        + From<<RoK1::RelationTarget as Relation>::Error>
        + From<<RoK2::RelationSource as Relation>::Error>
        + From<<RoK2::RelationTarget as Relation>::Error>,
{
    type Error = E;
    type RelationSource = RelationProduct<RoK1::RelationSource, RoK2::RelationSource, E>;
    type RelationTarget = RelationProduct<RoK1::RelationTarget, RoK2::RelationTarget, E>;
    type Proof = (RoK1::Proof, RoK2::Proof);

    fn label() -> String {
        [
            "RoK Parallel Composition: (",
            &RoK1::label(),
            " x ",
            &RoK2::label(),
            ")",
        ]
        .concat()
    }

    fn hash_statement(&self, statement: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the two statements
        self.rok1().hash_statement(statement.r1(), transcript);
        self.rok2().hash_statement(statement.r2(), transcript);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| format!("RoK ({}) Prover", Self::label()));
        self.initialize(rs, transcript);

        // reduce the first statement
        let (rt1, proof_1) = self.rok1().reduce(transcript, rs.r1(), rng)?;

        // reduce the second statement
        let (rt2, proof_2) = self.rok2().reduce(transcript, rs.r2(), rng)?;

        let rt: Self::RelationTarget = RelationProduct::from_parts(rt1, rt2);
        let proof = (proof_1, proof_2);
        end_timer!(t);

        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| format!("RoK ({}) Verifier", Self::label()));
        self.initialize(rs, transcript);

        // reduce the first statement
        let rt1 = self.rok1().reduce_statement(transcript, rs.r1(), &proof.0)?;

        // reduce the second statement
        let rt2 = self.rok2().reduce_statement(transcript, rs.r2(), &proof.1)?;

        let rt: Self::RelationTarget = RelationProduct::from_parts(rt1, rt2);
        end_timer!(t);

        Ok(rt)
    }
}

/// Struct representing sequential composition RoK2 o RoK1
pub struct SequentialRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK<RelationSource = RoK1::RelationTarget> + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    /// the first [RoK]
    rok1: RoK1,
    /// the second [RoK]
    rok2: RoK2,
    /// phantom data
    _phantom: PhantomData<E>,
}

// TODO: Check why the compiler complains with derive(clone)
impl<RoK1, RoK2, E> Clone for SequentialRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK<RelationSource = RoK1::RelationTarget> + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    fn clone(&self) -> Self {
        Self {
            rok1: self.rok1.clone(),
            rok2: self.rok2.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<RoK1, RoK2, E> SequentialRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK<RelationSource = RoK1::RelationTarget> + Clone,
    E: Error + From<RoK1::Error> + From<RoK2::Error>,
{
    /// Returns the first reduction of knowledge
    pub fn rok1(&self) -> &RoK1 {
        &self.rok1
    }

    /// Returns the second reduction of knowledge
    pub fn rok2(&self) -> &RoK2 {
        &self.rok2
    }

    /// creates a new sequantial composition from two roks
    pub fn new(rok1: RoK1, rok2: RoK2) -> Self {
        Self {
            rok1,
            rok2,
            _phantom: PhantomData,
        }
    }
}

impl<RoK1, RoK2, E> RoK for SequentialRoK<RoK1, RoK2, E>
where
    RoK1: RoK + Clone,
    RoK2: RoK<RelationSource = RoK1::RelationTarget> + Clone,
    E: Error
        + From<RoK1::Error>
        + From<RoK2::Error>
        + From<<RoK1::RelationSource as Relation>::Error>
        + From<<RoK1::RelationTarget as Relation>::Error>
        + From<<RoK2::RelationTarget as Relation>::Error>,
{
    type Error = E;
    type RelationSource = RoK1::RelationSource;
    type RelationTarget = RoK2::RelationTarget;
    type Proof = (RoK1::Proof, RoK2::Proof);

    fn label() -> String {
        [
            "RoK Sequential Composition: (",
            &RoK2::label(),
            " o ",
            &RoK1::label(),
            ")",
        ]
        .concat()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        self.rok1().hash_statement(rs, transcript);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| format!("RoK ({}) Prover", Self::label()));

        self.initialize(rs, transcript);

        // prove the first statement
        let (rt1, proof1) = self.rok1().reduce(transcript, rs, rng)?;

        // hash the intermediate statement
        self.rok2().hash_statement(&rt1, transcript);

        // prove the second statement
        let (rt2, proof2) = self.rok2().reduce(transcript, &rt1, rng)?;

        // proof consists of
        // 1. the intermediate statement and the proof of the first reduction
        // 2. the proof of the second reduction
        let proof = (proof1, proof2);

        end_timer!(t);

        Ok((rt2, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| format!("RoK ({}) Verifier", Self::label()));

        self.initialize(rs, transcript);

        // parse proof
        let (proof1, proof2) = proof;

        // verify the first statement
        let rt1 = self.rok1().reduce_statement(transcript, rs, proof1)?;

        // hash the intermediate statement
        self.rok2().hash_statement(&rt1, transcript);

        // verify the second statement
        let rt2 = self.rok2().reduce_statement(transcript, &rt1, proof2)?;

        end_timer!(t);

        Ok(rt2)
    }
}

#[macro_export]
/// Macro to construct complex composed [RoK]s given the individual [RoK]s.
///
/// Usage:
/// let my_composed_rok = rok_compose!(
///     MyErrorType;
///     (((rok1) o (rok2)) o ((rok1) x (rok2)))
/// );
///
/// # Operators
///
/// - `o` — **Sequential composition**
/// - `x` — **Parallel composition**
///
/// Parentheses can be used to control grouping.
///
/// The macro expands to nested [`SequentialRoK`] and [`ParallelRoK`]
/// instantiations.
///
/// # Syntax
///
/// ```text
/// rok_compose_type!(ErrorType; COMPOSITION)
/// ```
///
/// where `COMPOSITION` is an expression built from `RoK` types using
/// `o`, `x`, and parentheses.
///
/// # Example
///
/// ```ignore
/// type MyComposedRoK = rok_compose!(
///     MyErrorType;
///     ((rok1 o rok2) o (rok1 x rok2))
/// );
/// ```
macro_rules! rok_compose {
    ($E:ty ; $($expr:tt)+) => {
        $crate::rok_compose!(@parse $E ; $($expr)+)
    };

    (@parse $E:ty ; ( $($inner:tt)+ ) ) => {
        $crate::rok_compose!(@parse $E ; $($inner)+)
    };

    // Sequential: A o B  ==> SequentialRoK::<_, _, E>::new(A, B)
    (@parse $E:ty ; $lhs:tt o $rhs:tt) => {{
        $crate::SequentialRoK::<_, _, $E>::new(
            $crate::rok_compose!(@parse $E ; $rhs),
            $crate::rok_compose!(@parse $E ; $lhs),
        )
    }};

    // Parallel: A x B ==> ParallelRoK::<_, _, E>::new(A, B)
    (@parse $E:ty ; $lhs:tt x $rhs:tt) => {{
        $crate::ParallelRoK::<_, _, $E>::new(
            $crate::rok_compose!(@parse $E ; $lhs),
            $crate::rok_compose!(@parse $E ; $rhs),
        )
    }};

    (@parse $E:ty ; $leaf:expr) => { $leaf };
}

#[macro_export]
/// macro to construct complex composed [RoK]s types given the individual [RoK]s
/// types.
///
/// Usage:
/// type MyComposedRoK = rok_compose_type!(
///     MyErrorType;
///     (((RoK1) o (RoK2)) o ((RoK1) x (RoK2)))
/// );
/// Constructs a composed [`RoK`] type from simpler [`RoK`]s types
///
/// This macro lets you express complex compositions of reductions of
/// knowledge at the type level using a concise syntax.
///
/// # Operators
///
/// - `o` — **Sequential composition**
/// - `x` — **Parallel composition**
///
/// Parentheses can be used to control grouping.
///
/// The macro expands to nested [`SequentialRoK`] and [`ParallelRoK`] types.
///
/// # Syntax
///
/// ```text
/// rok_compose_type!(ErrorType; COMPOSITION)
/// ```
///
/// where `COMPOSITION` is an expression built from `RoK` types using
/// `o`, `x`, and parentheses.
///
/// # Example
///
/// ```ignore
/// type MyComposedRoK = rok_compose_type!(
///     MyErrorType;
///     ((RoK1 o RoK2) o (RoK1 x RoK2))
/// );
/// ```
macro_rules! rok_compose_type {
    ($E:ty ; $($t:tt)+) => {
        $crate::rok_compose_type!(@parse $E ; $($t)+)
    };

    (@parse $E:ty ; ( $($inner:tt)+ ) ) => {
        $crate::rok_compose_type!(@parse $E ; $($inner)+)
    };

    // Sequential: A o B ==> SequentialRoK<B, A, E>
    (@parse $E:ty ; $lhs:tt o $rhs:tt) => {
        $crate::SequentialRoK<
            $crate::rok_compose_type!(@parse $E ; $rhs),
            $crate::rok_compose_type!(@parse $E ; $lhs),
            $E
        >
    };

    // Parallel: A x B ==> ParallelRoK<A, B, E>
    (@parse $E:ty ; $lhs:tt x $rhs:tt) => {
        $crate::ParallelRoK<
            $crate::rok_compose_type!(@parse $E ; $lhs),
            $crate::rok_compose_type!(@parse $E ; $rhs),
            $E
        >
    };

    (@parse $E:ty ; $leaf:ty) => { $leaf };
}
