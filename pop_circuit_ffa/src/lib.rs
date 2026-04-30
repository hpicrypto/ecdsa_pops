//! Proves knowledge of points Q, R on P-256 such that
//!
//!   T = R + c·Q
//!
//! where T and c are the only public input.
//!
//! Two scalar-multiplication strategies are compiled and compared:
//!
//! * **Windowed (WS=4)** — `msm_by_fixed_le_bits`: packs bits into 4-bit
//!   windows, always processes all windows.  Cost: n doublings + ~40 adds
//!   for n = 100 bits.
//!
//! * **Double-and-add** — `mul_by_u128`: processes one bit at a time,
//!   adding `base` only for set bits.  Cost: n doublings + popcount(c) adds.
//!   Competitive when popcount(c) < ~40.
//!
//! Instance:  T: P256
//! Witness:   (Q: P256,  R: P256, blinders)

use midnight_curves::p256::{affine_x, P256Affine};

use ff::PrimeField;
use midnight_circuits::{
    field::foreign::params::MultiEmulationParams,
    instructions::{
        public_input::CommittedInstanceInstructions, AssertionInstructions, AssignmentInstructions,
        DecompositionInstructions, EccInstructions, PublicInputInstructions,
    },
    types::{AssignedForeignPoint, AssignedNative, Instantiable},
    CircuitField,
};

use midnight_curves::p256::P256;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};

type F = midnight_curves::Fq;

/// number of needed blinding factors
pub const B_FACTORS: usize = 8;

// helper function that decomposes a p256 point to two Field elements by expressing its x-coordinate
// to two limbs of 128 bits. Returns the limbs represented in the field.
//
// TODO: make this generic
fn p256_to_limbs<F: CircuitField>(q: &P256Affine) -> (F, F) {
    // convert the point to bytes
    let qx_bytes = &affine_x(q).to_bytes_be().to_vec();

    // high limb
    let mut qx_high_bytes = [0u8; 16].to_vec();
    qx_high_bytes.extend_from_slice(&qx_bytes[0..16]);
    let qx_high = F::from_bytes_be(&qx_high_bytes).unwrap();

    // low limb
    let mut qx_low_bytes = [0u8; 16].to_vec();
    qx_low_bytes.extend_from_slice(&qx_bytes[16..]);
    let qx_low = F::from_bytes_be(&qx_low_bytes).unwrap();

    (qx_low, qx_high)
}

// helper function that constructs the committed input for both circuits
// the committed inputs are:
// [q.x_low, qx.high, r.x_low, rx.high, b0, ..., b5]
fn format_committed_instances_helper(q: &P256, r: &P256, blinders: &[F; B_FACTORS]) -> Vec<F> {
    let q_limbs = p256_to_limbs::<F>(&q.to_affine());
    let r_limbs = p256_to_limbs::<F>(&r.to_affine());
    [
        // q low limb
        AssignedNative::as_public_input(&q_limbs.0),
        // q high limb
        AssignedNative::as_public_input(&q_limbs.1),
        // r low limb
        AssignedNative::as_public_input(&r_limbs.0),
        // r high limb
        AssignedNative::as_public_input(&r_limbs.1),
    ]
    .into_iter()
    // the blinding factors
    .chain(blinders.iter().map(AssignedNative::as_public_input))
    .flatten()
    .collect()
}

// ── Windowed relation (WS=4, c as public input) ───────────────────────────────

/// Parameterless relation: c is a public input, so a single VK covers all
/// challenge values.  Instance = (T, c) where c is a bounded u128 scalar.
///
/// eight blinding factors are used to guaranteed the KZG poly is hiding
#[derive(Clone)]
pub struct EcdsaPoPP256<const NB_BITS_C: usize>;

impl<const NB_BITS_C: usize> Relation for EcdsaPoPP256<NB_BITS_C> {
    type Error = Error;
    /// Public inputs: the target point T and the challenge scalar c.
    type Instance = (P256, u128);
    type Witness = (P256, P256, [F; B_FACTORS]);

    fn format_instance((t, c): &Self::Instance) -> Result<Vec<F>, Error> {
        let mut pi = AssignedForeignPoint::<F, P256, MultiEmulationParams>::as_public_input(t);
        pi.push(F::from_u128(*c));
        Ok(pi)
    }

    fn format_committed_instances(w: &Self::Witness) -> Vec<F> {
        format_committed_instances_helper(&w.0, &w.1, &w.2)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let curve = std_lib.p256();
        let base = curve.base_field_chip();

        // ── Public inputs ─────────────────────────────────────────────────────
        let t = curve.assign_as_public_input(layouter, instance.map(|(t, _)| t))?;
        let c_native =
            std_lib.assign_as_public_input(layouter, instance.map(|(_, c)| F::from_u128(c)))?;

        // ── Witnesses ─────────────────────────────────────────────────────────
        let (q_val, r_val) = witness.map(|(q, r, _)| (q, r)).unzip();
        let q: AssignedForeignPoint<_, _, _> = curve.assign(layouter, q_val)?;
        let r = curve.assign(layouter, r_val)?;

        // ── Relation: T = R + c·Q ─────────────────────────────────────────────
        // Decompose c into NB_BITS_C little-endian bits (range-checked).
        let c_bits = std_lib.assigned_to_le_bits(layouter, &c_native, Some(NB_BITS_C), false)?;
        let cq = curve.msm_by_le_bits(layouter, &[c_bits], &[q.clone()])?;
        let result = curve.add(layouter, &cq, &r)?;
        curve.assert_equal(layouter, &result, &t)?;

        // Compute the values q.x, q.r by the committed inputs
        //
        // TODO: abstract this common part of both circuits
        let ps = [q_val, r_val]
            .into_iter()
            .map(|p_val| {
                // compute the low and high limbs as F elements
                let (p_val_low, p_val_high) = p_val.map(|p| p256_to_limbs(&p.to_affine())).unzip();

                // assign them as F elements and constrain them as committed inputs
                let p_low: AssignedNative<F> = std_lib.assign(layouter, p_val_low)?;
                std_lib.constrain_as_committed_public_input(layouter, &p_low)?;
                let p_high: AssignedNative<F> = std_lib.assign(layouter, p_val_high)?;
                std_lib.constrain_as_committed_public_input(layouter, &p_high)?;

                // convert the elements to bytes representing p256 elements
                let p_low_bytes = std_lib.assigned_to_be_bytes(layouter, &p_low, Some(16))?;
                let p_high_bytes = std_lib.assigned_to_be_bytes(layouter, &p_high, Some(16))?;

                // compute the foreign point p from the bytes
                let p_bytes: Vec<_> =
                    p_high_bytes.iter().chain(p_low_bytes.iter()).cloned().collect();
                let px = base.assigned_from_be_bytes(layouter, &p_bytes)?;

                Ok::<_, Error>(px)
            })
            .collect::<Result<Vec<_>, _>>()?;

        // compare with the witnessed points
        let qx = curve.x_coordinate(&q);
        base.assert_equal(layouter, &qx, &ps[0])?;
        let rx = curve.x_coordinate(&r);
        base.assert_equal(layouter, &rx, &ps[1])
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            p256: true,
            nb_arith_cols: 5,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(()) // no fixed parameters
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(EcdsaPoPP256)
    }
}

// ── Double-and-add relation ───────────────────────────────────────────────────

#[derive(Clone)]
pub struct EcdsaPoPP256Daa {
    c_bits: u128,
}

impl EcdsaPoPP256Daa {
    pub fn new(c_bits: u128) -> Self {
        Self { c_bits }
    }
}

impl Relation for EcdsaPoPP256Daa {
    type Error = Error;
    type Instance = P256;
    type Witness = (P256, P256, [F; B_FACTORS]);

    fn format_instance(t: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(AssignedForeignPoint::<F, P256, MultiEmulationParams>::as_public_input(t))
    }

    fn format_committed_instances(w: &Self::Witness) -> Vec<F> {
        format_committed_instances_helper(&w.0, &w.1, &w.2)
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let curve = std_lib.p256();
        let base = curve.base_field_chip();

        // assign the public point t
        let t = curve.assign_as_public_input(layouter, instance)?;

        // the assigned secret points q, r
        let (q_val, r_val) = witness.map(|(q, r, _)| (q, r)).unzip();
        let q = curve.assign(layouter, q_val)?;
        let r = curve.assign(layouter, r_val)?;

        // compute c*q + r in circuit
        let cq = curve.mul_by_u128(layouter, self.c_bits, &q)?;
        let result = curve.add(layouter, &cq, &r)?;
        // assert c*q + r = t where t is a public point
        curve.assert_equal(layouter, &result, &t)?;

        // Compute the values q.x, q.r by the committed inputs
        let ps = [q_val, r_val]
            .into_iter()
            .map(|p_val| {
                // compute the low and high limbs as F elements
                let (p_val_low, p_val_high) = p_val.map(|p| p256_to_limbs(&p.to_affine())).unzip();

                // assign them as F elements and constrain them as committed inputs
                let p_low: AssignedNative<F> = std_lib.assign(layouter, p_val_low)?;
                std_lib.constrain_as_committed_public_input(layouter, &p_low)?;
                let p_high: AssignedNative<F> = std_lib.assign(layouter, p_val_high)?;
                std_lib.constrain_as_committed_public_input(layouter, &p_high)?;

                // convert the elements to bytes representing p256 elements
                let p_low_bytes = std_lib.assigned_to_be_bytes(layouter, &p_low, Some(16))?;
                let p_high_bytes = std_lib.assigned_to_be_bytes(layouter, &p_high, Some(16))?;

                // compute the foreign point p as bytes
                let p_bytes: Vec<_> =
                    p_high_bytes.iter().chain(p_low_bytes.iter()).cloned().collect();
                let px = base.assigned_from_be_bytes(layouter, &p_bytes)?;

                Ok::<_, Error>(px)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let qx = curve.x_coordinate(&q);
        base.assert_equal(layouter, &qx, &ps[0])?;
        let rx = curve.x_coordinate(&r);
        base.assert_equal(layouter, &rx, &ps[1])
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            p256: true,
            nb_arith_cols: 7,
            nr_pow2range_cols: 6,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.c_bits.to_le_bytes())
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; 16];
        reader.read_exact(&mut buf)?;
        Ok(EcdsaPoPP256Daa {
            c_bits: u128::from_le_bytes(buf),
        })
    }
}
