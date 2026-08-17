//! minimal prehashed version of ECDSA over P256 *for testing purposes*.

#![allow(non_snake_case)]

use ff::Field;
use halo2curves::{group::prime::PrimeCurveAffine, secp256r1::Secp256r1Affine};
use rand_core::{CryptoRng, RngCore};

use crate::{errors::PopError, utils::Fq};

/// struct containing the parameters for ECDSA
#[derive(Debug, Clone, Copy)]
#[allow(clippy::upper_case_acronyms)]
pub struct ECDSA {
    /// parameters consist only of the group generator
    pub pp: Secp256r1Affine,
}

/// [ECDSA] signature
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ECDSASignature {
    /// Random X coordinate
    pub Rx: Fq,
    /// Response
    pub response: Fq,
}

/// Transformed [ECDSASignature]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ECDSASignatureConverted {
    /// The first part of the signature
    pub K: Secp256r1Affine,
    /// The second part of the signature
    pub z: Fq,
}

impl ECDSA {
    /// Create parameters
    pub fn setup() -> Self {
        ECDSA {
            pp: Secp256r1Affine::generator(),
        }
    }

    /// Sample a key pair
    pub fn keygen<R>(&self, rng: &mut R) -> (Fq, Secp256r1Affine)
    where
        R: RngCore + CryptoRng,
    {
        let sk = Fq::random(rng);
        let pk: Secp256r1Affine = (self.pp * sk).into();
        (sk, pk)
    }

    /// Create a new [ECDSASignature] given that the message has already been
    /// hashed into a scalar [Fq]
    pub fn sign_prehashed<R>(
        &self,
        secret_key: &Fq,
        hm: &Fq,
        rng: &mut R,
    ) -> Result<ECDSASignature, PopError>
    where
        R: RngCore + CryptoRng,
    {
        let k = <Fq as Field>::random(&mut *rng);

        // R = k * P
        let R: Secp256r1Affine = (self.pp * k).into();

        // Rx to field
        let Rx = ECDSA::p256_to_scalar(&R);

        // response = 1/k * (message + secret_key * Rx)
        let response = k.invert().unwrap_or(Fq::ZERO) * (hm + secret_key * Rx);

        let fails = R == Secp256r1Affine::identity()
            || Rx == Fq::ZERO
            || response == Fq::ZERO
            || k == Fq::ZERO;

        // retry on failure
        if fails {
            self.sign_prehashed(hm, secret_key, rng)
        } else {
            Ok(ECDSASignature { Rx, response })
        }
    }

    /// Verify an [ECDSASignature] given that the message has already been
    /// hashed into a scalar [Fq]
    pub fn verify_prehashed(
        &self,
        public_key: &Secp256r1Affine,
        hm: &Fq,
        signature: &ECDSASignature,
    ) -> Result<(), PopError> {
        let P = self.pp;
        let response_inv = signature.response.invert().unwrap_or(Fq::ZERO);
        let R: Secp256r1Affine =
            (P * (response_inv * hm) + public_key * (response_inv * signature.Rx)).into();

        let Rx = ECDSA::p256_to_scalar(&R);
        // take x coordinate of R and compare with the given
        if *public_key != Secp256r1Affine::identity()
            && response_inv != Fq::zero()
            && signature.Rx == Rx
        {
            Ok(())
        } else {
            Err(PopError::ECDSASigError)
        }
    }

    /// converts the [ECDSASignature] to the alternative form
    /// [ECDSASignatureConverted]
    pub fn convert(
        &self,
        public_key: &Secp256r1Affine,
        hm: &Fq,
        signature: &ECDSASignature,
    ) -> ECDSASignatureConverted {
        let response_inv = signature.response.invert().unwrap();
        let u1 = hm * response_inv;
        let u2 = signature.Rx * response_inv;

        let K = (self.pp * u1 + public_key * u2).into();
        ECDSASignatureConverted {
            K,
            z: u2.invert().unwrap(),
        }
    }

    /// Verify an [ECDSASignatureConverted] given that the message has already
    /// been hashed into an [Fq] scalar
    pub fn verify_prehashed_converted(
        &self,
        public_key: &Secp256r1Affine,
        hm: &Fq,
        signature: &ECDSASignatureConverted,
    ) -> Result<(), PopError> {
        let Rx = ECDSA::p256_to_scalar(&signature.K);

        if *public_key != Secp256r1Affine::identity()
            && signature.K != Secp256r1Affine::identity()
            && signature.K * signature.z + self.pp * (-hm * Rx.invert().unwrap())
                == public_key.into()
        {
            Ok(())
        } else {
            Err(PopError::ECDSASigError)
        }
    }

    /// helper function to embed [Secp256r1Affine] to [Fq]
    pub(crate) fn p256_to_scalar(R: &Secp256r1Affine) -> Fq {
        // Rx to field
        let Rx_bytes = bincode::serialize(&R.x).unwrap();
        Fq::from_bytes(&Rx_bytes[..].try_into().unwrap()).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use rand_core::OsRng;

    use super::*;

    #[test]
    fn ecdsa_sig_verifies() {
        let hm = Fq::random(OsRng);

        let ecdsa = ECDSA::setup();
        let mut rng = OsRng;
        let (sk, pk) = ecdsa.keygen(&mut rng);
        let sig = ecdsa.sign_prehashed(&sk, &hm, &mut rng).unwrap();
        assert!(ecdsa.verify_prehashed(&pk, &hm, &sig).is_ok());

        let converted_sig = ecdsa.convert(&pk, &hm, &sig);

        assert!(ecdsa.verify_prehashed_converted(&pk, &hm, &converted_sig).is_ok());
    }
}
