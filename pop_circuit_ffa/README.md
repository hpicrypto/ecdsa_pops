# An FFA-based Circuit Implementation for ECDSA proof-of-possession

A Rust library implementing an plonk-based circuit for the relation `T=R+cQ` where
 - `T` is a public P256 point
 - `Q,R` are committed inputs corresponding to P256 points
 - `c` is a public P256 scalar
 
The circuit is based on the techniques of [\[1\]](#ffa) and the proving system used is the [plonk-based variant](https://github.com/midnightntwrk/midnight-zk) from [midnight](midnight).
 
Two solution are implemented:
1. *double-and-add based:* implements the in-circuit scalar multiplication using the double-and-add algorithm. The challenge `c` is "hardcoded" in the circuit meaning each statement corresponds to a different circuit
2. *window-method based:* implements the in-circuit scalar multiplication using the windowed method. The challenge `c` is part of the public inputs so all statements are proven with the same circuit. 

The circuit can be used to achieve ECDSA proof-of-possession as explained in (TODO add link to the paper)

## Overview

This crate implements the R1CS to IPA transform described in ePrint 2025/327:
"Bulletproofs for R1CS: Bridging the Completeness-Soundness Gap and a ZK Extension" by Gil Segev.

The underlying IPA protocol supports zero-knowledge as described in ePrint 2020/735:
"Bulletproofs+: Shorter Proofs for Privacy-Enhanced Distributed Ledger" by Heewon Chung, Kyoohyung Han, Chanyang Ju, Myungsun Kim, and Jae Hong Seo.

The library is a small adaptation of the [r1csipa](https://github.com/zaverucha/signature-proof/tree/main/r1csipa) that allows proofs where (part of) the public input is committed using hiding Pedersen commitments. 

## Disclaimer

This project is provided "as is" and is intended for educational and experimental purposes only. The library has not been audited. It is not production-ready and may contain bugs or incomplete features. Use at your own risk.

The authors and contributors are not responsible for any damage, loss of data, or other issues that may arise from using this software.

## License

MIT

## Acknowledgements

Thanks to [@miguel-ambrona](https://github.com/miguel-ambrona) and [iquerejeta](https://github.com/iquerejeta) for providing the circuit implementation and the emulation parameters for P256 curve.

## References 

\[1\]. <a id="ffa"></a>M. Ambrona, D. Firsov, I. Querejeta-Azurmendi, *Efficient Foreign-Field Arithmetic in PLONK*, Cryptology ePrint Archive.  [eprint](https://eprint.iacr.org/2025/695)
