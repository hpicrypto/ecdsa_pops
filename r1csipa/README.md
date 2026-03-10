# r1csipa

A Rust library implementing an R1CS to IPA (Inner Product Argument) transformation with zero-knowledge support that supports committed inputs.

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
