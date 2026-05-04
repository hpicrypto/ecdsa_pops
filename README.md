# ECDSA PoPs 

A Rust workspace containing multiple crates for producing proofs-of-possession (PoPs) based on ECDSA over P256 curve.


## Crates

This workspace currently contains the following crates:

- **rok** – An implementation of *Reductions of Knowledge* as defined in [\[1\]](#rok).
- **r1csipa** – An implementation of an R1CS to IPA (Inner Product Argument) transformation with zero-knowledge support that supports committed inputs based on [this crate](https://github.com/zaverucha/signature-proof/tree/main/r1csipa).
- **ecdsa-pops** – Implementations of PoPs.
- **pop-circuit-ffa** – An implementations of an arithmetic circuit based on the foreighn-field-arithmetic techniques of [\[2\]](#ffa) used for ECDSA proof-of-possession.

## Disclaimer

This project is provided "as is" and is intended for educational and experimental purposes only. The library has not been audited. It is not production-ready and may contain bugs or incomplete features. Use at your own risk.

The authors and contributors are not responsible for any damage, loss of data, or other issues that may arise from using this software.

## License

MIT

## References

\[1\]. <a id="rok"></a>A. Kothapalli, B. Parno, *Algebraic Reductions of Knowledge*, Crypto 2023.  [eprint](https://eprint.iacr.org/2022/009)

\[2\]. <a id="ffa"></a>M. Ambrona, D. Firsov, I. Querejeta-Azurmendi, *Efficient Foreign-Field Arithmetic in PLONK*, Cryptology ePrint Archive.  [eprint](https://eprint.iacr.org/2025/695)
