# ECDSA PoPs

A Rust workspace containing multiple crates for producing proofs-of-possession (PoPs) based on ECDSA over P256 curve. The implementations follow [\[1\]](#popspaper).


## Crates

This workspace currently contains the following crates:

- **rok** – An implementation of *Reductions of Knowledge* as defined in [\[2\]](#rok).
- **r1csipa** – An implementation of an R1CS to IPA (Inner Product Argument) transformation with zero-knowledge support that supports committed inputs based on [this crate](https://github.com/zaverucha/signature-proof/tree/main/r1csipa).
- **ecdsa-pops** – Implementations of PoPs following [\[1\]](#popspaper).
- **pop-circuit-ffa** – An implementations of an arithmetic circuit based on the foreighn-field-arithmetic techniques of [\[3\]](#ffa) used for ECDSA proof-of-possession.
- **CDLS** – An implementations of the CDLS protocol from [\[4\]](#cdls) with our optimizations.

## Benchmarks

To run the benchmarks for the proofs-of-possession you must first download a KZG SRS and place it at `./pop-circuits/ffa/examples/assets`. This is needed for the construction based on FFA. This can be done by running

```
mkdir ./pop_circuit_ffa/examples/assets/
curl -L -o ./pop_circuit_ffa/examples/assets/bls_filecoin_2p19 https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19
```

Then to run the benchmarks:
```
cargo bench -p ecdsa_pops
```

For benchmark comparing [\[4\]](#cdls) with our improvements:
```
cargo bench -p t256 
```

## Disclaimer

This project is provided "as is" and is intended for educational and experimental purposes only. The library has not been audited. It is not production-ready and may contain bugs or incomplete features. Use at your own risk.

The authors and contributors are not responsible for any damage, loss of data, or other issues that may arise from using this software.

## License

MIT

## References

\[1\]. <a id="popspaper"></a>S. Celi, A. Lehmann, S. Levin, A. Zacharakis, *Device Binding for Anonymous Credentials on Legacy Phones*.  [Eprint](https://eprint.iacr.org/2026/965)

\[2\]. <a id="rok"></a>A. Kothapalli, B. Parno, *Algebraic Reductions of Knowledge*, Crypto 2023.  [eprint](https://eprint.iacr.org/2022/009)

\[3\]. <a id="ffa"></a>M. Ambrona, D. Firsov, I. Querejeta-Azurmendi, *Efficient Foreign-Field Arithmetic in PLONK*, Cryptology ePrint Archive.  [eprint](https://eprint.iacr.org/2025/695)

\[4\]. <a id="cdls"></a>S. Celi, S. Levin, J. Rowell, *CDLS: Proving Knowledge of Committed Discrete Logarithms with Soundness*, Cryptology ePrint Archive.  [eprint](https://eprint.iacr.org/2023/1595)
