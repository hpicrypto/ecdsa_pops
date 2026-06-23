# An FFA-based Circuit Implementation for ECDSA proof-of-possession

A Rust library implementing an plonk-based circuit for the relation `T=R+cQ` where
 - `T` is a public P256 point
 - `Q,R` are committed inputs corresponding to P256 points
 - `c` is a public P256 scalar
 
The circuit is based on the techniques of [\[1\]](#ffa) and the proving system used is the [plonk-based variant](https://github.com/midnightntwrk/midnight-zk) from [midnight](midnight).
 
Two solution are implemented:
1. *double-and-add based:* implements the in-circuit scalar multiplication using the double-and-add algorithm. The challenge `c` is "hardcoded" in the circuit meaning each statement corresponds to a different circuit
2. *window-method based:* implements the in-circuit scalar multiplication using the windowed method. The challenge `c` is part of the public inputs so all statements are proven with the same circuit. 

The circuit can be used to achieve ECDSA proof-of-possession as explained in [\[2\]](#popspaper)

## Disclaimer

This project is provided "as is" and is intended for educational and experimental purposes only. The library has not been audited. It is not production-ready and may contain bugs or incomplete features. Use at your own risk.

The authors and contributors are not responsible for any damage, loss of data, or other issues that may arise from using this software.

## License

MIT

## Acknowledgements

Thanks to [@miguel-ambrona](https://github.com/miguel-ambrona) and [iquerejeta](https://github.com/iquerejeta) for providing the circuit implementation and the emulation parameters for P256 curve.

## References 

\[1\]. <a id="ffa"></a>M. Ambrona, D. Firsov, I. Querejeta-Azurmendi, *Efficient Foreign-Field Arithmetic in PLONK*, Cryptology ePrint Archive.  [eprint](https://eprint.iacr.org/2025/695)


\[2\]. <a id="popspaper"></a>S. Celi, A. Lehmann, S. Levin, A. Zacharakis, *Device Binding for Anonymous Credentials on Legacy Phones*.  [Eprint](https://eprint.iacr.org/2026/965)
