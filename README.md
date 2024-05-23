# X25519-Libjc-EasyCrypt-Proof
Bringing some libjc X25519 Jasmin-Easycrypt proofs up-to-date (WIP).

Below are files that run without errors as of writing. Note that the imports may need some tinkering around with as my emacs path is broken for whatever reason.

- [X] EClib.ec 
- [X] W64limbs.ec (*warning, contains one lemma that currently results in false*)
- [X] Zp_25519.ec
- [X] Curve25519_spec.ec
- [X] Curve25519_Hop1.ec
- [ ] Curve25519_Hop2.ec
- [ ] Curve25519_Hop3.ec
- [ ] Curve25519_Hop4.ec

The original Easycrypt files can be found [in the x25519 branch in libjc](https://github.com/tfaoliveira/libjc/tree/x25519/proof/crypto_scalarmult/curve25519).
