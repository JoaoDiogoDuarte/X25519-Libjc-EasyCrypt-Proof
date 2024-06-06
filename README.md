# X25519-Libjc-EasyCrypt-Proof
Bringing some libjc X25519 Jasmin-Easycrypt proofs up-to-date (WIP).

Below are files that run without errors as of latest commit date and time and do not include any `admit.` or `smt.`. 


### Common
- [X] EClib.ec 
- [X] W64limbs.ec 
- [X] Zp_25519.ec
- [X] Curve25519_spec.ec
- [X] Curve25519_Hop1.ec
- [X] Curve25519_Hop2.ec 
- [X] Curve25519_Hop3.ec

### Ref4
- [X] Curve25519_Hop4.ec
- [X] Curve25519_auto4.ec

### Ref5
- [X] Curve25519_Hop4.ec
- [X] Curve25519_auto5.ec

### Mulx
- [ ] Curve25519_Hop4.ec 
    - Invert and add_double not done.
- [X] Curve25519_auto_mulx.ec

Everything that is to be proven in Cryptoline are in the Curve25519_auto* files, Due to this, all lemmas are admitted for now.

The original Easycrypt files can be found [in the x25519 branch in libjc](https://github.com/tfaoliveira/libjc/tree/x25519/proof/crypto_scalarmult/curve25519).
