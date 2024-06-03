# X25519-Libjc-EasyCrypt-Proof
Bringing some libjc X25519 Jasmin-Easycrypt proofs up-to-date (WIP).

Below are files that run without errors as of latest commit date and time and do not include any `admit.` or `smt.`. 

- [X] EClib.ec 
- [X] W64limbs.ec 
- [X] Zp_25519.ec
- [X] Curve25519_auto.ec
    - Everything that is to be proven in Cryptoline, hence all lemmas are admitted for now.
- [X] Curve25519_spec.ec
- [X] Curve25519_Hop1.ec
- [X] Curve25519_Hop2.ec 
- [X] Curve25519_Hop3.ec
- [X] Curve25519_Hop4.ec
    - Warning: the post-conditions in all `*_ptr` equivalences are set to `true`, but this natrually needs to change to provide a proper correctness proof.

The original Easycrypt files can be found [in the x25519 branch in libjc](https://github.com/tfaoliveira/libjc/tree/x25519/proof/crypto_scalarmult/curve25519).
