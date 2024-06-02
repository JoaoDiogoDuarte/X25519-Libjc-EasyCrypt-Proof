# X25519-Libjc-EasyCrypt-Proof
Bringing some libjc X25519 Jasmin-Easycrypt proofs up-to-date (WIP).

Below are files that run without errors as of writing and do not include `admit.` or `smt.`. 

- [X] EClib.ec 
- [X] W64limbs.ec 
    - Requires some pruning for unused lemmas that do not prove anything relevant for this scenario.
    - Contains  one lemma that currently results in false but it is probably not be necessary and can be removed.
- [X] Zp_25519.ec
- [X] Curve25519_auto.ec
    - Everything that is to be proven in Cryptoline, hence all lemmas are admitted for now.
- [X] Curve25519_spec.ec
- [X] Curve25519_Hop1.ec
- [ ] Curve25519_Hop2.ec 
    - Includes two lemmas that end in `admit` because Easycrypt is a bit weird with assigning variables "to themselves" (e.g. `h <@ sqr(h)`) and I am still figuring out how to approach the montgomery ladder proof considering the spec's updated code.
- [X] Curve25519_Hop3.ec
- [ ] Curve25519_Hop4.ec
    - All lemmas with names `*_ptr`, `*itr_sqr_s*`, `*jade*` (in total, 6) are admitted as I need to learn about dealing with pointers in Easycrypt. However, the bulk of the work has already been done as their non-pointer versions have been proved. 
    
The original Easycrypt files can be found [in the x25519 branch in libjc](https://github.com/tfaoliveira/libjc/tree/x25519/proof/crypto_scalarmult/curve25519).
