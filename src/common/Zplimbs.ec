require import List Int IntDiv Ring CoreMap StdOrder.
require import Zp_25519 EClib W64limbs Array4 Array32.

from Jasmin require import JModel JWord.

import Zp Ring.IntID Array4 Array32 IntOrder JWord.W8 JWord.W64.


op inzp_limbs base l = inzp (val_limbs base l).

type Rep4 = W64.t Array4.t.
type Rep32 = W8.t Array32.t.

op valRep4       (x : Rep4)           : int   = val_limbs64 (Array4.to_list x) axiomatized by valRep4E.
op valRep4List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep4ListE.
op inzpRep4      (x : Rep4)           : zp    = inzp (valRep4 x)     axiomatized by inzpRep4E.
op inzpRep4List  (x: W64.t list)      : zp    = inzp (valRep4List x) axiomatized by inzpRep4ListE.

op valRep32List  (x : W8.t list)      : int    = val_limbs8 x axiomatized by valRep32ListE.
op valRep32      (x : Rep32)          : int    = val_limbs8 (Array32.to_list x) axiomatized by valRep32E.
op inzpRep32     (x : Rep32)          : zp     = inzp (valRep32 x) axiomatized by inzpRep32E.
op inzpRep32List (x : W8.t list)      : zp     = inzp (valRep32List x) axiomatized by inzpRep32ListE.


abbrev w256_nine = [true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
          false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false].

abbrev w64_nine = [true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
             false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
             false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
             false; false; false; false; false; false].

abbrev w64_2_63 = [true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; false].

abbrev w64_zero = [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
               false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
               false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false;
               false; false; false; false; false; false; false].

lemma val_limbs64_div2255 x0 x1 x2 x3:
    val_limbs64 [x0; x1; x2; x3] %/ 2^255 = to_uint x3 %/ 9223372036854775808.
proof.
    rewrite /val_digits /=.
    have := (divz_eq (to_uint x3) 9223372036854775808).
    rewrite addzC mulzC => {1}->.
    rewrite !mulzDr -!mulzA /=.
    have /= ? := W64.to_uint_cmp x0.
    have /= ? := W64.to_uint_cmp x1.
    have /= ? := W64.to_uint_cmp x2.
    have /= ? := W64.to_uint_cmp x3.
    have ? : 0 <= to_uint x3 %% 9223372036854775808 < 9223372036854775808 by smt().
    rewrite !addzA (mulzC 57896044618658097711785492504343953926634992332820282019728792003956564819968) divzMDr //.
    have ->: (to_uint x0 + 18446744073709551616 * to_uint x1 +
             340282366920938463463374607431768211456 * to_uint x2 +
             6277101735386680763835789423207666416102355444464034512896 * (to_uint x3 %% 9223372036854775808)) %/
             57896044618658097711785492504343953926634992332820282019728792003956564819968 = 0.
        by rewrite -divz_eq0 /#.
    by ring.
qed.


lemma val_limbs64_div2256 x0 x1 x2 x3:
    val_limbs64 [x0; x1; x2; x3] %/ 2^256 = to_uint x3 %/ 2^64.
proof.
    rewrite /val_digits /=.
    have := (divz_eq (to_uint x3) 18446744073709551616).
    rewrite addzC mulzC => {1}->.
    rewrite !mulzDr -!mulzA /=.
    have /= ? := W64.to_uint_cmp x0.
    have /= ? := W64.to_uint_cmp x1.
    have /= ? := W64.to_uint_cmp x2.
    have /= ? := W64.to_uint_cmp x3.
    have ? : 0 <= to_uint x3 %% 18446744073709551616 < 18446744073709551616 by smt().
    rewrite !addzA (mulzC 115792089237316195423570985008687907853269984665640564039457584007913129639936) divzMDr //.
    have ->: (to_uint x0 + 18446744073709551616 * to_uint x1 +
             340282366920938463463374607431768211456 * to_uint x2 +
             6277101735386680763835789423207666416102355444464034512896 * (to_uint x3 %% W64.modulus)) %/
             115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0.
        by rewrite -divz_eq0 /#.
    by ring.
qed.


op valid_ptr(p : int, o : int) = 0 <= o => 0 <= p /\ p + o < W64.modulus.

op load_array4 (m : global_mem_t, p : address) : W64.t list =
    [loadW64 m p; loadW64 m (p+8); loadW64 m (p+16); loadW64 m (p+24)].

op load_array32(m : global_mem_t, p : address) : W8.t Array32.t =
      Array32.init (fun i => m.[p + i]).

lemma valRep4ToPack x:  valRep4 x = W256.to_uint (W4u64.pack4 (Array4.to_list x)).
proof.
    rewrite to_uint_unpack4u64. rewrite valRep4E. congr. congr.
    rewrite pack4E !/to_list /mkseq -iotaredE => />.
    rewrite !W4u64.Pack.of_listE !wordP => />.
    do split.
    move => k K0 K1.
    case(k = 63) => /> *; case(k = 62) => /> *. case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
    move => k K0 K1.
    case(k = 63) => /> *; case(k = 62) => /> *. case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
    move => k K0 K1.
    case(k = 63) => /> *; case(k = 62) => /> *. case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
    move => k K0 K1.
    case(k = 63) => /> *; case(k = 62) => /> *. case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma inzpRep4ToPack x:  inzpRep4 x = inzp (W256.to_uint (W4u64.pack4 (Array4.to_list x))).
proof.
    rewrite inzpRep4E. congr. apply valRep4ToPack.
qed.

lemma valRep4ToPack_xy (x: W256.t, y):
    W256.to_uint x =  valRep4 y => x  = W4u64.pack4 (Array4.to_list y).
    rewrite valRep4ToPack. move => H. smt(@W256).
qed.


lemma x3_255_false (x: W64.t Array4.t, k: int):
    0 <= k < 64 =>
    (x.[3].[k] /\ ((bits2w w64_2_63))%W64.[k]) = if k = 63 then false else x.[3].[k].
proof.
     case(k = 63) => /> *; case(k = 62) => /> *. case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma x0k_255_false (x: W64.t Array4.t, k: int):
    0 <= k < 64 =>
    ((pack4 [x.[0]; x.[1]; x.[2]; x.[3]]).[255 <- false] \bits64 0).[k] = x.[0].[k].
proof.
    move => [K] K0.
    case(k = 63) => /> *; case(k = 62) => /> *; case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma x1k_255_false (x: W64.t Array4.t, k: int):
    0 <= k < 64 =>
    ((pack4 [x.[0]; x.[1]; x.[2]; x.[3]]).[255 <- false] \bits64 1).[k] = x.[1].[k].
proof.
    move => [K] K0.
    case(k = 63) => /> *; case(k = 62) => /> *; case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma x2k_255_false (x: W64.t Array4.t, k: int):
    0 <= k < 64 =>
    ((pack4 [x.[0]; x.[1]; x.[2]; x.[3]]).[255 <- false] \bits64 2).[k] = x.[2].[k].
proof.
    move => [K] K0.
    case(k = 63) => /> *; case(k = 62) => /> *; case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma x3k_255_false (x: W64.t Array4.t, k: int):
    0 <= k < 64 =>
    ((pack4 [x.[0]; x.[1]; x.[2]; x.[3]]).[255 <- false] \bits64 3).[k] = x.[3].[63 <- false].[k].
proof.
    move => [K] K0.
    case(k = 63) => /> *; case(k = 62) => /> *; case(k = 61) => /> *; case(k = 60) => /> *;
    case(k = 59) => /> *; case(k = 58) => /> *; case(k = 57) => /> *; case(k = 56) => /> *;
    case(k = 55) => /> *; case(k = 54) => /> *; case(k = 53) => /> *; case(k = 52) => /> *;
    case(k = 51) => /> *; case(k = 50) => /> *; case(k = 49) => /> *; case(k = 48) => /> *;
    case(k = 47) => /> *; case(k = 46) => /> *; case(k = 45) => /> *; case(k = 44) => /> *;
    case(k = 43) => /> *; case(k = 42) => /> *; case(k = 41) => /> *; case(k = 40) => /> *;
    case(k = 39) => /> *; case(k = 38) => /> *; case(k = 37) => /> *; case(k = 36) => /> *;
    case(k = 35) => /> *; case(k = 34) => /> *; case(k = 33) => /> *; case(k = 32) => /> *;
    case(k = 31) => /> *; case(k = 30) => /> *; case(k = 29) => /> *; case(k = 28) => /> *;
    case(k = 27) => /> *; case(k = 26) => /> *; case(k = 25) => /> *; case(k = 24) => /> *;
    case(k = 23) => /> *; case(k = 22) => /> *; case(k = 21) => /> *; case(k = 20) => /> *;
    case(k = 19) => /> *; case(k = 18) => /> *; case(k = 17) => /> *; case(k = 16) => /> *;
    case(k = 15) => /> *; case(k = 14) => /> *; case(k = 13) => /> *; case(k = 12) => /> *;
    case(k = 11) => /> *; case(k = 10) => /> *; case(k = 9) => />  *; case(k = 8) => />  *;
    case(k = 7) => />  *; case(k = 6) => />  *; case(k = 5) => />  *; case(k = 4) => />  *;
    case(k = 3) => />  *; case(k = 2) => />  *; case(k = 1) => />  *; case(k = 0) => />  *;
    smt().
qed.

lemma nine_256_k (k: int) :
    0 <= k < 256 =>
    ((init (nth false w256_nine)))%W256.[255 <- false].[k] =
(pack4
   [(init (nth false w64_nine))%W64;
    (init (nth false w64_zero))%W64;
    (init (nth false w64_zero))%W64;
    (init (nth false w64_zero))%W64]).[k].
proof.
    move => [K] K0.
    case(k = 255) => /> *; case(k = 254) => /> *; case(k = 253) => /> *; case(k = 252) => /> *;
    case(k = 251) => /> *; case(k = 250) => /> *; case(k = 249) => /> *; case(k = 248) => /> *;
    case(k = 247) => /> *; case(k = 246) => /> *; case(k = 245) => /> *; case(k = 244) => /> *;
    case(k = 243) => /> *; case(k = 242) => /> *; case(k = 241) => /> *; case(k = 240) => /> *;
    case(k = 239) => /> *; case(k = 238) => /> *; case(k = 237) => /> *; case(k = 236) => /> *;
    case(k = 235) => /> *; case(k = 234) => /> *; case(k = 233) => /> *; case(k = 232) => /> *;
    case(k = 231) => /> *; case(k = 230) => /> *; case(k = 229) => /> *; case(k = 228) => /> *;
    case(k = 227) => /> *; case(k = 226) => /> *; case(k = 225) => /> *; case(k = 224) => /> *;
    case(k = 223) => /> *; case(k = 222) => /> *; case(k = 221) => /> *; case(k = 220) => /> *;
    case(k = 219) => /> *; case(k = 218) => /> *; case(k = 217) => /> *; case(k = 216) => /> *;
    case(k = 215) => /> *; case(k = 214) => /> *; case(k = 213) => /> *; case(k = 212) => /> *;
    case(k = 211) => /> *; case(k = 210) => /> *; case(k = 209) => /> *; case(k = 208) => /> *;
    case(k = 207) => /> *; case(k = 206) => /> *; case(k = 205) => /> *; case(k = 204) => /> *;
    case(k = 203) => /> *; case(k = 202) => /> *; case(k = 201) => /> *; case(k = 200) => /> *;
    case(k = 199) => /> *; case(k = 198) => /> *; case(k = 197) => /> *; case(k = 196) => /> *;
    case(k = 195) => /> *; case(k = 194) => /> *; case(k = 193) => /> *; case(k = 192) => /> *;
    case(k = 191) => /> *; case(k = 190) => /> *; case(k = 189) => /> *; case(k = 188) => /> *;
    case(k = 187) => /> *; case(k = 186) => /> *; case(k = 185) => /> *; case(k = 184) => /> *;
    case(k = 183) => /> *; case(k = 182) => /> *; case(k = 181) => /> *; case(k = 180) => /> *;
    case(k = 179) => /> *; case(k = 178) => /> *; case(k = 177) => /> *; case(k = 176) => /> *;
    case(k = 175) => /> *; case(k = 174) => /> *; case(k = 173) => /> *; case(k = 172) => /> *;
    case(k = 171) => /> *; case(k = 170) => /> *; case(k = 169) => /> *; case(k = 168) => /> *;
    case(k = 167) => /> *; case(k = 166) => /> *; case(k = 165) => /> *; case(k = 164) => /> *;
    case(k = 163) => /> *; case(k = 162) => /> *; case(k = 161) => /> *; case(k = 160) => /> *;
    case(k = 159) => /> *; case(k = 158) => /> *; case(k = 157) => /> *; case(k = 156) => /> *;
    case(k = 155) => /> *; case(k = 154) => /> *; case(k = 153) => /> *; case(k = 152) => /> *;
    case(k = 151) => /> *; case(k = 150) => /> *; case(k = 149) => /> *; case(k = 148) => /> *;
    case(k = 147) => /> *; case(k = 146) => /> *; case(k = 145) => /> *; case(k = 144) => /> *;
    case(k = 143) => /> *; case(k = 142) => /> *; case(k = 141) => /> *; case(k = 140) => /> *;
    case(k = 139) => /> *; case(k = 138) => /> *; case(k = 137) => /> *; case(k = 136) => /> *;
    case(k = 135) => /> *; case(k = 134) => /> *; case(k = 133) => /> *; case(k = 132) => /> *;
    case(k = 131) => /> *; case(k = 130) => /> *; case(k = 129) => /> *; case(k = 128) => /> *;
    case(k = 127) => /> *; case(k = 126) => /> *; case(k = 125) => /> *; case(k = 124) => /> *;
    case(k = 123) => /> *; case(k = 122) => /> *; case(k = 121) => /> *; case(k = 120) => /> *;
    case(k = 119) => /> *; case(k = 118) => /> *; case(k = 117) => /> *; case(k = 116) => /> *;
    case(k = 115) => /> *; case(k = 114) => /> *; case(k = 113) => /> *; case(k = 112) => /> *;
    case(k = 111) => /> *; case(k = 110) => /> *; case(k = 109) => /> *; case(k = 108) => /> *;
    case(k = 107) => /> *; case(k = 106) => /> *; case(k = 105) => /> *; case(k = 104) => /> *;
    case(k = 103) => /> *; case(k = 102) => /> *; case(k = 101) => /> *; case(k = 100) => /> *;
    case(k = 99) => /> * ; case(k = 98) => /> * ; case(k = 97) => /> * ; case(k = 96) => />  *;
    case(k = 95) => /> * ; case(k = 94) => /> * ; case(k = 93) => /> * ; case(k = 92) => />  *;
    case(k = 91) => /> * ; case(k = 90) => /> * ; case(k = 89) => /> * ; case(k = 88) => />  *;
    case(k = 87) => /> * ; case(k = 86) => /> * ; case(k = 85) => /> * ; case(k = 84) => />  *;
    case(k = 83) => /> * ; case(k = 82) => /> * ; case(k = 81) => /> * ; case(k = 80) => />  *;
    case(k = 79) => /> * ; case(k = 78) => /> * ; case(k = 77) => /> * ; case(k = 76) => />  *;
    case(k = 75) => /> * ; case(k = 74) => /> * ; case(k = 73) => /> * ; case(k = 72) => />  *;
    case(k = 71) => /> * ; case(k = 70) => /> * ; case(k = 69) => /> * ; case(k = 68) => />  *;
    case(k = 67) => /> * ; case(k = 66) => /> * ; case(k = 65) => /> * ; case(k = 64) => />  *;
    case(k = 63) => /> * ; case(k = 62) => /> * ; case(k = 61) => /> * ; case(k = 60) => />  *;
    case(k = 59) => /> * ; case(k = 58) => /> * ; case(k = 57) => /> * ; case(k = 56) => />  *;
    case(k = 55) => /> * ; case(k = 54) => /> * ; case(k = 53) => /> * ; case(k = 52) => />  *;
    case(k = 51) => /> * ; case(k = 50) => /> * ; case(k = 49) => /> * ; case(k = 48) => />  *;
    case(k = 47) => /> * ; case(k = 46) => /> * ; case(k = 45) => /> * ; case(k = 44) => />  *;
    case(k = 43) => /> * ; case(k = 42) => /> * ; case(k = 41) => /> * ; case(k = 40) => />  *;
    case(k = 39) => /> * ; case(k = 38) => /> * ; case(k = 37) => /> * ; case(k = 36) => />  *;
    case(k = 35) => /> * ; case(k = 34) => /> * ; case(k = 33) => /> * ; case(k = 32) => />  *;
    case(k = 31) => /> * ; case(k = 30) => /> * ; case(k = 29) => /> * ; case(k = 28) => />  *;
    case(k = 27) => /> * ; case(k = 26) => /> * ; case(k = 25) => /> * ; case(k = 24) => />  *;
    case(k = 23) => /> * ; case(k = 22) => /> * ; case(k = 21) => /> * ; case(k = 20) => />  *;
    case(k = 19) => /> * ; case(k = 18) => /> * ; case(k = 17) => /> * ; case(k = 16) => />  *;
    case(k = 15) => /> * ; case(k = 14) => /> * ; case(k = 13) => /> * ; case(k = 12) => />  *;
    case(k = 11) => /> * ; case(k = 10) => /> * ; case(k = 9) => />  * ; case(k = 8) =>  />  *;
    case(k = 7) => />  * ; case(k = 6) => />  * ; case(k = 5) => />  * ; case(k = 4) =>  />  *;
    case(k = 3) => />  * ; case(k = 2) => />  * ; case(k = 1) => />  * ; case(k = 0) =>  />  *.
    smt().
qed.

lemma load_store_pos (mem: global_mem_t, p: W64.t, w: Rep4, i: int) :
    valid_ptr (to_uint p) 32 => (i = 0 \/ i = 8 \/ i = 16 \/ i = 24) =>
    w.[i %/ 8] =
        loadW64
            (storeW64
                (storeW64
                    (storeW64
                        (storeW64 mem (W64.to_uint p) w.[0])
                        (W64.to_uint (p + (W64.of_int 8)%W64)) w.[1])
                    (W64.to_uint (p + (W64.of_int 16)%W64)) w.[2])
                (W64.to_uint (p + (W64.of_int 24)%W64)) w.[3])
            (W64.to_uint p + i).
proof.
    move => V0 I.
    rewrite /load_array4 !/storeW64 !/stores /= load8u8' /mkseq -iotaredE => />.
    rewrite wordP => V1 V2. rewrite !to_uintD_small !to_uint_small => />.
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    rewrite pack8wE => />. rewrite get_of_list. smt().
    rewrite !bits8E !get_setE. auto => />.
    case: (i = 0). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 31! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 30! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 29! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 28! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 27! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 26! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 25! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 24! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 8). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 23! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 22! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 21! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 20! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 19! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 18! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 17! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 16! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 16). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 15! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 14! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 13! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 12! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 11! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 10! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 9! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 8! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 24). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 7! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 6! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 5! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 4! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 3! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 2! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 1! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 0! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).  move => *.
    smt(W8.initE).
qed.
