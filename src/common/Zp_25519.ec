require import List Int IntDiv Ring CoreMap.
require import EClib W64limbs Array4 Array5 Array32 Array40.

from Jasmin require import JModel.

import Ring.IntID Array4 Array5 Array32 Array40.

require ZModP.

(* modular operations modulo P *)
op p = 2^255 - 19 axiomatized by pE.

lemma two_pow255E: 2^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 by done.

lemma pVal: p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by smt(pE two_pow255E).

op valid_ptr(p : int, o : int) = 0 <= o => 0 <= p /\ p + o < W64.modulus.

op load_array4 (m : global_mem_t, p : address) : W64.t list =
    [loadW64 m p; loadW64 m (p+8); loadW64 m (p+16); loadW64 m (p+24)].

op load_array5 (m : global_mem_t, p : address) : W64.t list =
    [loadW64 m p; loadW64 m (p+8); loadW64 m (p+16); loadW64 m (p+24); loadW64 m (p+32)].

op load_array32(m : global_mem_t, p : address) : W8.t Array32.t = 
      Array32.init (fun i => m.[p + i]).

op load_array40(m : global_mem_t, p : address) : W8.t Array40.t = 
      Array40.init (fun i => m.[p + i]).


(* Embedding into ring theory *)
clone import ZModP.ZModRing as Zp_25519 with
    op p <- p 
    rename "zmod" as "zp"
    proof ge2_p by rewrite pE.

(* congruence "mod p" *)

lemma zpcgr_over a b:
    zpcgr (a + 57896044618658097711785492504343953926634992332820282019728792003956564819968 * b) (a + 19 * b).
proof.
    have /= ->: (2^ 255) = 19 + p by rewrite pE.
    by rewrite (mulzC _ b) mulzDr addzA modzMDr mulzC.
qed.

lemma inzp_over x:
    inzp (57896044618658097711785492504343953926634992332820282019728792003956564819968 * x) = inzp (19*x).
proof. 
    by have /= := zpcgr_over 0 x; rewrite -eq_inzp.    
qed.

lemma zp_over_lt2p_red x:
    p <= x < 2*p =>
    x %% p = (x + 19) %% 2^255.
proof.
    move=> *.
    rewrite modz_minus. split; smt().
    have ->: x-p = x+19-2^255.
      by rewrite pE.
    rewrite modz_minus. split.
    apply (lez_trans (p+19) (2^255) (x+19)).
    rewrite pE. trivial. smt().
    move => *. apply (ltz_trans (2*p+19) (x+19) (2*2^255)). smt(). 
    simplify. rewrite pE; trivial.
    smt().
qed.

op inzp_limbs base l = inzp (val_limbs base l).

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
    have ? : 0 <= to_uint x3 %% 9223372036854775808 < 9223372036854775808 by smt(W64.to_uint_cmp modz_cmp).
    rewrite !addzA (mulzC 57896044618658097711785492504343953926634992332820282019728792003956564819968) divzMDr //.
    have ->: (to_uint x0 + 18446744073709551616 * to_uint x1 +
             340282366920938463463374607431768211456 * to_uint x2 +
             6277101735386680763835789423207666416102355444464034512896 * (to_uint x3 %% 9223372036854775808)) %/
             57896044618658097711785492504343953926634992332820282019728792003956564819968 = 0.
        by rewrite -divz_eq0 /#.
    by ring.
qed.



type Rep4 = W64.t Array4.t.
type Rep5 = W64.t Array5.t.
type Rep32 = W8.t Array32.t.
type Rep40 = W8.t Array40.t.

op valRep4       (x : Rep4)           : int   = val_limbs64 (Array4.to_list x) axiomatized by valRep4E.
op valRep4List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep4ListE.
op inzpRep4      (x : Rep4)           : zp    = inzp (valRep4 x)     axiomatized by inzpRep4E.
op inzpRep4List  (x: W64.t list)      : zp    = inzp (valRep4List x) axiomatized by inzpRep4ListE.
op valRep5       (x : Rep5)           : int   = val_limbs64 (Array5.to_list x) axiomatized by valRep5E.
op valRep5List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep5ListE.
op inzpRep5      (x : Rep5)           : zp    = inzp (valRep5 x)     axiomatized by inzpRep5E.
op inzpRep5List  (x: W64.t list)      : zp    = inzp (valRep5List x) axiomatized by inzpRep5ListE.


abbrev zpcgrRep4 (x : Rep4) (z : int) : bool  = zpcgr (valRep4 x) z.

op valRep32List  (x : W8.t list)      : int    = val_limbs8 x axiomatized by valRep32ListE.
op valRep32      (x : Rep32)          : int    = val_limbs8 (Array32.to_list x) axiomatized by valRep32E.
op inzpRep32     (x : Rep32)          : zp     = inzp (valRep32 x) axiomatized by inzpRep32E.
op inzpRep32List (x : W8.t list)      : zp     = inzp (valRep32List x) axiomatized by inzpRep32ListE.
op valRep40List  (x : W8.t list)      : int    = val_limbs8 x axiomatized by valRep40ListE.
op valRep40      (x : Rep40)          : int    = val_limbs8 (Array40.to_list x) axiomatized by valRep40E.
op inzpRep40     (x : Rep40)          : zp     = inzp (valRep40 x) axiomatized by inzpRep40E.
op inzpRep40List (x : W8.t list)      : zp     = inzp (valRep40List x) axiomatized by inzpRep40ListE.


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
    do 31! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 30! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 29! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 28! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 27! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 26! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 25! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 24! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8). 
    case: (i = 8). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 23! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 22! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 21! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 20! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 19! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 18! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 17! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 16! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8). 
    case: (i = 16). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 15! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 14! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 13! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 12! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 11! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 10! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 9! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 8! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8).
    case: (i = 24). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 7! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 6! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 5! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 4! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 3! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 2! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 1! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 0! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8).  move => *.
    smt(@W8).
qed.


lemma load_store_pos5 (mem: global_mem_t, p: W64.t, w: Rep5, i: int) :
    valid_ptr (to_uint p) 32 => (i = 0 \/ i = 8 \/ i = 16 \/ i = 24 \/ i = 32) => 
    w.[i %/ 8] =
        loadW64
            (storeW64
                (storeW64
                    (storeW64 
                        (storeW64 
                             (storeW64
                            mem (W64.to_uint p) w.[0])
                        (W64.to_uint (p + (W64.of_int 8)%W64)) w.[1])
                    (W64.to_uint (p + (W64.of_int 16)%W64)) w.[2])
                (W64.to_uint (p + (W64.of_int 24)%W64)) w.[3])
            (W64.to_uint (p + (W64.of_int 32)%W64)) w.[4])
            (W64.to_uint p + i).
proof.
    move => V0 I.
    rewrite /load_array4 !/storeW64 !/stores /= load8u8' /mkseq -iotaredE => />.   
    rewrite wordP => V1 V2. rewrite !to_uintD_small !to_uint_small => />.
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    rewrite pack8wE => />. rewrite get_of_list. smt().
    rewrite !bits8E !get_setE. auto => />. 
    case: (i = 0). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 39! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 38! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 37! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 36! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 35! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 34! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 33! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 32! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8). 
    case: (i = 8). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 31! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 30! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 29! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 28! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 27! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 26! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 25! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 24! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8). 
    case: (i = 16). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 23! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 22! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 21! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 20! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 19! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 18! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 17! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 16! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8).
    case: (i = 24). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 15! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 14! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 13! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 12! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 11! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 10! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 9! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 8! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8). 
     case: (i = 32). auto => />.
    case: (V1 %/ 8 = 0). move => V3. 
    do 7! (rewrite ifF 1:/#). smt(@W8). 
    case: (V1 %/ 8 - 1 = 0). move => *. 
    do 6! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 2 = 0). move => *. 
    do 5! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 3 = 0). move => *. 
    do 4! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 3! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 2! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 1! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 0! (rewrite ifF 1:/#). rewrite initE => />. smt(@W8).
    move => *. smt(@W8).       
    move => *.
    smt(@W8).
qed.

