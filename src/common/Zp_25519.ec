require import List Int IntDiv Ring CoreMap StdOrder.
require import EClib W64limbs Array4 Array5 Array32 Array40.

from Jasmin require import JModel.

import Ring.IntID Array4 Array5 Array32 Array40 IntOrder.

require ZModP.

(* modular operations modulo P *)
op p = 2^255 - 19 axiomatized by pE.

lemma two_pow255E: 2^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 by done.

lemma pVal: p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by smt(pE two_pow255E).

op valid_ptr(p : int, o : int) = 0 <= o => 0 <= p /\ p + o < W64.modulus.

op load_array4 (m : global_mem_t, p : address) : W64.t list =
    [loadW64 m p; loadW64 m (p+8); loadW64 m (p+16); loadW64 m (p+24)].

op load_array32(m : global_mem_t, p : address) : W8.t Array32.t = 
      Array32.init (fun i => m.[p + i]).


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


lemma twop255_cgr : 2^255 %% p = 19 by smt(@JUtils ).
lemma twop256_cgr : 2^256 %% p = 38 by smt(@JUtils).

lemma ltP_overflow x:
    (x + 2^255 + 19 < 2^256) = (x < p).
proof.
    have ->: 2^255 = p + 19 by rewrite pE /#. 
    have ->: 2^256 = p + p + 19 + 19 by rewrite !pE /#.
smt().
qed.

op red x = if x + 2^255 + 19 < 2^256 then x else (x + 2^255 + 19) %% 2^256.

lemma redE x:
    p <= x < 2^256 =>
    (x + 2^255 + 19) %% 2^256 = x - p.
proof.
    move=> [H1 H2].
    pose y := x-p.
    rewrite (_: x= y+p) 1:/# (_:2^255 = p+19) 1:pE 1:/#.
    rewrite -addrA -addrA (_:p + (p + 19 + 19) = 2^256) 1:pE 1:/#.
    rewrite modzDr modz_small; last reflexivity.
    apply bound_abs.
    move: H2; have ->: 2^256 = p + p + 19 + 19 by rewrite !pE /#.
    smt(pVal).
qed.

lemma redP x:
    0 <= x < 2^256 =>
    x %% p = red (red x).
proof.
    move=> [H1 H2].
    rewrite /red !ltP_overflow.
    case: (x < p) => Hx1.
    rewrite Hx1 /= modz_small; last done.
        by apply bound_abs => /#.
    rewrite redE.
        split => *; [smt() | assumption].
    case: (x - p < p) => Hx2.
        rewrite {1}(_: x = x - p + p) 1:/# modzDr modz_small; last reflexivity.
    by apply bound_abs => /#.
    rewrite redE.
    split => *; first smt().
    rewrite (_:W256.modulus = W256.modulus-0) 1:/#.
    apply (ltr_le_sub); first assumption. 
    smt(pVal). 
    rewrite (_: x = x - p - p + p + p) 1:/#.
    rewrite modzDr modzDr modz_small.
    apply bound_abs; split => *; first smt().
    move: H2; have ->: 2^256 = p + p + 19 + 19 by     rewrite !pE /#.
    smt(pVal).
    smt().
qed.

op bezout_coef256 (x : int) : int * int = (x %/ W256.modulus, x %% W256.modulus).

op red256 (x: int) : int =
    (bezout_coef256 x).`2 + 38 * (bezout_coef256 x).`1.
    
lemma red256P x: zpcgr x (red256 x).
proof.
    by rewrite {1}(divz_eq x (2^256)) -modzDml -modzMmr twop256_cgr 
    modzDml /red256 /split256 /= addrC mulrC.
qed.


lemma red256_bnd B x:
    0 <= x < W256.modulus * B => 
    0 <= red256 x < W256.modulus + 38*B.
proof.
    move=> [Hx1 Hx2]; rewrite /red256 /bezout_coef256 /=; split => *.
    apply addz_ge0; first smt(modz_cmp).
    apply mulr_ge0; first done.
    apply divz_ge0; smt().
    have H1: x %/ W256.modulus < B by smt(@JUtils).
    have H2: x %% W256.modulus < W256.modulus by smt(modz_cmp).
    smt(@JUtils).
qed.

lemma red256_once x:
    0 <= x < W256.modulus * W256.modulus =>
    0 <= red256 x < W256.modulus*39.
proof.
    have ->: W256.modulus*39 = W256.modulus + 38*W256.modulus by ring.
    exact red256_bnd.
qed.

lemma red256_twice x:
    0 <= x < W256.modulus*W256.modulus =>
    0 <= red256 (red256 x) < W256.modulus*2.
proof.
    move=> Hx; split => *.
    smt(red256_once).
    move: (red256_once x Hx).
    move => Hy.
    move: (red256_bnd 39 _ Hy); smt().
qed.

lemma red256_twiceP x a b:
    0 <= x < W256.modulus*W256.modulus =>
    (a,b) = bezout_coef256 (red256 (red256 x)) =>
    (* 0 <= a < 2 /\ (a=0 \/ b <= 38*38).*)
    a=0 \/ a=1 /\ b <= 38*38.
proof.
    move=> Hx Hab. 
    have Ha: 0 <= a < 2.
    have H := (red256_twice x Hx).
    move: Hab; rewrite /split256.
    move => [-> _]. smt(@JUtils).
    case: (a=0) => Ea /=; first done.
    have {Ea} Ea: a=1 by smt().
    rewrite Ea /=.
    move: Hab; pose y := red256 x.
    rewrite /red256 /bezout_coef256 /=.
    pose yL := y%%W256.modulus.
    pose yH := y%/W256.modulus.
    have Hy := red256_once x Hx.
    have HyH : 0 <= yH <= 38 by smt().
    move => [Hab1 Hab2].
    have E: W256.modulus + b = yL + 38 * yH.
    by move: (divz_eq (yL + 38 * yH) W256.modulus); smt(@JUtils).
    smt(modz_cmp).
qed.

lemma red256_thrice x:
    0 <= x < W256.modulus*W256.modulus =>
    0 <= red256 (red256 (red256 x)) < W256.modulus.
proof.
    move=> Hx; pose y:= red256 (red256 x).
    rewrite /red256.
    have := (red256_twiceP x (bezout_coef256 y).`1 (bezout_coef256 y).`2 _ _).
    smt(@JUtils).
    smt(red256_twice).
    move=> [->|[-> H2]] /=.
    rewrite /bezout_coef256; smt(modz_cmp).
    split.
    rewrite /bezout_coef256; smt(modz_cmp).
    smt().
qed.

op reduce x = red256 (red256 (red256 x)).

lemma reduceP x:
    0 <= x < W256.modulus * W256.modulus =>
    zpcgr x (reduce x) /\ 0 <= reduce x < W256.modulus.
proof.
    rewrite /reduce => H; split; first smt(red256P).
    smt(@JUtils red256_thrice).
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
type Rep32 = W8.t Array32.t.
type Rep40 = W8.t Array40.t.

op valRep4       (x : Rep4)           : int   = val_limbs64 (Array4.to_list x) axiomatized by valRep4E.
op valRep4List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep4ListE.
op inzpRep4      (x : Rep4)           : zp    = inzp (valRep4 x)     axiomatized by inzpRep4E.
op inzpRep4List  (x: W64.t list)      : zp    = inzp (valRep4List x) axiomatized by inzpRep4ListE.


abbrev zpcgrRep4 (x : Rep4) (z : int) : bool  = zpcgr (valRep4 x) z.

op valRep32List  (x : W8.t list)      : int    = val_limbs8 x axiomatized by valRep32ListE.
op valRep32      (x : Rep32)          : int    = val_limbs8 (Array32.to_list x) axiomatized by valRep32E.
op inzpRep32     (x : Rep32)          : zp     = inzp (valRep32 x) axiomatized by inzpRep32E.
op inzpRep32List (x : W8.t list)      : zp     = inzp (valRep32List x) axiomatized by inzpRep32ListE.


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


