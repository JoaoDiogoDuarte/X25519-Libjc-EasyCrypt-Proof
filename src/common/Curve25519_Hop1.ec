require import Bool List Int IntDiv CoreMap Real Ring StdOrder Zp_25519.
require import Curve25519_Spec.
import Zp_25519  Ring.IntID Zp_25519.ZModpRing.

from Jasmin require import JModel.

(* exp exp *)
lemma expE (z : zp) (e1 e2 : int) : 0 <= e1 /\ 0 <= e2 =>
    ZModpRing.exp (ZModpRing.exp z e1) e2 =
    ZModpRing.exp z (e1*e2).
proof.
    rewrite -ZModpRing.exprM => />.
qed.

(* returns the first 2 elements of the input triple *)
op select_tuple_12 (t : ('a * 'a) * ('a * 'a) * 'c) = (t.`1, t.`2).

(* if the third element is true then the first 2 elements are swapped *)
  (*  - this op returns the first 2 elements in
  the correct order       *)
op reconstruct_tuple (t : ('a * 'a) * ('a * 'a) * bool) =
    if t.`3
    then swap_tuple (select_tuple_12 t)
    else select_tuple_12 t.

lemma eq_reconstruct_select_tuple (t : (('a * 'a) * ('a * 'a) * bool)) :
    t.`3 = false => 
    select_tuple_12 t = reconstruct_tuple t.
proof.
    rewrite /reconstruct_tuple /select_tuple_12.
    by move => ? /#.
qed.

(* similar to foldl_in_eq -- the proof is basically the same -- defined in JMemory *)
(* - foldl_in_eq states that any 2 foldl's are the same if the functions are equiv *)
(* - we will need to prove that + that the state a2 have a relational invariant r  *)
lemma foldl_in_eq_r (f1 : 'a1 -> 'b -> 'a1)
                    (f2 : 'a2 -> 'b -> 'a2)
                    (s  : 'b list)
                    (a2 : 'a2)
                    (r  : 'a2 -> 'a1) :
    (forall a2 b, b \in s => f1 (r a2) b = r (f2 a2 b)) => 
                        foldl f1 (r a2) s = r (foldl f2 a2 s).
proof.
    move: s a2. elim.
        by move => a2.
    move => x l hrec a2 /= hin. rewrite hin.
    by left.
    rewrite hrec //; move => ? ? h; rewrite hin.
        by right.
    by trivial.
qed.

(** step1: add_and_double = add_and_double1 : reordered to match implementation **)
op add_and_double1 (qx : zp) (nqs : (zp * zp) * (zp * zp)) =
  let x1 = qx in
  let (x2, z2) = nqs.`1 in
  let (x3, z3) = nqs.`2 in
  let t0 = x2 - z2 in
  let x2 = Zp_25519.(+) x2 z2 in 
  let t1 = x3 - z3 in
  let z2 = Zp_25519.(+) x3 z3 in
  let z3 = Zp_25519.( * ) x2 t1 in
  let z2 = Zp_25519.( * ) z2 t0 in
  let t2 = Zp_25519.( * ) x2 x2 in
  let t1 = Zp_25519.( * ) t0 t0 in
  let x3 = Zp_25519.(+) z3 z2 in
  let z2 = z3 - z2 in
  let x2 = Zp_25519.( * ) t2 t1 in
  let t0 = t2 - t1 in
  let z2 = Zp_25519.( * ) z2 z2 in
  let z3 = Zp_25519.( * ) t0 (inzp 121665) in
  let x3 = Zp_25519.( * ) x3 x3 in
  let t2 = Zp_25519.( + ) t2 z3 in
  let z3 = Zp_25519.( * ) x1 z2 in
  let z2 = Zp_25519.( * ) t0 t2
  in  ((x2,z2), (x3,z3)).

lemma eq_add_and_double1 (qx : zp) (nqs : (zp * zp) * (zp * zp)) :
    add_and_double qx nqs = add_and_double1 qx nqs.
proof.
    rewrite /add_and_double /add_and_double1.
    simplify => /#.
qed.

op montgomery_ladder1(init : zp, k : W256.t) =
    let nqs0 = ((Zp_25519.one,Zp_25519.zero),(init,Zp_25519.one)) in
    foldl (fun (nqs : (zp * zp) * (zp * zp)) ctr => 
         if ith_bit k ctr
         then swap_tuple (add_and_double1 init (swap_tuple(nqs)))
         else add_and_double1 init nqs) nqs0 (rev (iota_ 0 255)).

(* lemma: montgomery_ladder = montgomery_ladder1 *)
lemma eq_montgomery_ladder1 (init : zp) (k : W256.t) :
    montgomery_ladder init k = montgomery_ladder1 init k.
proof.
    rewrite /montgomery_ladder /montgomery_ladder1 /=.
    apply foldl_in_eq.
    move => nqs ctr inlist => /=.
    case (ith_bit k ctr).
        by move => ?; rewrite /swap_tuple /#.
    by move => ?; rewrite /swap_tuple /#.
qed.

(** step 2: isolate foldl function and introduce reconstruct tuple **)
op montgomery_ladder2_step(k : W256.t, init : zp, nqs : (zp * zp) * (zp * zp), ctr : int) =
    if ith_bit k ctr
    then swap_tuple(add_and_double1 init (swap_tuple(nqs)))
    else add_and_double1 init nqs.

op montgomery_ladder2(init : zp, k : W256.t) =
    let nqs0 = reconstruct_tuple ((Zp_25519.one,Zp_25519.zero),(init,Zp_25519.one),false) in
    foldl (montgomery_ladder2_step k init) nqs0 (rev (iota_ 0 255)).

(* lemma: montgomery_ladder1 = montgomery_ladder2 *)
lemma eq_montgomery_ladder2 (init : zp) (k : W256.t) :
    montgomery_ladder1 init k = montgomery_ladder2 init k.
proof.
    rewrite /montgomery_ladder1 /montgomery_ladder2 /reconstruct_tuple /select_tuple_12.
    rewrite /montgomery_ladder2_step.
    by simplify.
qed.

(** step 3: extend the state to contain an additional bit stating if the state is swapped **)
op cswap( t : ('a * 'a) * ('a * 'a), b : bool ) = 
    if b
    then swap_tuple t
    else t.

op montgomery_ladder3_step(k : W256.t, init : zp, nqs : (zp * zp) * (zp * zp) * bool, ctr : int) =
    let nqs = cswap (select_tuple_12 nqs) (nqs.`3 ^^ (ith_bit k ctr)) in
    let nqs = add_and_double1 init nqs in
    (nqs.`1, nqs.`2, (ith_bit k ctr)).

op montgomery_ladder3(init : zp, k : W256.t) =
    let nqs0 = ((Zp_25519.one,Zp_25519.zero),(init,Zp_25519.one),false) in
    foldl (montgomery_ladder3_step k init) nqs0 (rev (iota_ 0 255)).

lemma eq_montgomery_ladder3_reconstruct (init : zp) (k: W256.t) :
    montgomery_ladder2 init k = reconstruct_tuple (montgomery_ladder3 init k).
proof.
    rewrite /montgomery_ladder2 /montgomery_ladder3 //=.
    apply foldl_in_eq_r.
    move => ? ? ?.
    rewrite /reconstruct_tuple /montgomery_ladder2_step /montgomery_ladder3_step.
    rewrite /swap_tuple /select_tuple_12 /cswap.
    simplify => /#.
qed.
    
(* lemma: if the first bit of k is 0, which will be because of decodeScalar25519, *)
(*  then montgomery_ladder2 = select_tuple_12 montgomery_ladder3 *)
lemma eq_montgomery_ladder3 (init : zp) (k: W256.t) :
    k.[0] = false =>
    montgomery_ladder2 init k = select_tuple_12 (montgomery_ladder3 init k).
proof.
    move => hkf.  
    have tbf : (montgomery_ladder3 init k).`3 = false. (*third bit false*)
    rewrite /montgomery_ladder3 /montgomery_ladder3_step /select_tuple_12 /cswap /ith_bit /swap_tuple => />.
    rewrite foldl_rev; auto => />; rewrite -iotaredE => />.  
    have seqr : select_tuple_12 (montgomery_ladder3 init k) = reconstruct_tuple (montgomery_ladder3 init k).
        by apply /eq_reconstruct_select_tuple /tbf.
    rewrite seqr.
    by apply eq_montgomery_ladder3_reconstruct.
qed.

(** step 4: montgomery_ladder = select_tuple_12 montgomery_ladder3 **)
lemma eq_montgomery_ladder123 (init : zp) (k: W256.t) :
    k.[0] = false => montgomery_ladder init k = select_tuple_12 (montgomery_ladder3 init k).
proof.
    move => H.
    rewrite eq_montgomery_ladder1 eq_montgomery_ladder2 eq_montgomery_ladder3. apply H.
    trivial.
qed.

(** step 5: introduce reordering in encode point **)
(*  - we split invert in 3 parts to make the proof faster *)
op invert_p_p1(z1 : zp) : (zp*zp) =
    let z2 = exp z1 2 in
    let z8 = exp z2 (2*2) in
    let z9 = Zp_25519.( * ) z1 z8 in
    let z11 = Zp_25519.( * ) z2 z9 in
    let z22 = exp z11 2 in
    let z_5_0 = Zp_25519.( * ) z9 z22 in
        (z_5_0, z11).

op invert_p_p2(z_5_0 : zp) : zp = 
    let z_10_5 = ZModpRing.exp z_5_0 (2^5) in
    let z_10_0 = Zp_25519.( * ) z_10_5 z_5_0 in
    let z_20_10 = ZModpRing.exp z_10_0 (2^10) in
    let z_20_0 = Zp_25519.( * ) z_20_10 z_10_0 in
    let z_40_20 = ZModpRing.exp z_20_0 (2^20) in
    let z_40_0 = Zp_25519.( * ) z_40_20 z_20_0 in
    let z_50_10 = ZModpRing.exp z_40_0 (2^10) in
    let z_50_0 = Zp_25519.( * ) z_50_10 z_10_0 in
        z_50_0.

op invert_p_p3(z_50_0 z11 : zp) : zp =
    let z_100_50 = ZModpRing.exp z_50_0 (2^50) in
    let z_100_0 = Zp_25519.( * ) z_100_50 z_50_0 in
    let z_200_100 = ZModpRing.exp z_100_0 (2^100) in
    let z_200_0 = Zp_25519.( * ) z_200_100 z_100_0 in
    let z_250_50 = ZModpRing.exp z_200_0 (2^50) in
    let z_250_0 = Zp_25519.( * ) z_250_50 z_50_0 in
    let z_255_5 = ZModpRing.exp z_250_0 (2^5) in
    let z_255_21 = Zp_25519.( * ) z_255_5 z11 in
        z_255_21    .

op invert_p(z1 : zp) : zp =
    let (z_5_0, z11) = invert_p_p1 z1 in
    let z_50_0 = invert_p_p2 z_5_0 in
    let z_255_21 = invert_p_p3 z_50_0 z11 in
    z_255_21 axiomatized by invert_pE.

lemma eq_invert_p (z1: zp) :
    invert_p z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite invert_pE.
    rewrite /invert_p_p1 /= expE //= /invert_p_p3 /invert_p_p2 //=. 
    rewrite -!exprS // -!exprD_nneg => />. rewrite -!exprM -!exprD_nneg => />.
    rewrite -!exprM => />. rewrite -!exprD_nneg => />. rewrite -!exprM => />.
    rewrite -!exprD_nneg => />. rewrite -!exprM => />. rewrite -!exprD_nneg => />.
    rewrite -!exprM => />. rewrite -!exprD_nneg => />. rewrite -!exprM => />.
    rewrite -!exprD_nneg => />. rewrite -!exprM => />. rewrite -!exprD_nneg => />.
    rewrite -!exprM => />. rewrite -exprD_nneg => />. rewrite -exprM => />.
    rewrite -!exprD_nneg => />. rewrite pE => />.
qed. (* there must be a faster and elegant way of doing this *)

(* now we define invert as one op and prove it equiv to exp z1 (p-2) *)
op invert0(z1 : zp) : zp =
    let z2 = ZModpRing.exp z1 2 in
    let z8 = ZModpRing.exp z2 (2*2) in
    let z9 = Zp_25519.( * ) z1 z8 in
    let z11 = Zp_25519.( * ) z2 z9 in
    let z22 = ZModpRing.exp z11 2 in
    let z_5_0 =  Zp_25519.( * ) z9 z22 in
    let z_10_5 = ZModpRing.exp z_5_0 (2^5) in
    let z_10_0 =  Zp_25519.( * ) z_10_5 z_5_0 in
    let z_20_10 = ZModpRing.exp z_10_0 (2^10) in
    let z_20_0 =  Zp_25519.( * ) z_20_10 z_10_0 in
    let z_40_20 = ZModpRing.exp z_20_0 (2^20) in
    let z_40_0 =  Zp_25519.( * ) z_40_20 z_20_0 in
    let z_50_10 = ZModpRing.exp z_40_0 (2^10) in
    let z_50_0 =  Zp_25519.( * ) z_50_10 z_10_0 in
    let z_100_50 = ZModpRing.exp z_50_0 (2^50) in
    let z_100_0 =  Zp_25519.( * ) z_100_50 z_50_0 in
    let z_200_100 = ZModpRing.exp z_100_0 (2^100) in
    let z_200_0 =  Zp_25519.( * ) z_200_100 z_100_0 in
    let z_250_50 = ZModpRing.exp z_200_0 (2^50) in
    let z_250_0 =  Zp_25519.( * ) z_250_50 z_50_0 in
    let z_255_5 = ZModpRing.exp z_250_0 (2^5) in
    let z_255_21 =  Zp_25519.( * ) z_255_5 z11 in
        z_255_21 axiomatized by invert0E.

lemma eq_invert0 (z1 : zp) :
    invert0 z1 = invert_p z1.
proof.
    rewrite invert0E invert_pE /invert_p_p1 /invert_p_p2 /invert_p_p3 //.
qed.

lemma eq_invert0p (z1 : zp) :
    invert0 z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite eq_invert0 eq_invert_p //.
qed.

op sqr(z : zp) : zp =
    ZModpRing.exp z 2.

op it_sqr(e : int, z : zp) : zp =
    ZModpRing.exp z (2^e).

op it_sqr1(e : int, z : zp) : zp =
    foldl (fun (z' : zp) _ => exp z' 2) z (iota_ 0 e).

op it_sqr_x2(e : int, z : zp) : zp =
    ZModpRing.exp z (4^e).

op it_sqr1_x2(e : int, z : zp) : zp =
    foldl (fun (z' : zp) _ => exp z' 4) z (iota_ 0 e).

lemma eq_it_sqr1 (e : int, z : zp) :
    0 <= e  =>
    it_sqr1 e z = it_sqr e z.
proof.
    move : e.
    rewrite /it_sqr1 /it_sqr. elim. simplify. rewrite -iotaredE expr1 //. 
    move => i ige0 hin.
    rewrite iotaSr // -cats1 foldl_cat hin /= expE /=.  smt(gt0_pow2).
    congr. clear hin.
    rewrite exprS // mulzC //.
qed.

lemma eq_it_sqr1_x2 (e : int, z : zp) :
    0 <= e  =>
    it_sqr1_x2 e z = it_sqr_x2 e z.
proof.
    move : e.
    rewrite /it_sqr1_x2 /it_sqr_x2. elim. simplify. rewrite -iotaredE expr1 //. 
    move => i ige0 hin.
    rewrite iotaSr // -cats1 foldl_cat hin /= expE /=.  
    have ->: 4^i = 2^2^i. rewrite expr2 //.
    rewrite -exprM. smt(gt0_pow2).
    congr. clear hin.
    rewrite exprS // mulzC //.
qed.

lemma eq_it_sqr_x2_4 (e : int, z : zp) :
    0 <= e  => e %% 2 = 0 => 
    it_sqr e z = it_sqr_x2 (e%/2) z.
proof.
    move => e1 e2.
    rewrite /it_sqr /it_sqr_x2.
    congr. 
    have ->: 4 ^ (e %/ 2) = 2 ^ 2 ^ (e %/ 2). rewrite expr2 => />.
    rewrite -exprM => />. smt().
qed.

lemma eq_it_sqr1_x2_4 (e : int, z : zp) :
    0 <= e  => e %% 2 = 0 => 
    it_sqr1 e z = it_sqr1_x2 (e%/2) z.
proof.
    move => H H0.
    rewrite eq_it_sqr1 // eq_it_sqr1_x2. smt().
    apply eq_it_sqr_x2_4; trivial.
qed.

op invert1(z1 : zp) : zp =
    let t0 = sqr z1  in        (* z1^2  *)
    let t1 = sqr t0  in        (* z1^4  *)
    let t1 = sqr t1  in        (* z1^8  *)
    let t1 = Zp_25519.( * ) z1 t1 in        (* z1^9  *)
    let t0 = Zp_25519.( * ) t0 t1 in        (* z1^11 *)
    let t2 = sqr t0  in        (* z1^22 *)
    let t1 = Zp_25519.( * ) t1 t2 in        (* z_5_0  *)
    let t2 = sqr t1  in        (* z_10_5 *) 
    let t2 = it_sqr 4 t2  in
    let t1 = Zp_25519.( * ) t1 t2 in        (* z_10_0 *)
    let t2 = it_sqr 10 t1 in   (* z_20_10 *)
    let t2 = Zp_25519.( * ) t1 t2 in        (* z_20_0 *)
    let t3 = it_sqr 20 t2 in   (* z_40_20 *)
    let t2 = Zp_25519.( * ) t2 t3 in        (* z_40_0 *)
    let t2 = it_sqr 10 t2 in   (* z_50_10 *)
    let t1 = Zp_25519.( * ) t1 t2 in        (* z_50_0 *)
    let t2 = it_sqr 50 t1 in   (* z_100_50 *)
    let t2 = Zp_25519.( * ) t1 t2 in        (* z_100_0 *)
    let t3 = it_sqr 100 t2 in  (* z_200_100 *)
    let t2 = Zp_25519.( * ) t2 t3 in        (* z_200_0 *)
    let t2 = it_sqr 50 t2 in   (* z_250_50 *)
    let t1 = Zp_25519.( * ) t1 t2 in        (* z_250_0 *)
    let t1 = it_sqr 4 t1 in    (* z_255_5 *) 
    let t1 = sqr t1 in
    let t1 = Zp_25519.( * ) t0 t1 in
        t1 axiomatized by invert1E.

lemma eq_invert1 (z1: zp) :
    invert1 z1 = invert0 z1.
proof.
    rewrite invert1E invert0E /= /it_sqr /sqr /=.
    smt(exprS exprD expE).
qed.

(** split invert2 in 3 parts : jump from it_sqr to it_sqr1 **)

op invert2(z1 : zp) : zp =
    let t0 = sqr z1  in        (* z1^2  *)
    let t1 = sqr t0  in        (* z1^4  *)
    let t1 = sqr t1  in        (* z1^8  *)
    let t1 =  Zp_25519.( * ) z1 t1 in        (* z1^9  *)
    let t0 =  Zp_25519.( * ) t0 t1 in        (* z1^11 *)
    let t2 = sqr t0  in        (* z1^22 *)
    let t1 =  Zp_25519.( * ) t1 t2 in        (* z_5_0  *)
    let t2 = sqr t1  in        (* z_10_5 *) 
    let t2 = it_sqr1 4 t2  in
    let t1 =  Zp_25519.( * ) t1 t2 in        (* z_10_0 *)
    let t2 = it_sqr1 10 t1 in  (* z_20_10 *)
    let t2 =  Zp_25519.( * ) t1 t2 in        (* z_20_0 *)
    let t3 = it_sqr1 20 t2 in  (* z_40_20 *)
    let t2 =  Zp_25519.( * ) t2 t3 in        (* z_40_0 *)
    let t2 = it_sqr1 10 t2 in  (* z_50_10 *)
    let t1 =  Zp_25519.( * ) t1 t2 in        (* z_50_0 *)
    let t2 = it_sqr1 50 t1 in  (* z_100_50 *)
    let t2 =  Zp_25519.( * ) t1 t2 in        (* z_100_0 *)
    let t3 = it_sqr1 100 t2 in (* z_200_100 *)
    let t2 =  Zp_25519.( * ) t2 t3 in        (* z_200_0 *)
    let t2 = it_sqr1 50 t2 in  (* z_250_50 *)
    let t1 =  Zp_25519.( * ) t1 t2 in        (* z_250_0 *)
    let t1 = it_sqr1 4 t1 in   (* z_255_5 *) 
    let t1 = sqr t1 in
    let t1 =  Zp_25519.( * ) t0 t1 in
        t1 axiomatized by invert2E.

lemma eq_invert2 (z1: zp) :
    invert2 z1 = invert1 z1.
proof.
    rewrite invert2E invert1E. smt(eq_it_sqr1).
qed.

lemma eq_invert210p (z1: zp) :
    invert2 z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite eq_invert2 eq_invert1 eq_invert0p //.
qed.

(* now we define an alternative version of encodePoint *)
op encodePoint1 (q: zp * zp) : W256.t =
    let qi = invert2 q.`2 in
    let q =  Zp_25519.( * ) q.`1 qi in
        W256.of_int (asint q) axiomatized by encodePoint1E.

lemma eq_encodePoint1 (q: zp * zp) :
    encodePoint1 q = encodePoint q.
proof.
    rewrite encodePoint1E encodePointE. simplify. congr.
    rewrite eq_invert210p //.
qed.

(** step 6: scalarmult with updated montgomery_ladder3 **)

op scalarmult_internal1(u: zp) (k:W256.t) : W256.t =
    let r = montgomery_ladder3 u  k in
        encodePoint1 (r.`1) axiomatized by scalarmult_internal1E.

(* lemma scalarmult = scalarmult1 *)
lemma eq_scalarmult_internal1 (u:zp) (k:W256.t) :
    k.[0] = false => scalarmult_internal1 u k = scalarmult_internal u k.
proof.
    rewrite /scalarmult_internal1. simplify.
    rewrite eq_encodePoint1 /scalarmult_internal.
    simplify. move => H. 
    congr.
    have ml123 : montgomery_ladder u k = select_tuple_12 (montgomery_ladder3 u k).
        apply eq_montgomery_ladder123. apply H.
    rewrite ml123 /select_tuple_12 //.
qed.

hint simplify scalarmult_internal1E.

op scalarmult1 (k:W256.t) (u:W256.t) : W256.t =
    let k = decodeScalar25519 k in
    let u = decodeUCoordinate u in
    scalarmult_internal1 u k axiomatized by scalarmult1E.
 
hint simplify scalarmult1E.

op scalarmult_base1(k:W256.t) : W256.t =
    scalarmult1 (k) (W256.of_int(9%Int)).

(* lemma scalarmult = scalarmult1 *)
lemma eq_scalarmult1 (k:W256.t) (u:W256.t) :
    scalarmult1 k u = scalarmult k u.
proof.
    simplify.
    pose du := decodeUCoordinate u.
    pose dk := decodeScalar25519 k.
    rewrite eq_encodePoint1 /scalarmult_internal. simplify.
    congr.
    have kb0f  : (dk).[0] = false. (* k bit 0 false *)
        rewrite /dk /decodeScalar25519 //.
    have ml123 : montgomery_ladder du dk = select_tuple_12 (montgomery_ladder3 du dk).
        move : kb0f. apply eq_montgomery_ladder123.
    rewrite ml123 /select_tuple_12 //.
qed.

lemma eq_scalarmult_base1 (k:W256.t) :
    scalarmult_base1 k = scalarmult_base k.
proof.
    apply eq_scalarmult1.
qed.


