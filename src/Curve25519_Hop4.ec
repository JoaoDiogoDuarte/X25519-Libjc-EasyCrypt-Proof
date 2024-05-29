require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Zp_25519 Ring EClib Distr.
from Jasmin require import JModel JWord_array.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_ref4.
import Zp_25519 ZModpRing.
import Curve25519_Spec Curve25519_Hop1 Curve25519_Hop2 Curve25519_ref4 Array4 Array32 StdOrder.IntOrder.
require import W64limbs.



(** representation : move to another file/use rep3/5 **)
type Rep4 = W64.t Array4.t.
type Rep32 = W8.t Array32.t.


op valRep4  (x : Rep4) : int = val_limbs64 (Array4.to_list x).
op valRep4List  (x : W64.t list) : int = val_limbs64(x).
op inzpRep4 (x : Rep4) : zp  = inzp (valRep4 x) axiomatized by inzpRep4E.
op inzpRep4List (x: W64.t list) : zp = inzp (valRep4List x) axiomatized by inzpRep4ListE.
abbrev zpcgrRep4 (x : Rep4) (z : int) : bool = zpcgr (valRep4 x) z.

op valRep32  (x : Rep32) : int = val_limbs8 (Array32.to_list x).
op inzpRep32 (x : Rep32) : zp  = inzp (valRep32 x) axiomatized by inzpRep32E.
(** ************************************* **)

(** step 0 : add sub mul sqr **)

equiv eq_h4_add : MHop2.add ~ M.__add4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.   
 admit.
qed.

equiv eq_h4_sub : MHop2.sub ~ M.__sub4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_a24 : MHop2.mul_a24 ~ M.__mul4_a24_rs:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
 admit.
qed.

equiv eq_h4_mul_rss : MHop2.mul ~ M.__mul4_rss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr : MHop2.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
admit.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_h4_add_ssr : MHop2.add ~ M.__add4_ssr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_add_sss : MHop2.add ~ M.__add4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_add_rrs : MHop2.add ~ M.__add4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_sub_ssr : MHop2.sub ~ M.__sub4_ssr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sub_rsr : MHop2.sub ~ M.__sub4_rsr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sub_sss : MHop2.sub ~ M.__sub4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_a24_ss : MHop2.mul_a24 ~ M.__mul4_a24_ss:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_sss : MHop2.mul ~ M.__mul4_sss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_pp : MHop2.mul ~ M._mul4_pp:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_mul_ss : MHop2.mul ~ M._mul4_ss_:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_sqr_rs : MHop2.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_ss : MHop2.sqr ~ M._sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_ss_ : MHop2.sqr ~ M.__sqr4_ss:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_s_ : MHop2.sqr ~ M._sqr4_s_:
    f{1} = inzpRep4 x{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_p : MHop2.sqr ~ M._sqr4_p:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

(** init **)

equiv eq_init_point4 :
    MHop2.init_points ~ M.__init_points4 : 
init{1} = inzpRep4 initr{2}
==> 
res{1}.`1 = inzpRep4 res{2}.`1 /\
res{1}.`2 = inzpRep4 res{2}.`2 /\
res{1}.`3 = inzpRep4 res{2}.`3 /\
res{1}.`4 = inzpRep4 res{2}.`4.
proof.
proc. 
wp. unroll for{2} ^while. wp. skip. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
split; auto => />. rewrite /H4 /H0 /H2 /H3 /Zp_25519.one /set0_64_ /inzpRep4 => />.
rewrite /valRep4 /to_list /mkseq -iotaredE => />.
split; auto => />. rewrite /H5  /H0 /H3 /H2 /Zp_25519.zero /set0_64_ /inzpRep4 => />.
rewrite /valRep4 /to_list /mkseq -iotaredE  => />.
rewrite /H6  /H0 /H3 /H2 /Zp_25519.zero /set0_64_ /inzpRep4 //  /valRep4 /to_list /mkseq -iotaredE  => />.
qed. 

(** step 1 : decode_scalar_25519 **)
 equiv eq_h4_decode_scalar_25519 :
  MHop2.decode_scalar ~ M.__decode_scalar:
  inzp(W256.to_uint(k'{1})) = inzpRep4 k{2}
  ==> 
  W32u8.to_list res{1} = to_list res{2}. 
proof.
admit. (* HELP No idea how to prove these "bit manipulation tricks" in easycrypt *)
qed.


(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate :
  MHop2.decode_u_coordinate ~ M.__decode_u_coordinate4:
  inzp(W256.to_uint  u'{1}) = inzpRep4 u{2}
  ==> 
  res{1} = inzpRep4 res{2}.
proof.
 proc. wp. skip.
 move => &1 &2 H0. rewrite H0.
 congr. 
admit. (* HELP This seems false...? *)
qed.

equiv eq_h4_decode_u_coordinate_base :
  MHop2.decode_u_coordinate_base ~ M.__decode_u_coordinate_base4:
  true ==> res{1} = inzpRep4 res{2}.
proof.
proc. wp. skip. move => &1 &2 H.
rewrite /inzpRep4. congr. rewrite /valRep4 /to_list /mkseq -iotaredE => />.
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit :
  MHop2.ith_bit ~ M.__ith_bit :
  inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  (ctr{1} = to_uint ctr{2}) ==> b2i res{1} = to_uint res{2}.
proof.
proc.
admit. (* HELP No idea how to prove these "bit manipulation tricks" in easycrypt *)
qed.


(** step 4 : cswap **)
equiv eq_h4_cswap :
  MHop2.cswap ~ M.__cswap4:
  x2{1}         = inzpRep4 x2{2}  /\
  z2{1}         = inzpRep4 z2r{2} /\
  x3{1}         = inzpRep4 x3{2}  /\
  z3{1}         = inzpRep4 z3{2}  /\
  b2i toswap{1} = to_uint toswap{2}
  ==>
  res{1}.`1     = inzpRep4 res{2}.`1  /\
  res{1}.`2     = inzpRep4 res{2}.`2  /\
  res{1}.`3     = inzpRep4 res{2}.`3  /\
  res{1}.`4     = inzpRep4 res{2}.`4.
proof.
proc.
do 4! unroll for{2} ^while.
case: (toswap{1}).
  rcondt {1} 1 => //. wp => /=. skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64_ /=. smt(@W64).
    rewrite !mask_set /=.
    have lxor1 : forall (x1 x2:W64.t),  x1 `^` (x2 `^` x1) = x2.
      move=> *. rewrite xorwC -xorwA xorwK xorw0 //.
    have lxor2 : forall (x1 x2:W64.t),  x1 `^` (x1 `^` x2) = x2.
      move=> *. rewrite xorwA xorwK xor0w //. 
  rewrite !lxor1 !lxor2.
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
             congr. apply Array4.ext_eq. smt(@Array4).
  rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. smt(@W64).
    rewrite !mask_not_set !andw0 !xorw0.
    smt(@Array4).
qed.

(** step 5 : add_and_double **)
equiv eq_h4_add_and_double :
  MHop2.add_and_double ~ M.__add_and_double4:
  init{1} = inzpRep4 init{2} /\
  x2{1}   = inzpRep4 x2{2}   /\
  z2{1}   = inzpRep4 z2r{2}  /\
  x3{1}   = inzpRep4 x3{2}   /\
  z3{1}   = inzpRep4 z3{2}
  ==>
  res{1}.`1 = inzpRep4 res{2}.`1 /\
  res{1}.`2 = inzpRep4 res{2}.`2 /\
  res{1}.`3 = inzpRep4 res{2}.`3 /\
  res{1}.`4 = inzpRep4 res{2}.`4.
proof.
proc => /=.
  call eq_h4_mul_rss.
  call eq_h4_mul_sss.
  call eq_h4_add_sss.
  call eq_h4_sqr_ss_.
  call eq_h4_mul_a24_ss.
  call eq_h4_sqr_ss_.
  call eq_h4_sub_sss.
  call eq_h4_mul_sss.
  call eq_h4_sub_sss.
  call eq_h4_add_sss.
  call eq_h4_sqr_ss_.
  call eq_h4_sqr_ss_.
  call eq_h4_mul_sss.
  call eq_h4_mul_sss.
  call eq_h4_add_sss.
  call eq_h4_sub_sss.
  call eq_h4_add_ssr.
  call eq_h4_sub_ssr.
  wp. done.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_h4_montgomery_ladder_step :
 MHop2.montgomery_ladder_step ~ M.__montgomery_ladder_step4:
   inzp (to_uint k'{1}) =   inzpRep32 k{2} /\
   init'{1} = inzpRep4 init{2} /\
   x2{1} = inzpRep4 x2{2} /\
   z2{1} = inzpRep4 z2r{2} /\
   x3{1} = inzpRep4 x3{2} /\
   z3{1} = inzpRep4 z3{2} /\ 
   b2i swapped{1} = to_uint swapped{2} /\
   ctr'{1} = to_uint ctr{2}
   ==>
   res{1}.`1 = inzpRep4 res{2}.`1 /\
   res{1}.`2 = inzpRep4 res{2}.`2 /\
   res{1}.`3 = inzpRep4 res{2}.`3 /\
   res{1}.`4 = inzpRep4 res{2}.`4 /\
   b2i res{1}.`5 = to_uint res{2}.`5.
proof.
proc => /=. 
call eq_h4_add_and_double. wp.
call eq_h4_cswap. wp.
call eq_h4_ith_bit. skip. 
move => &1 &2 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.   
auto => />. rewrite H0. 
move => [H8 H9] H10 H11 H12 H13 H14. 
split;  auto => />.  rewrite /H14 /H13. 
rewrite /b2i. 
case: (swapped{1} ^^ H10).
move => *. smt(@W64). 
move => *. smt(@W64). 
qed.   

(** step 7 : montgomery_ladder **)
equiv eq_h4_montgomery_ladder :
  MHop2.montgomery_ladder ~ M.__montgomery_ladder4 :
   init'{1} = inzpRep4 u{2} /\
   to_list (W32u8.unpack8 k'{1}) = Array32.to_list k{2}
   ==>
   res{1}.`1 = inzpRep4 res{2}.`1 /\
   res{1}.`2 =inzpRep4  res{2}.`2.
proof.
proc. sp.
(*while((to_uint ctr = 0 \/ to_uint ctr = 1 \/ to_uint ctr = W64.max_int) /\
      (to_uint ctr = 1 => valores à entrada) /\ (to_uint ctr = 0 => valores a meio) /\
      (to_uint ctr = W64.max_int => valores à saida))
*)
 admit.

qed.

 (** step 8 : iterated square, may be error in variable names, ened to chec  **)
equiv eq_h4_it_sqr :
 MHop2.it_sqr ~ M._it_sqr4_p:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    W32.to_uint i{2}  
   ==>
   res{1} = inzpRep4 res{2}.
proof.
proc. sp. wp. progress. admit.
qed.

equiv eq_h4_it_sqr_s :
 MHop2.it_sqr ~ M._it_sqr4_s_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    W32.to_uint i{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
admit.
qed.

equiv eq_h4_it_sqr_ss :
 MHop2.it_sqr ~ M._it_sqr4_ss_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    W32.to_uint i{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
admit.
qed.

(** step 9 : invert **)
equiv eq_h4_invert :
  MHop2.invert ~ M.__invert4 : 
     z1'{1} = inzpRep4 fs{2}
  ==> res{1} = inzpRep4 res{2}.
proof.
  proc => /=.
  sp.
  call eq_h4_mul_ss.
  call eq_h4_sqr_s_.
  call eq_h4_it_sqr_s. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_s. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_ss. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_ss. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_s. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_ss. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_ss. wp.
  call eq_h4_mul_ss.
  call eq_h4_it_sqr_s. wp.
  call eq_h4_sqr_ss.
  call eq_h4_mul_ss.
  call eq_h4_sqr_ss.
  call eq_h4_mul_ss.
  call eq_h4_mul_ss.
  call eq_h4_sqr_s_.
  call eq_h4_sqr_ss.
  call eq_h4_sqr_ss. wp. 
  admit.
qed.


(** step 10 : encode point **)
equiv eq_h4_encode_point : 
  MHop2.encode_point ~ M.__encode_point4:
  x2{1} = inzpRep4 x2{2} /\ 
  z2{1} = inzpRep4 z2r{2}
  ==>
  inzp (to_uint res{1}) =  inzpRep4 res{2}.
proof.
  proc. inline M.__tobytes4. wp. 
  call eq_h4_mul_rss. 
  call eq_h4_invert.
  wp. skip. move => &1 &2 [H] H0. split. auto => />. 
  move => H1 H2 H3 H4. split. split. auto => />. auto => />.  
admit. (* HELP I do not know how to prove bit tricks like these in easycrypt *)
qed.

(** step 11 : scalarmult **)

equiv eq_h4_scalarmult_internal :
  MHop2.scalarmult_internal ~ M.__curve25519_internal_ref4:
  true ==> true.
proof.
proc.
call eq_h4_encode_point.
call eq_h4_montgomery_ladder. wp. skip.
move => *. split. split. progress.
admit.
qed.

equiv eq_h4_scalarmult :
  MHop2.scalarmult ~ M._curve25519_ref4:
  true ==> true.
proof.
proc.
admit.
qed.


equiv eq_h4_scalarmult_ptr :
  MHop2.scalarmult ~ M.__curve25519_ref4_ptr:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_base :
  MHop2.scalarmult_base ~ M._curve25519_ref4_base:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_base_ptr :
  MHop2.scalarmult_base ~ M.__curve25519_ref4_base_ptr:
  true ==> true.
proof.
admit.
qed.


equiv eq_h4_scalarmult_jade :
  MHop2.scalarmult ~ M.jade_scalarmult_curve25519_amd64_ref4:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_jade_base :
  MHop2.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_ref4_base:
  true ==> true.
proof.
admit.
qed.
it_
