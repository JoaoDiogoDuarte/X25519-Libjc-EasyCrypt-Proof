require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Zp_25519 Ring EClib Distr.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_ref4.
require import Curve25519_auto.
import Zp_25519.
import Curve25519_Spec Curve25519_auto Curve25519_Hop1 Curve25519_Hop2 Curve25519_ref4 Array4 Array32 StdOrder.IntOrder.



(** init **)

equiv eq_h4_init_points :
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
rewrite /H6  /H0 /H3 /H2 /Zp_25519.zero /set0_64_ /inzpRep4 // /valRep4 /to_list /mkseq -iotaredE  => />.
qed. 

equiv eq_h4_decode_u_coordinate_base :
  MHop2.decode_u_coordinate_base ~ M.__decode_u_coordinate_base4:
  true ==> res{1} = inzpRep4 res{2}.
proof.
proc. wp. skip. move => &1 &2 H.
rewrite /inzpRep4. congr. rewrite /valRep4 /to_list /mkseq -iotaredE => />.
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
    split;  auto => />. rewrite /H14 /H13. 
    rewrite /b2i. 
    case: (swapped{1} ^^ H10).
    move => *. smt(@W64). 
    move => *. smt(@W64). 
qed.   

(** step 7 : montgomery_ladder **)
equiv eq_h4_montgomery_ladder :
  MHop2.montgomery_ladder ~ M.__montgomery_ladder4 :
   init'{1} = inzpRep4 u{2} /\
    inzp (W256.to_uint k'{1}) =  inzpRep32 k{2}
   ==>
   res{1}.`1 = inzpRep4 res{2}.`1 /\
   res{1}.`2 =inzpRep4  res{2}.`2.
proof.
    proc. wp. sp. 
    unroll {1} 4. 
    rcondt {1} 4. progress. inline MHop2.init_points.
    wp. sp. skip. progress.
    while(
          inzp (to_uint k'{1}) = inzpRep32 k{2}             /\ 
          ctr{1} = to_uint ctr{2}                          /\ 
          inzp (to_uint k'{1}) = inzpRep32 k{2}            /\
          init'{1} = inzpRep4 us{2}                        /\ 
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
    wp. sp. call eq_h4_montgomery_ladder_step. skip. progress.
    rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
    rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
    rewrite to_uint1 to_uint0. trivial. smt(@W64).  
    call eq_h4_montgomery_ladder_step. wp. call eq_h4_init_points. skip. done.
qed.

 (** step 8 : iterated square, may be error in variable names, ened to chec  **)
(** step 8 : iterated square **)
equiv eq_h4_it_sqr :
 MHop2.it_sqr ~ M._it_sqr4_p:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   2               <=   to_uint i{2}  /\
   i{1}            <=   W32.modulus   /\
   0              <=   i{1}   ==>
   res{1} = inzpRep4 res{2}.
proof.
proc. simplify. wp. sp.
  while (h{1}            =    inzpRep4 x{2}            /\ 
         ii{1}            =    to_uint i{2}             /\
         ii{1}            <=   W32.modulus              /\
         0                <=   ii{1}                     
).
   wp. call eq_h4_sqr_p. conseq(_: _ ==> h{1} = inzpRep4 x{2}).
   progress. rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
   smt(@W32). smt().  smt(@W32). 
   rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. smt(@W32).
   rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. smt(@W32).
   skip. progress. wp. 
   call eq_h4_sqr_p.  
   skip. progress.
   rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. smt(@W32). smt(). smt(@W32).
   rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. smt(@W32). smt().
qed.

equiv eq_h4_it_sqr_s :
 MHop2.it_sqr ~ M._it_sqr4_s_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   2               <=   to_uint i{2}  /\
   i{1}            <=   W32.modulus   /\
    2              <=   i{1}   ==>
   res{1} = inzpRep4 res{2}.
proof.
 proc. simplify. wp. sp.
admit.
qed.

equiv eq_h4_it_sqr_ss :
 MHop2.it_sqr ~ M._it_sqr4_ss_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    W32.to_uint i{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
 proc. wp. sp. inline M._it_sqr4_p. sp. wp. admit.
qed.

(** step 9 : invert **)
equiv eq_h4_invert :
  MHop2.invert ~ M.__invert4 : 
     fs{1} = inzpRep4 fs{2}
  ==> res{1} = inzpRep4 res{2}.
proof.
  proc.
  sp.
  call eq_h4_mul_ss.
  call eq_h4_sqr_s_.
  call (eq_h4_it_sqr_s). wp.
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
  skip. done.
qed.



(** step 11 : scalarmult **)

equiv eq_h4_scalarmult_internal :
  MHop2.scalarmult_internal ~ M.__curve25519_internal_ref4:
  inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\  u''{1} = inzpRep4 u{2}
  ==>
  inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
proc.
call eq_h4_encode_point.
call eq_h4_montgomery_ladder. wp. skip.
done.
qed.

equiv eq_h4_scalarmult :
  MHop2.scalarmult ~ M._curve25519_ref4:
  inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} /\  inzp (to_uint u'{1}) = inzpRep4 _u{2}
  ==>
  inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
proc.
call eq_h4_scalarmult_internal => />.
call eq_h4_decode_u_coordinate => />.
call eq_h4_decode_scalar_25519.
wp. skip. progress.
qed.


equiv eq_h4_scalarmult_ptr : (* how to get address *)
  MHop2.scalarmult ~ M.__curve25519_ref4_ptr:
  true ==> true.
proof.
admit.
qed.


equiv eq_h4_scalarmult_base :
  MHop2.scalarmult_base ~ M._curve25519_ref4_base:
  inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} ==>  inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
proc.
call eq_h4_scalarmult_internal => />.
call eq_h4_decode_u_coordinate_base => />.
call eq_h4_decode_scalar_25519.
wp. skip. progress.
qed.

equiv eq_h4_scalarmult_base_ptr :
  MHop2.scalarmult_base ~ M.__curve25519_ref4_base_ptr:
  true ==> true.
proof.
admit.
qed.


equiv eq_h4_scalarmult_jade :
  MHop2.scalarmult ~ M.jade_scalarmult_curve25519_amd64_ref4:
  true
  ==>
  true.
admit.
qed.

equiv eq_h4_scalarmult_jade_base :
  MHop2.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_ref4_base:
  true ==> true.
proof.
admit.
qed.
