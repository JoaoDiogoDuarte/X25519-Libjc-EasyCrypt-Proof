require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Zp_25519 Ring EClib Distr.
from Jasmin require import JModel JMemory JWord.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_Ref5.
require import Curve25519_auto5.
require import W64limbs.
import Zp_25519.
import Curve25519_Spec Curve25519_auto5 Curve25519_Hop1 Curve25519_Hop2 Curve25519_Ref5 Array4 Array5 Array8 Array32 StdOrder.IntOrder.


(* additions, substractions and powers *)

equiv eq_h4_sqr_ss__ref5 : MHop2.sqr ~ M_ref5._sqr5_ss_:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc *. inline {2} (1). unroll for{2} ^while. wp. sp.
    call eq_h4_sqr_p_ref5. skip. auto => />. move => &2.
    congr. apply Array5.ext_eq. smt(@Array5).
qed.


equiv eq_h4_sqr_s_ref5 : MHop2.sqr ~ M_ref5._sqr5_s_:
    f{1}   = inzpRep5 x{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc *.  inline {2 }(1). wp. sp.
    call eq_h4_sqr_p_ref5. skip. auto => />. 
qed.

equiv eq_h4_mul_ss_ref5 : MHop2.mul ~ M_ref5._mul5_ss_:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc *.  inline {2 }(1). wp. sp.
    call eq_h4_mul_pp_ref5. skip. auto => />. 
qed.


equiv eq_h4_sqr_ss_ref5 : MHop2.sqr ~ M_ref5.__sqr5_ss:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc *.  inline {2 }(1). wp. sp.
    call eq_h4_sqr_rs_ref5. skip. auto => />.  
qed.


equiv eq_h4_mul_sss_ref5 : MHop2.mul ~ M_ref5.__mul5_sss:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc *. inline {2 }(1). wp. sp.
    call eq_h4_mul_rss_ref5. skip. auto => />. 
qed.


equiv eq_h4_sub_ssr_ref5 : MHop2.sub ~ M_ref5.__sub5_ssr:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 g{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc *.  inline {2 }(1). wp. sp.
    call eq_h4_sub_rsr_ref5. skip. auto => />. 
qed.


equiv eq_h4_sub_sss_ref5 : MHop2.sub ~ M_ref5.__sub5_sss:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 gs{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc *. inline {2 }(1). wp. sp.
    call eq_h4_sub_rss_ref5. skip. auto => />. 
qed.

(** step 1: init points and decoding u-coordinates **)
equiv eq_h4_init_points_ref5 :
    MHop2.init_points ~ M_ref5.__init_points5 : 
        init{1} = inzpRep5 initr{2}
        ==> 
        res{1}.`1 = inzpRep5 res{2}.`1 /\
        res{1}.`2 = inzpRep5 res{2}.`2 /\
        res{1}.`3 = inzpRep5 res{2}.`3 /\
        res{1}.`4 = inzpRep5 res{2}.`4.
proof.
    proc. 
    wp. unroll for{2} ^while. wp. skip. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    split; auto => />. rewrite /H4 /H0 /H2 /H3 /Zp_25519.one /set0_64_ /inzpRep5 => />.
        rewrite /valRep5 /to_list /mkseq -iotaredE => />.
    split; auto => />. rewrite /H5  /H0 /H3 /H2 /Zp_25519.zero /set0_64_ /inzpRep5 => />.
        rewrite /valRep5 /to_list /mkseq -iotaredE  => />.
    rewrite /H6  /H0 /H3 /H2 /Zp_25519.zero /set0_64_ /inzpRep5 // /valRep5 /to_list /mkseq -iotaredE  => />.
qed. 

equiv eq_h4_decode_u_coordinate_base5 :
    MHop2.decode_u_coordinate_base ~ M_ref5.__decode_u_coordinate_base5:
        true 
        ==> 
        res{1} = inzpRep5 res{2}.
proof.
    proc. wp. skip. move => &1 &2 H.
    rewrite /inzpRep5. congr. rewrite /valRep5 /to_list /mkseq -iotaredE => />.
qed.


(** step 4 : cswap **)
equiv eq_h4_cswap_ref5 :

    MHop2.cswap ~ M_ref5.__cswap5:
        x2{1}         = inzpRep5 x2{2}      /\
        z2{1}         = inzpRep5 z2r{2}     /\
        x3{1}         = inzpRep5 x3{2}      /\
        z3{1}         = inzpRep5 z3{2}      /\
        b2i toswap{1} = to_uint toswap{2}
        ==>
        res{1}.`1     = inzpRep5 res{2}.`1  /\
        res{1}.`2     = inzpRep5 res{2}.`2  /\
        res{1}.`3     = inzpRep5 res{2}.`3  /\
        res{1}.`4     = inzpRep5 res{2}.`4.
proof.
    proc.
    do 3! unroll for{2} ^while.
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
        split. congr. apply Array5.ext_eq. smt(@Array5).
        split. congr. apply Array5.ext_eq. smt(@Array5).
        split. congr. apply Array5.ext_eq. smt(@Array5).
        congr. apply Array5.ext_eq. smt(@Array5).
    rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. smt(@W64).
    rewrite !mask_not_set !andw0 !xorw0.
    smt(@Array5).
qed.

axiom test (x y z: W64.t, k : W8.t) : (x * y `>>` k = x * z) = (y `>>` k = z).
axiom test0 (x y z: W64.t, k: int) : (x * y `>>>` k = x * z) = (y `>>>` k = z).

(** step 5 : add_and_double **)
equiv eq_h4_add_and_double_ref5 :
    MHop2.add_and_double ~ M_ref5.__add_and_double5:
        init{1} = inzpRep5 init{2}     /\
        x2{1}   = inzpRep5 x2{2}       /\
        z2{1}   = inzpRep5 z2r{2}      /\
        x3{1}   = inzpRep5 x3{2}       /\
        z3{1}   = inzpRep5 z3{2}
        ==>
        res{1}.`1 = inzpRep5 res{2}.`1 /\
        res{1}.`2 = inzpRep5 res{2}.`2 /\
        res{1}.`3 = inzpRep5 res{2}.`3 /\
        res{1}.`4 = inzpRep5 res{2}.`4.
proof.
    proc => /=. sp.
    swap{1} 16 -1.
    call eq_h4_mul_rss_ref5.
    call eq_h4_mul_sss_ref5.
    call eq_h4_sqr_ss_ref5.
    auto => />.
    seq 13 13 : (t0{1} = inzpRep5 t0{2} /\ t2{1} = inzpRep5 t2{2} /\  x3{1} = inzpRep5 x3{2} /\ z2{1} = inzpRep5 z2{2}   /\ x2{1} = inzpRep5 x2{2}).
    
    
    call eq_h4_sqr_ss_ref5.
    call eq_h4_sub_sss_ref5.
    call eq_h4_mul_sss_ref5.
    call eq_h4_sub_sss_ref5.
    call eq_h4_add_sss_ref5.
    call eq_h4_sqr_ss_ref5.
    call eq_h4_sqr_ss_ref5.
    call eq_h4_mul_sss_ref5.
    call eq_h4_mul_sss_ref5.
    call eq_h4_add_sss_ref5.
    call eq_h4_sub_sss_ref5.
    call eq_h4_add_ssr_ref5.
    call eq_h4_sub_ssr_ref5. skip. done.
    conseq />.
    transitivity {1} {t2 <@ Aux_mul_a24.aux_mul_a24(t0, t2);}
    (t0{1} = t0{2} /\ t2{1} = t2{2} ==> t2{1} = t2{2})
    (t0{1} = inzpRep5 t0{2} /\ t2{1} = inzpRep5 t2{2} ==> t2{1} = inzpRep5 t2{2}). 
    smt(). smt(). inline {2} 1. sim. call eq_aux_mul_a24. auto => />. 
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_h4_montgomery_ladder_step_ref5 :
    MHop2.montgomery_ladder_step ~ M_ref5.__montgomery_ladder_step5:
        inzp (to_uint k'{1}) =   inzpRep32 k{2} /\
        init'{1} = inzpRep5 init{2}             /\
        x2{1} = inzpRep5 x2{2}                  /\
        z2{1} = inzpRep5 z2r{2}                 /\
        x3{1} = inzpRep5 x3{2}                  /\
        z3{1} = inzpRep5 z3{2}                  /\ 
        b2i swapped{1} = to_uint swapped{2}     /\
        ctr'{1} = to_uint ctr{2}
        ==>
        res{1}.`1 = inzpRep5 res{2}.`1          /\
        res{1}.`2 = inzpRep5 res{2}.`2          /\
        res{1}.`3 = inzpRep5 res{2}.`3          /\
        res{1}.`4 = inzpRep5 res{2}.`4          /\
        b2i res{1}.`5 = to_uint res{2}.`5.
proof.
    proc => /=. 
    call eq_h4_add_and_double_ref5. wp.
    call eq_h4_cswap_ref5. wp.
    call eq_h4_ith_bit_ref5. skip. 
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
equiv eq_h4_montgomery_ladder_ref5 :
    MHop2.montgomery_ladder ~ M_ref5.__montgomery_ladder5 :
        init'{1} = inzpRep5 u{2}                     /\
        inzp (W256.to_uint k'{1}) =  inzpRep32 k{2}
        ==>
        res{1}.`1 = inzpRep5 res{2}.`1               /\
        res{1}.`2 =inzpRep5  res{2}.`2.
proof.
    proc. wp. sp. 
    unroll {1} 4. 
    rcondt {1} 4. auto => />. inline MHop2.init_points.
        wp. sp. skip. auto => />.
    while(
          inzp (to_uint k'{1}) = inzpRep32 k{2}            /\ 
          ctr{1} = to_uint ctr{2}                          /\ 
          init'{1} = inzpRep5 us{2}                        /\ 
          x2{1} = inzpRep5 x2{2}                           /\
          x3{1} = inzpRep5 x3{2}                           /\
          z2{1} = inzpRep5 z2r{2}                          /\
          z3{1} = inzpRep5 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_h4_montgomery_ladder_step_ref5. skip. auto => />. 
        move => &1 &2 ctrR H H0 H1 H2. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        move => H3 H4 H5 H6 H7 H8 H9 H10. split.
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial. smt(@W64).  
    call eq_h4_montgomery_ladder_step_ref5. wp. call eq_h4_init_points_ref5. skip. done.
qed.

(** step 8 : iterated square **)
equiv eq_h4_it_sqr_ref5 :
    MHop2.it_sqr ~ M_ref5._it_sqr5_p:
        f{1}            =    inzpRep5 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep5 res{2}.
proof.
    proc. simplify. wp. sp.
    while (h{1}            =    inzpRep5 x{2}            /\ 
         ii{1}            =    to_uint i{2}              /\
         ii{1}            <=   W32.modulus               /\
         0                <=   ii{1}                     
    ).
    wp. call eq_h4_sqr_p_ref5. conseq(_: _ ==> h{1} = inzpRep5 x{2}).
    move => &1 &2 [[H][ H0] [H1] H2 [H3] H4 H5]. split. apply H5.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    move => H6 H7 H8 H9. split. split. apply H9. split.
    rewrite to_uintB. rewrite  uleE => />. by smt(). rewrite to_uint1 H0 //.
    split. move: H1. smt(). move: H2. smt(). split. rewrite H0. move => H10.
    smt(@W32). smt(@W32). skip. auto => />. wp.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. 
    call eq_h4_sqr_p_ref5.  
    skip. auto => />. move => &2 H H0. split. split.
    rewrite to_uintB. rewrite uleE => />. move: H. smt().
    rewrite to_uint1 //. split. move: H0. smt(). move: H. smt().
    split. move => H1. smt(@W32). move => H1. move: H. smt().
qed.

equiv eq_h4_it_sqr_s_ref5 :
    MHop2.it_sqr ~ M_ref5._it_sqr5_s_:
        f{1}            =    inzpRep5 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2              <=   i{1}   ==>
        res{1} = inzpRep5 res{2}.
proof.
    proc *. inline M_ref5._it_sqr5_s_. wp. sp. 
    call eq_h4_it_sqr_ref5. skip. auto => />.
qed.

equiv eq_h4_it_sqr_ss_ref5 :
        MHop2.it_sqr ~ M_ref5._it_sqr5_ss_: 
        f{1}            =    inzpRep5 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep5 res{2}.
proof.
    proc *. inline M_ref5._it_sqr5_ss_. 
    unroll for{2} ^while. wp. sp.
    call eq_h4_it_sqr_ref5. skip. auto => />. move => &2 H H0. congr. 
    apply Array5.ext_eq. move => H1 [H2] H3. smt(@Array5).
qed.

(** step 9 : invert **)
equiv eq_h4_invert_ref5 :
    MHop2.invert ~ M_ref5.__invert5 : 
        fs{1} = inzpRep5 fs{2}
        ==> 
        res{1} = inzpRep5 res{2}.
proof.
    proc.
    sp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_sqr_s_ref5.
    call (eq_h4_it_sqr_s_ref5). wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_s_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_ss_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_ss_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_s_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_ss_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_ss_ref5. wp.
    call eq_h4_mul_ss_ref5.
    call eq_h4_it_sqr_s_ref5. wp.
    call eq_h4_sqr_ss__ref5.
    call eq_h4_mul_ss_ref5.
    call eq_h4_sqr_ss__ref5.
    call eq_h4_mul_ss_ref5.
    call eq_h4_mul_ss_ref5.
    call eq_h4_sqr_s_ref5.
    call eq_h4_sqr_ss__ref5.
    call eq_h4_sqr_ss__ref5. wp. 
    skip. done.
qed.


(** step 11 : scalarmult **)

equiv eq_h4_scalarmult_internal_ref5 :
    MHop2.scalarmult_internal ~ M_ref5.__curve25519_internal_ref5:
        inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\  
        u''{1} = inzpRep5 u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
    proc.
    call eq_h4_encode_point_ref5.
    call eq_h4_montgomery_ladder_ref5. wp. skip.
    done.
qed.

equiv eq_h4_scalarmult_ref5 :
    MHop2.scalarmult ~ M_ref5.__curve25519_ref5:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} /\  
        inzp (to_uint u'{1}) = inzpRep4 _u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2} /\
        inzpRep40List (W32u8.to_list res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_h4_scalarmult_internal_ref5 => />. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7. auto => />.
    rewrite -H7.
    rewrite /inzpRep40List /inzpRep5 /valRep40List. congr. 
    rewrite to_uint_unpack32u8. congr. congr. smt().
    call eq_h4_decode_u_coordinate_ref5 => />.
    call eq_h4_decode_scalar_25519_ref5 => />.
    move => &1 &2 [H] H0 H1. split. auto => />.
    move => H2 H3 H4 H5 H6. split. auto => />.
    move => H7 H8 H9 H10. rewrite -H10.
    rewrite /inzpRep40List /inzpRep5 /valRep40List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
    wp. skip. 
    auto => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    rewrite -H6.
    rewrite /inzpRep40List /inzpRep5 /valRep40List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
qed.

equiv eq_h4_scalarmult_base_ref5 :
    MHop2.scalarmult_base ~ M_ref5.__curve25519_ref5_base:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} 
        ==>  
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
    proc.
    call eq_h4_scalarmult_internal_ref5 => />.
    call eq_h4_decode_u_coordinate_base5 => />.
    call eq_h4_decode_scalar_25519_ref5.
    wp. skip. done.
qed.

lemma eq_h4_scalarmult_jade_ref5 mem _qp _np _pp:
    equiv [MHop2.scalarmult ~ M_ref5.jade_scalarmult_curve25519_amd64_ref5:
        valid_ptr (W64.to_uint _qp)  32                                                          /\ 
        valid_ptr (W64.to_uint _np)  32                                                          /\
        valid_ptr (W64.to_uint _pp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\ 
        np{2} = _np                                                                              /\
        pp{2} = _pp                                                                              /\ 
        inzp (W256.to_uint k'{1}) = inzpRep4List (load_array4 (Glob.mem{2}) (W64.to_uint np{2})) /\  
        inzp (to_uint u'{1})      = inzpRep4List (load_array4 (Glob.mem{2}) (W64.to_uint pp{2}))
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref5.jade_scalarmult_curve25519_amd64_ref5. 
    inline M_ref5.__load4 M_ref5.__store4. 
    do 3! unroll for{2} ^while. wp. sp.
    call eq_h4_scalarmult_ref5. skip. auto => />.
    move => &1 H H0 H1 H2 H3 H4 H5 H6. split. split.
    rewrite H5. rewrite /inzpRep4List /inzpRep4 /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />. split. 
    rewrite !to_uintD_small !to_uint_small. move: H2. auto => />. smt(). auto => />.
    trivial. split.     rewrite !to_uintD_small !to_uint_small. move: H2. auto => />. smt(). auto => />.
    trivial. rewrite !to_uintD_small !to_uint_small. move: H2. auto => />. smt(). auto => />.
    trivial. rewrite !to_uintD_small !to_uint_small. move: H2. auto => />. smt(). auto => />.
    trivial. smt(). trivial. smt(). trivial. smt(). smt().
    rewrite H6. rewrite /inzpRep4List /inzpRep4 /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />. 
    move => H7 H8 H9 H10 H11 H12. 
    rewrite H11. rewrite /inzpRep4List /inzpRep4 /valRep4List /valRep4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />. rewrite /load_array4 => />.
    split. 
    apply (load_store_pos mem _qp H10 0). rewrite /valid_ptr. split. trivial. apply H0. trivial. split.
    apply (load_store_pos mem _qp H10 8). rewrite /valid_ptr. split. trivial. apply H0. trivial. split.
    apply (load_store_pos mem _qp H10 16). rewrite /valid_ptr. split. trivial. apply H0. trivial.    
    apply (load_store_pos mem _qp H10 24). rewrite /valid_ptr. split. trivial. apply H0. trivial.   
qed.

lemma eq_h4_scalarmult_jade_base_ref5  mem _qp _np:
    equiv [MHop2.scalarmult_base ~ M_ref5.jade_scalarmult_curve25519_amd64_ref5_base:
        valid_ptr (W64.to_uint _qp)  32                                                          /\ 
        valid_ptr (W64.to_uint _np)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\ 
        np{2} = _np                                                                              /\
        inzp (W256.to_uint k'{1}) = inzpRep4List (load_array4 (Glob.mem{2}) (W64.to_uint np{2}))  
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref5.jade_scalarmult_curve25519_amd64_ref5_base. wp. sp.
    inline M_ref5.__load4 M_ref5.__store4. 
    do 2! unroll for{2} ^while. wp. sp.
    call eq_h4_scalarmult_base_ref5. skip. auto => />.
    move => &1 &2 H H0 H1 H2 H3. split. 
    rewrite H3. rewrite /inzpRep4List /inzpRep4 /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />.  split. 
    rewrite !to_uintD_small !to_uint_small => />. move: H2. smt(). split.
    rewrite !to_uintD_small !to_uint_small => />. move: H2. smt(). 
    rewrite !to_uintD_small !to_uint_small => />. move: H2. smt().
    move => H4 H5 H6 H7. 
    rewrite H7. rewrite /inzpRep4List /inzpRep4 /valRep4List /valRep4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />.  rewrite /load_array4 => />.
    split. 
    apply (load_store_pos Glob.mem{2} qp{2} H6 0). rewrite /valid_ptr. split. trivial. apply H0. trivial. 
    split.
    apply (load_store_pos Glob.mem{2} qp{2} H6 8). rewrite /valid_ptr. split. trivial. apply H0. trivial. 
    split.
    apply (load_store_pos Glob.mem{2} qp{2} H6 16). rewrite /valid_ptr. split. trivial. apply H0. trivial.    
    apply (load_store_pos Glob.mem{2} qp{2} H6 24). rewrite /valid_ptr. split. trivial. apply H0. trivial.   
qed.



