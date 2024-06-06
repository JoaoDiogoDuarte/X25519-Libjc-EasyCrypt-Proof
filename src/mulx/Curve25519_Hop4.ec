require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Zp_25519 Ring EClib Distr.
from Jasmin require import JModel JMemory JWord.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_Ref4.
require import Curve25519_auto_mulx.
require import W64limbs.
import Zp_25519.
import Curve25519_Spec Curve25519_auto_mulx Curve25519_Hop1 Curve25519_Hop2 Curve25519_mulx Array4 Array8 Array32 StdOrder.IntOrder.


(* Should be moved elsewhere *)

(** init **)

equiv eq_h4_init_points_mulx :
    MHop2.init_points ~ M_mulx.__init_points4 : 
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

equiv eq_h4_decode_u_coordinate_base_mulx :
    MHop2.decode_u_coordinate_base ~ M_mulx.__decode_u_coordinate_base4:
        true 
        ==> 
        res{1} = inzpRep4 res{2}.
proof.
    proc. wp. skip. move => &1 &2 H.
    rewrite /inzpRep4. congr. rewrite /valRep4 /to_list /mkseq -iotaredE => />.
qed.


(** step 4 : cswap **)
equiv eq_h4_cswap_mulx :
    MHop2.cswap ~ M_mulx.__cswap4:
        x2{1}         = inzpRep4 x2{2}      /\
        z2{1}         = inzpRep4 z2r{2}     /\
        x3{1}         = inzpRep4 x3{2}      /\
        z3{1}         = inzpRep4 z3{2}      /\
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
equiv eq_h4_add_and_double_mulx :
    MHop2.add_and_double ~ M_mulx.__add_and_double4:
        init{1} = inzpRep4 init{2}     /\
        x2{1}   = inzpRep4 x2{2}       /\
        z2{1}   = inzpRep4 z2r{2}      /\
        x3{1}   = inzpRep4 x3{2}       /\
        z3{1}   = inzpRep4 z3{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1 /\
        res{1}.`2 = inzpRep4 res{2}.`2 /\
        res{1}.`3 = inzpRep4 res{2}.`3 /\
        res{1}.`4 = inzpRep4 res{2}.`4.
proof.
    proc => /=.
    call eq_h4_mul_rss_mulx.
    call eq_h4_mul_sss_mulx.
    call eq_h4_add_sss_mulx.
    call eq_h4_sqr_ss_mulx.
    call eq_h4_mul_a24_ss_mulx.
    call eq_h4_sqr_ss_mulx.
    admit.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_h4_montgomery_ladder_step_mulx :
    MHop2.montgomery_ladder_step ~ M_mulx.__montgomery_ladder_step4:
        inzp (to_uint k'{1}) =   inzpRep32 k{2} /\
        init'{1} = inzpRep4 init{2}             /\
        x2{1} = inzpRep4 x2{2}                  /\
        z2{1} = inzpRep4 z2r{2}                 /\
        x3{1} = inzpRep4 x3{2}                  /\
        z3{1} = inzpRep4 z3{2}                  /\ 
        b2i swapped{1} = to_uint swapped{2}     /\
        ctr'{1} = to_uint ctr{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1          /\
        res{1}.`2 = inzpRep4 res{2}.`2          /\
        res{1}.`3 = inzpRep4 res{2}.`3          /\
        res{1}.`4 = inzpRep4 res{2}.`4          /\
        b2i res{1}.`5 = to_uint res{2}.`5.
proof.
    proc => /=. 
    call eq_h4_add_and_double_mulx. wp.
    call eq_h4_cswap_mulx. wp.
    call eq_h4_ith_bit_mulx. skip. 
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
equiv eq_h4_montgomery_ladder_mulx :
    MHop2.montgomery_ladder ~ M_mulx.__montgomery_ladder4 :
        init'{1} = inzpRep4 u{2}                     /\
        inzp (W256.to_uint k'{1}) =  inzpRep32 k{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1               /\
        res{1}.`2 =inzpRep4  res{2}.`2.
proof.
    proc. wp. sp. 
    unroll {1} 4. 
    rcondt {1} 4. auto => />. inline MHop2.init_points.
        wp. sp. skip. auto => />.
    while(
          inzp (to_uint k'{1}) = inzpRep32 k{2}            /\ 
          ctr{1} = to_uint ctr{2}                          /\ 
          init'{1} = inzpRep4 us{2}                        /\ 
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_h4_montgomery_ladder_step_mulx. skip. auto => />. 
        move => &1 &2 ctrR H H0 H1 H2. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        move => H3 H4 H5 H6 H7 H8 H9 H10. split.
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial. smt(@W64).  
    call eq_h4_montgomery_ladder_step_mulx. wp. call eq_h4_init_points_mulx. skip. done.
qed.

(** step 8 : iterated square **)
equiv eq_h4__it_sqr_x2_mulx :
    MHop2.it_sqr_x2 ~ M_mulx.__it_sqr4_x2:
         f{1}            =    inzpRep4 f{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc. simplify. wp. sp.
    while (h{1}            =    inzpRep4 h{2}            /\ 
         f{1}             = inzpRep4 f{2} /\
         ii{1}            =    to_uint i{2}              /\
         ii{1}            <=   W32.modulus               /\
         0                <=   ii{1}                     
    ).
    wp. sp. call eq_h4_sqr__rr_mulx.  call eq_h4_sqr__rr_mulx. 
    conseq(_: _ ==> f{1} = inzpRep4 f{2} /\  h{1} = inzpRep4 h{2}).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    move=> &1 &2 [H1 [[H2]] [H3] [H4] [H5] H6 [H7] H8 [H9] H10]. split. apply H9.
    move => H11 H12 H13 H14. split. apply H14. move => H15 H16 H17 H18.
    split. split. rewrite H14. trivial. split. apply H18. split.
    rewrite H1. rewrite to_uintB. rewrite  uleE => />. smt(). rewrite to_uint1 H4 //.
    split. move: H5. smt(). move: H7. smt(). split. move => H19.
    rewrite H1. smt(@W32). rewrite H1. smt(@W32).  
    skip. auto => />. 
    wp. call eq_h4_sqr__rr_mulx.  call eq_h4_sqr__rr_mulx. 
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. 
    auto => />. move => &2 H H0. split. split. 
    rewrite to_uintB. rewrite uleE => />. move: H. smt().
    rewrite to_uint1 //. split. move: H0. smt(). move: H. smt().
    split. move => H3. smt(@W32). move => H4. move: H. smt().    
qed.

equiv eq_h4_it_sqr_x2_mulx :
    MHop2.it_sqr_x2 ~ M_mulx._it_sqr4_x2:
        f{1}            =    inzpRep4 f{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2              <=   i{1}   ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx._it_sqr4_x2. wp. sp. 
    call eq_h4__it_sqr_x2_mulx. skip. auto => />.
qed.

equiv eq_h4_it_sqr_x2__mulx :
        MHop2.it_sqr_x2 ~ M_mulx._it_sqr4_x2_: 
        f{1}            =    inzpRep4 _f{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx._it_sqr4_x2_. 
    wp. sp. call eq_h4_it_sqr_x2_mulx. skip.
    auto => />.
qed.

(** step 9 : invert **)
equiv eq_h4_invert_mulx :
    MHop2.invert ~ M_mulx.__invert4 : 
        fs{1} = inzpRep4 f{2}
        ==> 
        res{1} = inzpRep4 res{2}.
proof.
    proc.
    sp.
    call eq_h4_mul_rsr__mulx.
    call eq_h4_sqr_rr_mulx.
    admit.
qed.


(** step 11 : scalarmult **)

equiv eq_h4_scalarmult_internal_mulx :
    MHop2.scalarmult_internal ~ M_mulx.__curve25519_internal_mulx:
        inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\  
        u''{1} = inzpRep4 u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
    proc.
    call eq_h4_encode_point_mulx.
    call eq_h4_montgomery_ladder_mulx. wp. skip.
    done.
qed.

equiv eq_h4_scalarmult_mulx :
    MHop2.scalarmult ~ M_mulx.__curve25519_mulx:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} /\  
        inzp (to_uint u'{1}) = inzpRep4 _u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2} /\
        inzpRep32List (W32u8.to_list res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_h4_scalarmult_internal_mulx => />. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7. auto => />.
    rewrite -H7.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr. 
    rewrite to_uint_unpack32u8. congr. congr. smt().
    call eq_h4_decode_u_coordinate_mulx => />.
    call eq_h4_decode_scalar_25519_mulx => />.
    move => &1 &2 [H] H0 H1. split. auto => />.
    move => H2 H3 H4 H5 H6. split. auto => />.
    move => H7 H8 H9 H10. rewrite -H10.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
    wp. skip. 
    auto => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    rewrite -H6.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
qed.

equiv eq_h4_scalarmult_base_mulx :
    MHop2.scalarmult_base ~ M_mulx.__curve25519_mulx_base:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} 
        ==>  
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
    proc.
    call eq_h4_scalarmult_internal_mulx => />.
    call eq_h4_decode_u_coordinate_base_mulx => />.
    call eq_h4_decode_scalar_25519_mulx.
    wp. skip. done.
qed.

lemma eq_h4_scalarmult_jade_mulx mem _qp _np _pp:
    equiv [MHop2.scalarmult ~ M_mulx.jade_scalarmult_curve25519_amd64_mulx:
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
    proc *. inline M_mulx.jade_scalarmult_curve25519_amd64_mulx. wp. sp.
    inline M_mulx.__load4 M_mulx.__store4. 
    do 3! unroll for{2} ^while. wp. sp.
    call eq_h4_scalarmult_mulx. skip. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6. split. split.
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
    apply (load_store_pos Glob.mem{2} qp{2} H10 0). rewrite /valid_ptr. split. trivial. apply H0. trivial. split.
    apply (load_store_pos Glob.mem{2} qp{2} H10 8). rewrite /valid_ptr. split. trivial. apply H0. trivial. split.
    apply (load_store_pos Glob.mem{2} qp{2} H10 16). rewrite /valid_ptr. split. trivial. apply H0. trivial.    
    apply (load_store_pos Glob.mem{2} qp{2} H10 24). rewrite /valid_ptr. split. trivial. apply H0. trivial.   
qed.


lemma eq_h4_scalarmult_jade_base  mem _qp _np:
    equiv [MHop2.scalarmult_base ~ M_mulx.jade_scalarmult_curve25519_amd64_mulx_base:
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
     proc *. inline M_mulx.jade_scalarmult_curve25519_amd64_mulx_base. wp. sp.
    inline M_mulx.__load4 M_mulx.__store4. 
    do 2! unroll for{2} ^while. wp. sp.
    call eq_h4_scalarmult_base_mulx. skip. auto => />.
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



