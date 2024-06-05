require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Zp_25519 Ring EClib Distr.
from Jasmin require import JModel JMemory JWord.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_ref4.
require import Curve25519_auto.
require import W64limbs.
import Zp_25519.
import Curve25519_Spec Curve25519_auto Curve25519_Hop1 Curve25519_Hop2 Curve25519_ref4 Array4 Array8 Array32 StdOrder.IntOrder.


(* Should be moved elsewhere *)

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
        true 
        ==> 
        res{1} = inzpRep4 res{2}.
proof.
    proc. wp. skip. move => &1 &2 H.
    rewrite /inzpRep4. congr. rewrite /valRep4 /to_list /mkseq -iotaredE => />.
qed.


(** step 4 : cswap **)
equiv eq_h4_cswap :
    MHop2.cswap ~ M.__cswap4:
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
equiv eq_h4_add_and_double :
    MHop2.add_and_double ~ M.__add_and_double4:
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
          inzp (to_uint k'{1}) = inzpRep32 k{2}            /\
          init'{1} = inzpRep4 us{2}                        /\ 
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_h4_montgomery_ladder_step. skip. auto => />. 
        move => &1 &2 ctrR H H0 H1 H2. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        move => H3 H4 H5 H6 H7 H8 H9 H10. split.
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial. smt(@W64).  
    call eq_h4_montgomery_ladder_step. wp. call eq_h4_init_points. skip. done.
qed.

(** step 8 : iterated square **)
equiv eq_h4_it_sqr :
    MHop2.it_sqr ~ M._it_sqr4_p:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc. simplify. wp. sp.
    while (h{1}            =    inzpRep4 x{2}            /\ 
         ii{1}            =    to_uint i{2}              /\
         ii{1}            <=   W32.modulus               /\
         0                <=   ii{1}                     
    ).
    wp. call eq_h4_sqr_p. conseq(_: _ ==> h{1} = inzpRep4 x{2}).
    move => &1 &2 [[H][ H0] [H1] H2 [H3] H4 H5]. split. apply H5.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    move => H6 H7 H8 H9. split. split. apply H9. split.
    rewrite to_uintB. rewrite  uleE => />. by smt(). rewrite to_uint1 H0 //.
    split. move: H1. smt(). move: H2. smt(). split. rewrite H0. move => H10.
    smt(@W32). smt(@W32). skip. auto => />. wp.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=. 
    call eq_h4_sqr_p.  
    skip. auto => />. move => &2 H H0. split. split.
    rewrite to_uintB. rewrite uleE => />. move: H. smt().
    rewrite to_uint1 //. split. move: H0. smt(). move: H. smt().
    split. move => H1. smt(@W32). move => H1. move: H. smt().
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
    proc *. inline M._it_sqr4_s_. wp. sp. 
    call eq_h4_it_sqr. skip. auto => />.
qed.

equiv eq_h4_it_sqr_ss :
        MHop2.it_sqr ~ M._it_sqr4_ss_: 
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}   
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M._it_sqr4_ss_. 
    unroll for{2} ^while. wp. sp.
    call eq_h4_it_sqr. skip. auto => />. move => &2 H H0. congr. 
    apply Array4.ext_eq. move => H1 [H2] H3. smt(@Array4).
qed.

(** step 9 : invert **)
equiv eq_h4_invert :
    MHop2.invert ~ M.__invert4 : 
        fs{1} = inzpRep4 fs{2}
        ==> 
        res{1} = inzpRep4 res{2}.
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
        inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\  
        u''{1} = inzpRep4 u{2}
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
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} /\  
        inzp (to_uint u'{1}) = inzpRep4 _u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2} /\
        inzpRep32List (W32u8.to_list res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_h4_scalarmult_internal => />. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7. auto => />.
    rewrite -H7.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr. 
    rewrite to_uint_unpack32u8. congr. congr. smt().
    call eq_h4_decode_u_coordinate => />.
    call eq_h4_decode_scalar_25519 => />.
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


lemma eq_h4_scalarmult_ptr mem _rp _kp _up :
    equiv [MHop2.scalarmult ~ M.__curve25519_ref4_ptr:
        valid_ptr (W64.to_uint _up)  32                                                          /\ 
        valid_ptr (W64.to_uint _kp)  32                                                          /\
        valid_ptr (W64.to_uint _rp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        rp{2} = _rp                                                                              /\ 
        kp{2} = _kp                                                                              /\
        up{2} = _up                                                                              /\ 
        inzp (W256.to_uint u'{1}) = inzpRep4List (load_array4 (mem) (W64.to_uint _up))           /\
        inzp (W256.to_uint k'{1}) = inzpRep4List (load_array4 (mem) (W64.to_uint _kp))             
        ==>
        inzpRep32List(W32u8.to_list res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _rp))    /\
        res{2} = tt
    ].
proof.
    proc *.
    inline M.__curve25519_ref4_ptr. wp. sp.
    inline M.__load4 M.__store4. 
    do 3! unroll for{2} ^while.
    sp. wp. auto => />.
    call eq_h4_scalarmult. skip. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6. 
    split. split.
    rewrite H6 /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE. auto => />.  
    rewrite !to_uintD_small !to_uint_small => />. 
    move: H2. smt(). move: H1. smt(). move: H2. smt().
    rewrite H5 /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE. auto => />.  
    rewrite !to_uintD_small !to_uint_small => />. 
    move: H5. smt(). move: H5. smt(). move: H5. smt().
    move => H7 H8 H9 H10 H11. auto => />. rewrite -H11.
    move => H12. rewrite H12 H11.
    rewrite /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. congr. rewrite /to_list /mkseq -iotaredE => />. 
    split. apply (load_store_pos Glob.mem{2} rp{2} H10 0). 
    rewrite /valid_ptr. split. trivial. apply H4. trivial.
    split. apply (load_store_pos Glob.mem{2} rp{2} H10 8). 
    rewrite /valid_ptr. split. trivial. apply H4. trivial.
    split. apply (load_store_pos Glob.mem{2} rp{2} H10 16). 
    rewrite /valid_ptr. split. trivial. apply H4. trivial.
    apply (load_store_pos Glob.mem{2} rp{2} H10 24). 
    rewrite /valid_ptr. split. trivial. apply H4. trivial.    
qed.


equiv eq_h4_scalarmult_base :
    MHop2.scalarmult_base ~ M._curve25519_ref4_base:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} 
        ==>  
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}. 
proof.
    proc.
    call eq_h4_scalarmult_internal => />.
    call eq_h4_decode_u_coordinate_base => />.
    call eq_h4_decode_scalar_25519.
    wp. skip. done.
qed.


lemma eq_h4_scalarmult_base_ptr mem _rp _kp : 
 equiv [MHop2.scalarmult_base ~ M.__curve25519_ref4_base_ptr:
        valid_ptr (W64.to_uint _rp) 32 /\
        valid_ptr (W64.to_uint _kp) 32 /\
        Glob.mem{2} = mem /\
        rp{2} = _rp /\
        kp{2} = _kp /\
        inzp(W256.to_uint k'{1}) = inzpRep4List (load_array4 (Glob.mem{2}) (W64.to_uint _kp))
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _rp)) /\ res{2} = tt].
proof.
    proc *. inline M.__curve25519_ref4_base_ptr M.__load4 M.__store4. 
    do 2! unroll for{2} ^while. wp. sp. call eq_h4_scalarmult_base.
    skip. auto => />.  move => &1 &2 H H0 H1 H2. split.
    rewrite H2. rewrite /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4 /to_list /mkseq -iotaredE.
    congr. congr. congr. auto => />. rewrite !to_uintD_small !to_uint_small; smt(); smt().    
    move => H3 H4 H5 H6. rewrite H6. rewrite /inzpRep4 /inzpRep4List /valRep4 /valRep4List.
    congr. congr. congr. rewrite /to_list /mkseq /load_array4 -iotaredE => />. split.
    apply (load_store_pos mem _rp H5 0). rewrite /valid_ptr. smt(). smt(). split.
    apply (load_store_pos mem _rp H5 8). rewrite /valid_ptr. smt(). smt(). split.
    apply (load_store_pos mem _rp H5 16). rewrite /valid_ptr. smt(). smt(). 
    apply (load_store_pos mem _rp H5 24). rewrite /valid_ptr. smt(). smt().
qed.    


lemma eq_h4_scalarmult_jade mem _qp _np _pp:
    equiv [MHop2.scalarmult ~ M.jade_scalarmult_curve25519_amd64_ref4:
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
    proc *. inline M.jade_scalarmult_curve25519_amd64_ref4. wp. sp.
    call (eq_h4_scalarmult_ptr mem _qp _np _pp). skip. auto => />.
    move => &1 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite -H9. rewrite to_uint_unpack32u8. rewrite /inzpRep32List /valRep32List.
    congr. congr. congr. smt(@W32u8).
qed.


lemma eq_h4_scalarmult_jade_base  mem _qp _np:
    equiv [MHop2.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_ref4_base:
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
    proc *. inline M.jade_scalarmult_curve25519_amd64_ref4_base. wp. sp.
    call (eq_h4_scalarmult_base_ptr mem _qp _np). skip. done.
qed.



