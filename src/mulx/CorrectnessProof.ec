require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Ring Distr.

from Jasmin require import JModel JMemory JWord.

require import Curve25519_Procedures Curve25519_Operations Curve25519_auto_mulx Curve25519_mulx W64limbs Zp_25519 Zplimbs EClib.

import Zp Curve25519_auto_mulx Curve25519_Operations Curve25519_Procedures Curve25519_mulx Array4 Array8 Array32 StdOrder.IntOrder EClib.


abbrev zexp = ZModpRing.exp.

(* additions, substractions and powers *)
equiv eq_spec_impl_add_sss_mulx : CurveProcedures.add ~ M_mulx.__add4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__add4_sss. wp. sp.
    call eq_spec_impl_add_rrs_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_add_ssr_mulx : CurveProcedures.add ~ M_mulx.__add4_ssr:
    g{1}   = inzpRep4 fs{2} /\
    f{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__add4_ssr. wp. sp.
    call eq_spec_impl_add_rrs_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sub_sss_mulx : CurveProcedures.sub ~ M_mulx.__sub4_sss:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx.__sub4_sss. wp. sp.
    call eq_spec_impl_sub_rrs_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sub_ssr_mulx : CurveProcedures.sub ~ M_mulx.__sub4_ssr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__sub4_ssr. wp. sp.
    call eq_spec_impl_sub_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_a24_ss_mulx : CurveProcedures.mul_a24 ~ M_mulx.__mul4_a24_ss:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx.__mul4_a24_ss. wp. sp.
    call eq_spec_impl_mul_a24_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_rpr_mulx : CurveProcedures.mul ~ M_mulx._mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx._mul4_rpr. wp. sp.
    call eq_spec_impl_mul__rpr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_rsr__mulx : CurveProcedures.mul ~ M_mulx._mul4_rsr_:
    f{1}   = inzpRep4 _fs{2} /\
    g{1}   = inzpRep4 _g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx._mul4_rsr_. wp. sp.
    call eq_spec_impl_mul_rpr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_ssr_mulx : CurveProcedures.mul ~ M_mulx.__mul4_ssr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__mul4_ssr. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_sss_mulx : CurveProcedures.mul ~ M_mulx.__mul4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__mul4_sss. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_rss_mulx : CurveProcedures.mul ~ M_mulx.__mul4_rss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx.__mul4_rss. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rr_mulx : CurveProcedures.sqr ~ M_mulx._sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx._sqr4_rr. wp. sp.
    call (eq_spec_impl__sqr_rr_mulx) . skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rr__mulx : CurveProcedures.sqr ~ M_mulx._sqr4_rr_:
    f{1}   = inzpRep4 _f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_mulx._sqr4_rr_. wp. sp. rewrite /copy_64 => />.
    call eq_spec_impl_sqr_rr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_ss_mulx : CurveProcedures.sqr ~ M_mulx.__sqr4_ss:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx.__sqr4_ss. wp. sp.
    call eq_spec_impl__sqr_rr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rs_mulx : CurveProcedures.sqr ~ M_mulx.__sqr4_rs:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M_mulx.__sqr4_rs. wp. sp.
    call eq_spec_impl__sqr_rr_mulx. skip. auto => />.
qed.


(** step 1: init points and decoding u-coordinates **)
equiv eq_spec_impl_init_points_mulx :
    CurveProcedures.init_points ~ M_mulx.__init_points4 :
        init{1} = inzpRep4 initr{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1 /\
        res{1}.`2 = inzpRep4 res{2}.`2 /\
        res{1}.`3 = inzpRep4 res{2}.`3 /\
        res{1}.`4 = inzpRep4 res{2}.`4.
proof.
    proc.
    wp. unroll for{2} ^while. wp. skip. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    split; auto => />. rewrite /H4 /H0 /H2 /H3 /Zp.one /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE => />.
    split; auto => />. rewrite /H5  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE  => />.
    rewrite /H6  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 // /valRep4 /to_list /mkseq -iotaredE  => />.
qed.

equiv eq_spec_impl_decode_u_coordinate_base_mulx :
    CurveProcedures.decode_u_coordinate_base ~ M_mulx.__decode_u_coordinate_base4:
        true
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc. wp. skip. move => &1 &2 H.
    rewrite /inzpRep4. congr. rewrite /valRep4 /to_list /mkseq -iotaredE => />.
qed.


(** step 4 : cswap **)
equiv eq_spec_impl_cswap_mulx :
    CurveProcedures.cswap ~ M_mulx.__cswap4:
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
        have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64_ /=. smt().
        rewrite !mask_set /=.
        have lxor1 : forall (x1 x2:W64.t),  x1 `^` (x2 `^` x1) = x2.
            move=> *. rewrite xorwC -xorwA xorwK xorw0 //.
        have lxor2 : forall (x1 x2:W64.t),  x1 `^` (x1 `^` x2) = x2.
            move=> *. rewrite xorwA xorwK xor0w //.
        rewrite !lxor1 !lxor2.
        split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
        split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
        split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
        congr. apply Array4.ext_eq. smt(Array4.get_setE).
    rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. rewrite /set0_64_ => />. smt().
    rewrite !mask_not_set !andw0 !xorw0.
    do split.
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
qed.

(** step 5 : add_and_double **)
equiv eq_spec_impl_add_and_double_mulx :
    CurveProcedures.add_and_double ~ M_mulx.__add_and_double4:
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
    proc => /=. sp.
    call eq_spec_impl_mul_rss_mulx.
    call eq_spec_impl_mul_sss_mulx.
    call eq_spec_impl_add_sss_mulx.
    call eq_spec_impl_sqr_ss_mulx.
    call eq_spec_impl_mul_a24_ss_mulx.
    call eq_spec_impl_sqr_ss_mulx.
    swap{1} 11 1.
    call eq_spec_impl_mul_ssr_mulx.
    call eq_spec_impl_sub_ssr_mulx.
    call eq_spec_impl_sub_sss_mulx.
    call eq_spec_impl_add_sss_mulx.
    call eq_spec_impl_sqr_rs_mulx.
    call eq_spec_impl_sqr_ss_mulx.
    call eq_spec_impl_mul_sss_mulx.
    call eq_spec_impl_mul_sss_mulx.
    call eq_spec_impl_add_sss_mulx.
    call eq_spec_impl_sub_sss_mulx.
    call eq_spec_impl_add_ssr_mulx.
    call eq_spec_impl_sub_ssr_mulx.
    skip. by done.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_spec_impl_montgomery_ladder_step_mulx :
    CurveProcedures.montgomery_ladder_step ~ M_mulx.__montgomery_ladder_step4:
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
    call eq_spec_impl_add_and_double_mulx. wp.
    call eq_spec_impl_cswap_mulx. wp.
    call eq_spec_impl_ith_bit_mulx. skip.
    move => &1 &2 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.
    auto => />. rewrite H0.
    move => [H8 H9] H10 H11 H12 H13 H14.
    split;  auto => />. rewrite /H14 /H13.
    rewrite /b2i.
    case: (swapped{1} ^^ H10).
    move => *. smt(W64.to_uintK W64.xorw0 W64.xorwC).
    move => *. smt(W64.ge2_modulus W64.to_uintK W64.of_uintK W64.xorwK).
qed.

(** step 7 : montgomery_ladder **)
equiv eq_spec_impl_montgomery_ladder_mulx :
    CurveProcedures.montgomery_ladder ~ M_mulx.__montgomery_ladder4 :
        init'{1} = inzpRep4 u{2}                     /\
        inzp (W256.to_uint k'{1}) =  inzpRep32 k{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1               /\
        res{1}.`2 =inzpRep4  res{2}.`2.
proof.
    proc. wp. sp.
    unroll {1} 4.
    rcondt {1} 4. auto => />. inline CurveProcedures.init_points.
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
        wp. sp. call eq_spec_impl_montgomery_ladder_step_mulx. skip. auto => />.
        move => &1 &2 ctrR H H0 H1 H2. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        move => H3 H4 H5 H6 H7 H8 H9 H10. split.
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial. smt(W64.to_uintK).
        call eq_spec_impl_montgomery_ladder_step_mulx. wp. call eq_spec_impl_init_points_mulx. skip. done.
qed.


(** step 9 : invert **)

equiv eq_spec_impl_it_sqr_aux_mulx :
        M_mulx.__it_sqr4_x2 ~ CurveProcedures.it_sqr_aux:
        inzpRep4 f{1} = a{2} /\
        W32.to_uint i{1} = l{2} /\
        0 < l{2}
        ==>
        inzpRep4 res{1} = res{2}.
proof.
    proc; simplify.
    while(
        0 <= ii{2} /\ 0 <= W32.to_uint i{1} /\ ii{2} = W32.to_uint i{1} /\
        f{2} = inzpRep4 f{1}  /\ zf{1} = (0 = W32.to_uint i{1})
    ).
    wp.
    symmetry.
    call eq_spec_impl__sqr_rr_mulx. call eq_spec_impl__sqr_rr_mulx. wp. symmetry.
    skip => />.
    move => &1 *. do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />.
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1. smt(W32.to_uint_cmp).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite to_uintB.
    + rewrite uleE to_uint1; smt(). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of to_uintB.
    + rewrite uleE to_uint1. smt(). rewrite -to_uintB. rewrite uleE. smt(W32.to_uint_cmp).
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    wp. call eq_spec_impl__sqr_rr_mulx_rev. call eq_spec_impl__sqr_rr_mulx_rev. wp.
    skip => />. move => &1 H.
    do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    rewrite to_uintB. rewrite uleE to_uint1. smt(W32.to_uint_cmp). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
qed.

equiv eq_spec_impl_it_sqr_aux_mulx_test :
        CurveProcedures.it_sqr_aux ~ M_mulx.__it_sqr4_x2:
        a{1} = inzpRep4 f{2} /\
        l{1} = W32.to_uint i{2} /\
        0 < l{1}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc; simplify.
    while(
        0 <= ii{1} /\ 0 <= W32.to_uint i{2} /\ ii{1} = W32.to_uint i{2} /\
        f{1} = inzpRep4 f{2}  /\ zf{2} = (0 = W32.to_uint i{2})
    ).
    wp. call eq_spec_impl__sqr_rr_mulx. call eq_spec_impl__sqr_rr_mulx. wp.
    skip => />.
    move => &1 *. do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />.
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1. smt(W32.to_uint_cmp).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite to_uintB.
    + rewrite uleE to_uint1; smt(). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of to_uintB.
    + rewrite uleE to_uint1. smt(). rewrite -to_uintB. rewrite uleE. smt(W32.to_uint_cmp).
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    wp. call eq_spec_impl__sqr_rr_mulx. call eq_spec_impl__sqr_rr_mulx. wp.
    skip => />. move => &1 H.
    do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    rewrite to_uintB. rewrite uleE to_uint1. smt(W32.to_uint_cmp). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
qed.


lemma eq_spec_impl__it_sqr_mulx (i1: int) (i2: int):
    i1 = i2 => 2 <= i1  =>
equiv[
        M_mulx.__it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
proof.
    move => I I0.
    transitivity
     CurveProcedures.it_sqr_aux
     (
       l{2} = W32.to_uint i{1}  /\
       a{2} = inzpRep4 f{1} /\
       1 < l{2}
        ==>
        inzpRep4 res{1} = res{2})
     (  a{1} = f{2} /\
        l{1} = i{2} /\
        l{1} = i1 /\
        l{1} = i2 /\
        2 <= i{2}
        ==>
        res{1} = zexp res{2} (exp 2 i1)).
    auto => />.
    move => &1 &2 *.
    exists(f{2}, i{2}) => />. smt().
    move => &1 &m &2 H H0. rewrite -H0. assumption.
    proc *.
    call eq_spec_impl_it_sqr_aux_mulx. skip => />. smt(W32.to_uint_cmp).

    proc; inline *; simplify.
    seq 7 6 : (ii{1} = l{1} - 1 /\
        h{2} = (zexp a{1} 2) /\
        0 <= ii{2} /\
        0 <= ii{1} /\
        ii{1} = ii{2} /\
        1 <= counter{2} <= i1 /\
        counter{2} = i1 - ii{2} /\
        f{1} = zexp h{2} (exp 2 counter{2})).
        wp; skip. auto => />. move => *.  smt().

    while(
        0 <= ii{1} /\
        0 <= ii{2} /\
        ii{1} = ii{2} /\
        1 <= counter{2} /\
        counter{2} = i1 - ii{2} /\
        f{1} = zexp h{2} (exp 2 (counter{2}))).
    wp; skip. auto => />.
    move => &1 &2 H H0 H1.
    smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
    skip => />. move => &1 &2 H H1 H2 H3 H4 H5 H6 H7 H8 H9.
    have H10: H4 = 0. smt(). rewrite H10 => />.
qed.

lemma eq_spec_impl__it_sqr_mulx_x2 (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
equiv[
        M_mulx.__it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
proof.
    move => I I0 I1 I2;
     transitivity
     CurveProcedures.it_sqr_aux
     (
       l{2} = W32.to_uint i{1}  /\
       a{2} = inzpRep4 f{1} /\
       1 < l{2}
        ==>
        inzpRep4 res{1} = res{2})
     (  a{1} = f{2} /\
        2*l{1} = i{2} /\
        l{1} = i1 /\
        i{2} = i2  /\
        4 <= i{2}  /\
        2 <= l{1}
        ==>
        res{1} = res{2}).
    auto => />. move => &1 &2 *.
    exists(f{2}, i1) => />. smt(). smt().
    proc *.
    call eq_spec_impl_it_sqr_aux_mulx. skip => />. smt(W32.to_uint_cmp).
     proc; simplify. inline *.
     seq 7 6 : (
        i2 = 2*l{1} /\
        ii{1} = l{1} - counter{2} /\
        ii{2} = i2 - counter{2} /\
        h{2} = (zexp a{1} 2) /\
        0 <= ii{2} /\
        0 <= ii{1} /\
        1 <= counter{2} <= i1 /\
        f{1} = zexp h{2} (exp 2 counter{2})).
    wp; skip. auto => />.
    move => *. smt().
      async while
      [ (fun r => 0%r < ii%r), (ii{1} - 1)%r ]
      [ (fun r => 0%r < ii%r), (ii{1} - 1)%r ]
        (0 < ii{1} /\ 0 < ii{2}) (!(0 < ii{1}))
      :
      (
        (ii{2} %% 2 = 0   => 2*ii{1} - 1 = ii{2})  /\
        (ii{2} %% 2 <> 0  => 2*ii{1}     = ii{2})  /\
        0 <= ii{1} /\
        0 <= ii{2}
      ).
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &2 * /#.
    move => &1; auto => />.
    move => v1 v2; auto => />.
    while(
        0 <= ii{1} /\
        0 <= ii{2} /\
        (ii{2} %% 2 = 0   => 2*ii{1} - 1 = ii{2})  /\
        (ii{2} %% 2 <> 0  => 2*ii{1}     = ii{2})  /\
        1 <= counter{2} /\
        f{1} = zexp h{2} (exp 2 counter{2})
    ) => //=.
   auto => />; move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7.
   smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
   auto => />; move => &1 &2 H H0 H1 H2 H3 H4 H5.
   smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
    while true (ii) => //.
    move => H; auto => />. skip => />; move => &hr H0 H1 H2 H3 H4 H5 /#.
    while true (ii) => //. move => H; auto => /> /#. skip => /> /#.
    skip => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 /#.
qed.


lemma eq_spec_impl_it_sqr_x2_mulx (i1: int) (i2: int):
    i1 = i2 => 2 <= i1 => i2 %% 2 = 0 =>
equiv[
        M_mulx._it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
    move => *; proc *.
    inline {1} 1. sp; wp.
    call (eq_spec_impl__it_sqr_mulx i1 i2). skip => />.
qed.


lemma  eq_spec_impl_it_sqr_x2__mulx  (i1: int) (i2: int):
    i1 = i2 => 2 <= i1 => i2 %% 2 = 0 =>
    equiv[
        M_mulx._it_sqr4_x2_ ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 _f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
proof.
    move => *; proc *.
    inline{1} 1. inline{1} 5. wp; sp.
    call (eq_spec_impl__it_sqr_mulx i1 i2). skip => />.
qed.


lemma eq_spec_impl_it_sqr_x2_mulx_x2 (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
equiv[
        M_mulx._it_sqr4_x2 ~ CurveProcedures.it_sqr:
       i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
    move => *; proc *.
    inline {1} 1. sp; wp.
    call (eq_spec_impl__it_sqr_mulx_x2 i1 i2). skip => />.
qed.


lemma  eq_spec_impl_it_sqr_x2__mulx_x2  (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
        equiv[
        M_mulx._it_sqr4_x2_ ~ CurveProcedures.it_sqr:
         i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 _f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
proof.
    move => *; proc *.
    inline{1} 1. inline{1} 5. wp; sp.
    call (eq_spec_impl__it_sqr_mulx_x2 i1 i2). skip => />.
qed.



lemma eq_spec_impl_invert_mulx (i1: int) (i2: int) :
    i1 = 2*i2 => 0 < i1 =>
    equiv[
    CurveProcedures.invert ~ M_mulx.__invert4 :
        fs{1} = inzpRep4 f{2}
        ==>
        res{1} = inzpRep4 res{2}].
proof.
    move => H H0.
    proc. sp.
    auto => />.
    call eq_spec_impl_mul_rsr__mulx.
    call eq_spec_impl_sqr_rr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 2 4); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 25 50); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 50 100); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 25 50); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 5 10); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 10 20); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 5 10); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 2 4); wp; symmetry.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_mul_rsr__mulx.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_mul_rsr__mulx. wp.
    call eq_spec_impl_mul_rsr__mulx.
    call eq_spec_impl_sqr_rr__mulx.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx.
    skip.  done.
qed.

(** step 11 : scalarmult **)

equiv eq_spec_impl_scalarmult_internal_mulx :
    CurveProcedures.scalarmult_internal ~ M_mulx.__curve25519_internal_mulx:
        inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\
        u''{1} = inzpRep4 u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_encode_point_mulx.
    call eq_spec_impl_montgomery_ladder_mulx. wp. skip.
    done.
qed.

equiv eq_spec_impl_scalarmult_mulx :
    CurveProcedures.scalarmult ~ M_mulx.__curve25519_mulx:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2} /\
        inzp (to_uint u'{1}) = inzpRep4 _u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2} /\
        inzpRep32List (W32u8.to_list res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_mulx => />. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7. auto => />.
    rewrite -H7.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
    call eq_spec_impl_decode_u_coordinate_mulx => />.
    call eq_spec_impl_decode_scalar_25519_mulx => />.
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

equiv eq_spec_impl_scalarmult_base_mulx :
    CurveProcedures.scalarmult_base ~ M_mulx.__curve25519_mulx_base:
        inzp(W256.to_uint k'{1}) = inzpRep4 _k{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_mulx => />.
    call eq_spec_impl_decode_u_coordinate_base_mulx => />.
    call eq_spec_impl_decode_scalar_25519_mulx.
    wp. skip. done.
qed.

lemma eq_spec_impl_scalarmult_jade_mulx mem _qp _np _pp:
    equiv [CurveProcedures.scalarmult ~ M_mulx.jade_scalarmult_curve25519_amd64_mulx:
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
    call eq_spec_impl_scalarmult_mulx. skip. auto => />.
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


lemma eq_spec_impl_scalarmult_jade_base  mem _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M_mulx.jade_scalarmult_curve25519_amd64_mulx_base:
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
    call eq_spec_impl_scalarmult_base_mulx. skip. auto => />.
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
