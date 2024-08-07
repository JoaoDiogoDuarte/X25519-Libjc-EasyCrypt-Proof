require import AllCore Bool List Int IntDiv StdOrder CoreMap Ring Distr.

from Jasmin require import JModel JMemory JWord.

require import Curve25519_Procedures Curve25519_auto4 Curve25519_Ref4 W64limbs Zp_25519 Zplimbs EClib.

import Zp Curve25519_auto4 Curve25519_Procedures Curve25519_Ref4 Array4 Array8 Array32 StdOrder.IntOrder EClib.


(* additions, substractions and powers *)
equiv eq_spec_impl_add_ssr_ref4 : CurveProcedures.add ~ M_ref4.__add4_ssr:
    f{1}   = inzpRep4 g{2} /\
    g{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call (eq_spec_impl_add_rrs_ref4). skip. auto => />.
qed.


equiv eq_spec_impl_add_sss_ref4 : CurveProcedures.add ~ M_ref4.__add4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_add_rrs_ref4. skip. auto => />.
qed.


equiv eq_spec_impl_sub_ssr_ref4 : CurveProcedures.sub ~ M_ref4.__sub4_ssr:
    f{1} = inzpRep4 fs{2} /\
    g{1} = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rsr_ref4. skip. auto => />.
qed.


equiv eq_spec_impl_sub_sss_ref4 : CurveProcedures.sub ~ M_ref4.__sub4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rrs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_a24_ss_ref4 : CurveProcedures.mul_a24 ~ M_ref4.__mul4_a24_ss:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_a24_rs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_sss_ref4 : CurveProcedures.mul ~ M_ref4.__mul4_sss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_rss_ref4. skip. auto => />.
qed.


equiv eq_spec_impl_mul_ss_ref4 : CurveProcedures.mul ~ M_ref4._mul4_ss_:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_pp_ref4. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_ss_ref4 : CurveProcedures.sqr ~ M_ref4._sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1).
    unroll for{2} ^while.
    wp. sp. simplify.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
    move => &2.
    congr. apply Array4.ext_eq. move => H [H1] H2.
    smt(Array4.get_setE).
qed.

equiv eq_spec_impl_sqr_s__ref4 : CurveProcedures.sqr ~ M_ref4._sqr4_s_:
    f{1}   = inzpRep4 x{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
qed.


equiv eq_spec_impl_init_points_ref4 :
    CurveProcedures.init_points ~ M_ref4.__init_points4 :
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


equiv eq_spec_impl_ith_bit_ref4 : CurveProcedures.ith_bit ~ M_ref4.__ith_bit :
    k'{1}                    = pack32 (to_list k{2}) /\
    ctr{1}                   = to_uint ctr{2} /\
    0 <= ctr{1} < 256
    ==>
    b2i res{1}                = to_uint res{2}.
proof.
    proc; wp; skip => /> &2 H H0.
    rewrite (W64.and_mod 3 ctr{2}) //=  (W64.and_mod 6 (of_int (to_uint ctr{2} %% 8))%W64) //= !to_uint_shr //= !shr_shrw.
    smt(W64.to_uint_cmp  W64.of_uintK W64.to_uintK).
    rewrite /zeroextu64 /truncateu8 //=  !of_uintK => />.
    + rewrite  of_intE modz_small.  apply bound_abs. smt(W8.to_uint_cmp JUtils.powS_minus JUtils.pow2_0).
    rewrite bits2wE /int2bs /mkseq -iotaredE => />.
    auto => />.
    rewrite (modz_small (to_uint ctr{2} %% 8) W64.modulus). apply bound_abs. smt(W64.to_uint_cmp).
    rewrite (modz_small (to_uint ctr{2} %% 8) 64). apply bound_abs. smt(W64.to_uint_cmp).
    rewrite (modz_small (to_uint ctr{2} %% 8) W64.modulus). apply bound_abs. smt(W64.to_uint_cmp).
    pose ctr := to_uint ctr{2}.
    rewrite pack32E of_listE /to_list !/mkseq !initiE // -!iotaredE => />.
    rewrite !initiE //=. auto => />. smt().
    rewrite !/b2i !of_intE !bits2wE !/int2bs !/mkseq //=.
    rewrite -!iotaredE => />.
    rewrite !to_uintE !/bs2int !/w2bits !/mkseq /big /range !/predT -!iotaredE => />.
    rewrite !b2i0 => />.
    rewrite !initiE => />. smt(). auto => />.
    smt().
qed.

equiv eq_spec_impl_decode_scalar_25519_ref4 : CurveProcedures.decode_scalar ~ M_ref4.__decode_scalar:
    k'{1}  = pack4 (to_list k{2})
    ==>
    res{1} = pack32 (to_list res{2}).
proof.
    proc; wp; auto => />.
    unroll for{2} ^while => />; wp; skip => /> &2.
    rewrite !/set64_direct !/get8 !/init8 => />.
    rewrite pack4E pack32E.
    rewrite !/to_list /mkseq -!iotaredE => /> .
    rewrite !of_intE modz_small. by apply bound_abs. rewrite !bits2wE /int2bs /mkseq -!iotaredE => />.
    rewrite wordP => i rgi />.
    rewrite !of_listE !bits8E //= => />.
    rewrite !get_setE //= !orE !andE !map2E //=.
    rewrite !initiE => />.
    rewrite !initiE => />. smt(). smt().
    + case(i = 0) => /> *; case(i = 1) => /> *; case(i = 2) => /> *; case(i = 254) => /> *; case(i = 255) => /> *.
    + case(i %/ 8 = 0) => /> *.
    + rewrite initiE => /> . smt(). rewrite initiE => />. smt(). rewrite initiE => />. smt(). smt().
    + case(i %/ 8 - 1 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 2 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 3 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 4 = 0) => /> *.
    rewrite initiE => /> /#.
    + case(i %/ 8 - 5 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 6 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 7 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 8 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 9 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 10 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 11 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 12 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 13 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 14 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 15 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 16 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 17 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 18 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 19 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 20 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 21 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 22 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 23 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 24 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 25 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 26 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 27 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 28 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 29 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 30 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 31 = 0) => /> *.
    + rewrite !initiE => />. smt().
    + rewrite !initiE => />. smt().
    case(i %/ 64 = 0) => /> *. smt(). smt().
    + rewrite !initiE => /> /#. smt().
qed.


lemma eq_set_last_bit_to_zero64_ref4 x :
  hoare [
      M_ref4.__decode_u_coordinate4 :
      u = x
      ==>
      res = Curve25519_Operations.last_bit_to_zero64 x
  ].
proof.
    proc; wp; skip => />.
    rewrite /last_bit_to_zero64 => />; congr.
    pose X := x.[3].
    rewrite /of_int /int2bs  /mkseq /to_list -iotaredE => />.
    rewrite andE  wordP => /> k K0 K1.
    rewrite  map2iE //  get_bits2w //.
    smt(W64.initE).
qed.

lemma ill_set_last_bit_to_zero64: islossless M_ref4.__decode_u_coordinate4 by islossless.

lemma eq_ph_set_last_bit_to_zero64 x:
  phoare [
    M_ref4.__decode_u_coordinate4 :
    u = x
    ==>
    res = Curve25519_Operations.last_bit_to_zero64 x
  ] = 1%r.
proof.
    by conseq ill_set_last_bit_to_zero64 (eq_set_last_bit_to_zero64_ref4 x).
qed.

equiv eq_spec_impl_decode_u_coordinate_ref4 : CurveProcedures.decode_u_coordinate ~ M_ref4.__decode_u_coordinate4:
    u'{1}                      =     pack4 (to_list u{2})
    ==>
    res{1}                     =     inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (eq_ph_set_last_bit_to_zero64 u{2}).
    inline *; wp; skip => /> &2.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /last_bit_to_zero64 => />.
    rewrite /to_list /mkseq /to_list -iotaredE => />.
    do split.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= i && i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= i %/ 64 by smt(). auto => />.
    + case(i %/ 64 < 4) => /> *. smt(). smt().

    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= 64 + i && 64 + i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= (64 + i) %/ 64 by smt(). auto => />.
    + case((64 + i) %/ 64 < 4) => /> *. smt(). smt().

    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= 128 + i && 128 + i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= (128 + i) %/ 64 by smt(). auto => />.
    + case((128 + i) %/ 64 < 4) => /> *. smt(). smt().
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.

    rewrite pack4E => />. rewrite of_listE => />.
    rewrite !setE => />. rewrite initE => />.
    have ->: (0 <= 192 + i && 192 + i < 256) by smt(). auto => />.
    rewrite !initE => />.
    have ->: (0 <= i && i < 64) by smt().
    have ->: (0 <= 192 + i && 192 + i < 256) by smt().
    auto => />.
    case (i <> 63) => /> C.
    have ->: 192 + i <> 255 by smt().
    auto => />. rewrite !initE. smt().
qed.


equiv eq_spec_impl_decode_u_coordinate_base_ref4 :
    CurveProcedures.decode_u_coordinate_base ~ M_ref4.__decode_u_coordinate_base4:
        true
        ==>
        res{1} = inzpRep4 res{2}.
proof.
            proc *.
    inline *; wp; skip => />.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /last_bit_to_zero64 => />.
    have !->: ((of_int 9))%W256.[255 <- false] = ((of_int 9))%W256.
    rewrite !of_intE !bits2wE !/int2bs !/mkseq -iotaredE => />.
    apply W256.ext_eq => />. move => X X0 X1.
    rewrite get_setE //. case (X = 255) => /> C.
    rewrite /to_list /mkseq /to_list -iotaredE => />.
qed.


(** step 4 : cswap **)
equiv eq_spec_impl_cswap_ref4 :
    CurveProcedures.cswap ~ M_ref4.__cswap4:
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
        congr. apply Array4.ext_eq. rewrite /copy_64 => />. smt(Array4.get_setE).
    rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. rewrite /set0_64_ => />. smt().
    rewrite !mask_not_set !andw0 !xorw0 !/copy_64 => />.
    do split.
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
qed.

equiv eq_spec_impl_add_and_double_ref4 :
    CurveProcedures.add_and_double ~ M_ref4.__add_and_double4:
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
    call eq_spec_impl_mul_rss_ref4.
    call eq_spec_impl_mul_sss_ref4.
    call eq_spec_impl_add_sss_ref4.
    call eq_spec_impl_sqr_ss__ref4.
    call eq_spec_impl_mul_a24_ss_ref4.
    call eq_spec_impl_sqr_ss__ref4.
    call eq_spec_impl_sub_sss_ref4.
    call eq_spec_impl_mul_sss_ref4.
    call eq_spec_impl_sub_sss_ref4.
    call eq_spec_impl_add_sss_ref4.
    call eq_spec_impl_sqr_ss__ref4.
    call eq_spec_impl_sqr_ss__ref4.
    call eq_spec_impl_mul_sss_ref4.
    call eq_spec_impl_mul_sss_ref4.
    call eq_spec_impl_add_sss_ref4.
    call eq_spec_impl_sub_sss_ref4.
    call eq_spec_impl_add_ssr_ref4.
    call eq_spec_impl_sub_ssr_ref4.
    wp. done.
qed.

equiv eq_spec_impl_montgomery_ladder_step_ref4 :
    CurveProcedures.montgomery_ladder_step ~ M_ref4.__montgomery_ladder_step4:
        k'{1} =   pack32 (to_list k{2}) /\
        init'{1} = inzpRep4 init{2}             /\
        x2{1} = inzpRep4 x2{2}                  /\
        z2{1} = inzpRep4 z2r{2}                 /\
        x3{1} = inzpRep4 x3{2}                  /\
        z3{1} = inzpRep4 z3{2}                  /\
        b2i swapped{1} = to_uint swapped{2}     /\
        ctr'{1} = to_uint ctr{2}                /\
        0 <= ctr'{1} < 256
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1          /\
        res{1}.`2 = inzpRep4 res{2}.`2          /\
        res{1}.`3 = inzpRep4 res{2}.`3          /\
        res{1}.`4 = inzpRep4 res{2}.`4          /\
        b2i res{1}.`5 = to_uint res{2}.`5.
proof.
    proc => /=.
    call eq_spec_impl_add_and_double_ref4. wp.
    call eq_spec_impl_cswap_ref4. wp.
    call eq_spec_impl_ith_bit_ref4. skip.
    move => &1 &2 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.
    auto => />. rewrite H0.
    move => [H8 H9] H10 H11 H12 H13 H14.
    split;  auto => />. rewrite /H14 /H13.
    rewrite /b2i.
    case: (swapped{1} ^^ H10).
    move => *. smt(W64.to_uintK W64.xorw0 W64.xorwC).
    move => *. smt(W64.ge2_modulus W64.to_uintK W64.of_uintK W64.xorwK).
qed.


equiv eq_spec_impl_montgomery_ladder_ref4 :
    CurveProcedures.montgomery_ladder ~ M_ref4.__montgomery_ladder4 :
        init'{1} = inzpRep4 u{2}                     /\
        k'{1} =  pack32 (to_list k{2})
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1               /\
        res{1}.`2 = inzpRep4 res{2}.`2.
proof.
    proc. wp. sp.
    unroll {1} 4.
    rcondt {1} 4. auto => />. inline CurveProcedures.init_points.
        wp. sp. skip. auto => />.
    while(
          k'{1} = pack32 (to_list  k{2})                   /\
          ctr{1} = to_uint ctr{2}                          /\
          -1 <= ctr{1} < 256                                /\
          init'{1} = inzpRep4 us{2}                        /\
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_spec_impl_montgomery_ladder_step_ref4. skip. auto => />.
        move => &1 &2 ctrR H H0 H1 H2 E3. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        smt(W64.to_uint_cmp).
        move => H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. split. smt(W64.to_uint_cmp).
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial.
        call eq_spec_impl_montgomery_ladder_step_ref4. wp. call eq_spec_impl_init_points_ref4. skip. done.
qed.

equiv eq_spec_impl_it_sqr_ref4 :
    CurveProcedures.it_sqr ~ M_ref4._it_sqr4_p:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc. simplify. wp. sp.
    while (h{1}           =    inzpRep4 x{2}            /\
         ii{1}            =    to_uint i{2}              /\
         ii{1}            <=   W32.modulus               /\
         0                <=   ii{1}
    ).
    wp. call eq_spec_impl_sqr_p_ref4. conseq(_: _ ==> h{1} = inzpRep4 x{2}).
    move => &1 &2 [[H][ H0] [H1] H2 [H3] H4 H5]. split. apply H5.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    move => H6 H7 H8 H9. split. split. apply H9. split.
    rewrite to_uintB. rewrite  uleE => />. by smt(). rewrite to_uint1 H0 //.
    split. move: H1. smt(). move: H2. smt(). split. rewrite H0. move => H10.
    smt(W32.of_uintK W32.to_uintK W32.of_intN W32.to_uintN W32.of_intD).
    smt(W32.of_uintK W32.to_uintK W32.of_intN W32.to_uintN W32.of_intD).
    skip. auto => />. wp.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    call eq_spec_impl_sqr_p_ref4.
    skip. auto => />. move => &2 H H0. split. split.
    rewrite to_uintB. rewrite uleE => />. move: H. smt().
    rewrite to_uint1 //. split. move: H0. smt(). move: H. smt().
    split. move => H1.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    move => H1. move: H. smt().
qed.

equiv eq_spec_impl_it_sqr_s_ref4 :
    CurveProcedures.it_sqr ~ M_ref4._it_sqr4_s_:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2              <=   i{1}   ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_ref4._it_sqr4_s_. wp. sp.
    call eq_spec_impl_it_sqr_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_it_sqr_ss_ref4 :
        CurveProcedures.it_sqr ~ M_ref4._it_sqr4_ss_:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M_ref4._it_sqr4_ss_.
    unroll for{2} ^while. wp. sp.
    call eq_spec_impl_it_sqr_ref4. skip. auto => />. move => &2 H H0. congr.
    apply Array4.ext_eq. move => H1 [H2] H3. smt(Array4.get_setE).
qed.

equiv eq_spec_impl_invert_ref4 :
    CurveProcedures.invert ~ M_ref4.__invert4 :
        fs{1} = inzpRep4 fs{2}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc.
    sp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_sqr_s__ref4.
    call (eq_spec_impl_it_sqr_s_ref4). wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_s_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_ss_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_ss_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_s_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_ss_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_ss_ref4. wp.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_it_sqr_s_ref4. wp.
    call eq_spec_impl_sqr_ss_ref4.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_sqr_ss_ref4.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_mul_ss_ref4.
    call eq_spec_impl_sqr_s__ref4.
    call eq_spec_impl_sqr_ss_ref4.
    call eq_spec_impl_sqr_ss_ref4. wp.
    skip. done.
qed.

equiv eq_spec_impl_encode_point_ref4 : CurveProcedures.encode_point ~ M_ref4.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    res{1} = pack4 (to_list  res{2}).
proof.
    proc.
    ecall {2} (ph_eq_to_bytes_ref4 (inzpRep4 r{2})).
    call eq_spec_impl_mul_rss_ref4.
    call eq_spec_impl_invert_ref4.
    wp; skip => /> &2 H H0 H1 H2.
    by rewrite -H2.
qed.

equiv eq_spec_impl_scalarmult_internal_ref4 :
    CurveProcedures.scalarmult_internal ~ M_ref4.__curve25519_internal_ref4:
        k'{1} = pack32 (to_list  k{2}) /\
        u''{1} = inzpRep4 u{2}
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc.
    call eq_spec_impl_encode_point_ref4.
    call eq_spec_impl_montgomery_ladder_ref4. wp. skip.
    done.
qed.

equiv eq_spec_impl_scalarmult_ref4 :
    CurveProcedures.scalarmult ~ M_ref4._curve25519_ref4:
        k'{1} = pack4 (to_list  _k{2}) /\
        u'{1} = pack4 (to_list _u{2})
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_ref4 => />.
    call eq_spec_impl_decode_u_coordinate_ref4 => />.
    call eq_spec_impl_decode_scalar_25519_ref4 => />.
    wp; skip => />.
qed.


lemma eq_spec_impl_scalarmult_ptr_ref4 mem _rp _kp _up :
    equiv [CurveProcedures.scalarmult ~ M_ref4.__curve25519_ref4_ptr:
        valid_ptr (W64.to_uint _up)  32                                                          /\
        valid_ptr (W64.to_uint _kp)  32                                                          /\
        valid_ptr (W64.to_uint _rp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        rp{2} = _rp                                                                              /\
        kp{2} = _kp                                                                              /\
        up{2} = _up                                                                              /\
        u'{1} = pack4 (load_array4 (mem) (W64.to_uint _up))           /\
        k'{1} = pack4 (load_array4 (mem) (W64.to_uint _kp))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint _rp))    /\
        res{2} = tt
    ].
proof.
    proc *.
    inline M_ref4.__curve25519_ref4_ptr. wp. sp.
    inline M_ref4.__load4 M_ref4.__store4.
    do 3! unroll for{2} ^while.
    sp. wp. auto => />.
    call eq_spec_impl_scalarmult_ref4. skip. auto => />.
    move => &2 H H0 H1 H2 H3 H4.
    do split.
    congr. congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr. congr. rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H5 H6 H7.
    congr. congr. rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    apply (load_store_pos Glob.mem{2} rp{2} H7 0).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 8).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 16).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 24).
    rewrite /valid_ptr; split => />. done.
qed.


equiv eq_spec_impl_scalarmult_base_ref4 :
    CurveProcedures.scalarmult_base ~ M_ref4._curve25519_ref4_base:
        k'{1} = pack4 (to_list _k{2})
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_ref4.
    call eq_spec_impl_decode_u_coordinate_base_ref4.
    call eq_spec_impl_decode_scalar_25519_ref4.
    wp. skip. move => *. smt(Zplimbs.valRep4ToPack_xy).
qed.


lemma eq_spec_impl_scalarmult_base_ptr_ref4 mem _rp _kp :
 equiv [CurveProcedures.scalarmult_base ~ M_ref4.__curve25519_ref4_base_ptr:
        valid_ptr (W64.to_uint _rp) 32 /\
        valid_ptr (W64.to_uint _kp) 32 /\
        Glob.mem{2} = mem /\
        rp{2} = _rp /\
        kp{2} = _kp /\
        k'{1} =  pack4 (load_array4 (Glob.mem{2}) (W64.to_uint _kp))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint _rp)) /\ res{2} = tt].
proof.
    proc *. inline M_ref4.__curve25519_ref4_base_ptr M_ref4.__load4 M_ref4.__store4.
    do 2! unroll for{2} ^while.
    wp; call eq_spec_impl_scalarmult_base_ref4; wp; skip => />.
    move => H H0 H1 H2.
    do split.
    congr; congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H3 H4.
    congr; congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    apply (load_store_pos mem _rp H4 0); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 8); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 16); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 24); rewrite /valid_ptr. smt(). smt().
qed.


lemma eq_spec_impl_scalarmult_jade_ref4 mem _qp _np _pp:
    equiv [CurveProcedures.scalarmult ~ M_ref4.jade_scalarmult_curve25519_amd64_ref4:
        valid_ptr (W64.to_uint _qp)  32                                                          /\
        valid_ptr (W64.to_uint _np)  32                                                          /\
        valid_ptr (W64.to_uint _pp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        pp{2} = _pp                                                                              /\
        k'{1} = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint np{2})) /\
        u'{1}      = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint pp{2}))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref4.jade_scalarmult_curve25519_amd64_ref4; wp.
    call (eq_spec_impl_scalarmult_ptr_ref4 mem _qp _np _pp); wp; skip => />.
qed.


lemma eq_spec_impl_scalarmult_jade_base_ref4  mem _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M_ref4.jade_scalarmult_curve25519_amd64_ref4_base:
        valid_ptr (W64.to_uint _qp)  32                                                          /\
        valid_ptr (W64.to_uint _np)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        k'{1} = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint np{2}))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref4.jade_scalarmult_curve25519_amd64_ref4_base. wp. sp.
    call (eq_spec_impl_scalarmult_base_ptr_ref4 mem _qp _np). skip. done.
qed.
