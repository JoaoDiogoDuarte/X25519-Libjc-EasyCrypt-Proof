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

(** step 1: init points and decoding u-coordinates **)
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


(** step 1 : decode_scalar_25519 **)
equiv eq_spec_impl_decode_scalar_25519_ref4 : CurveProcedures.decode_scalar ~ M_ref4.__decode_scalar:
    k'{1}  = pack4 (to_list k{2})
    ==>
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}.
proof.
    proc; wp; auto => />.
    unroll for{2} ^while => />; wp; skip => /> &2.
    rewrite !/set64_direct !/get8 !/init8 => />.
    rewrite to_uint_unpack32u8 inzpRep32E valRep32E /val_digits pack4E.
    congr. congr. congr. rewrite !/to_list /mkseq -iotaredE => /> .
    rewrite of_intE modz_small. by apply bound_abs. rewrite bits2wE /int2bs /mkseq -iotaredE => />.
    rewrite !W8.wordP.
    do split.
    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: i <> 254 by smt(). have ->: i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 8 + i <> 254 by smt(). have ->: 8 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 16 + i <> 254 by smt(). have ->: 16 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 24 + i <> 254 by smt(). have ->: 24 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 32 + i <> 254 by smt(). have ->: 32 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 40 + i <> 254 by smt(). have ->: 40 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 48 + i <> 254 by smt(). have ->: 48 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 56 + i <> 254 by smt(). have ->: 56 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 64 + i <> 254 by smt(). have ->: 64 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 72 + i <> 254 by smt(). have ->: 72 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 80 + i <> 254 by smt(). have ->: 80 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 88 + i <> 254 by smt(). have ->: 88 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 96 + i <> 254 by smt(). have ->: 96 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 104 + i <> 254 by smt(). have ->: 104 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 112 + i <> 254 by smt(). have ->: 112 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 120 + i <> 254 by smt(). have ->: 120 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 128 + i <> 254 by smt(). have ->: 128 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 136 + i <> 254 by smt(). have ->: 136 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 144 + i <> 254 by smt(). have ->: 144 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 152 + i <> 254 by smt(). have ->: 152 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 160 + i <> 254 by smt(). have ->: 160 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 168 + i <> 254 by smt(). have ->: 168 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 176 + i <> 254 by smt(). have ->: 176 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 184 + i <> 254 by smt(). have ->: 184 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 192 + i <> 254 by smt(). have ->: 192 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 200 + i <> 254 by smt(). have ->: 200 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 208 + i <> 254 by smt(). have ->: 208 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 216 + i <> 254 by smt(). have ->: 216 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 224 + i <> 254 by smt(). have ->: 224 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 232 + i <> 254 by smt(). have ->: 232 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. have ->: 240 + i <> 254 by smt(). have ->: 240 + i <> 255 by smt(). auto => />.
    + rewrite !initiE. by smt(). smt().

    + move => i rgi />. rewrite !of_intE !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    + rewrite !initiE. by smt(). by smt().
    rewrite of_listE !bits8E !initiE //= => />.
    + rewrite !get_setE //=. rewrite !initiE. by smt().
    + auto => />. rewrite !initiE. by smt().
    smt().
qed.

(** step 2 : decode_u_coordinate **)

lemma eq_set_msb_to_zero_ref4 x :
  hoare [
      M_ref4.__decode_u_coordinate4 :
      u = x
      ==>
      res = Curve25519_Operations.msb_to_zero x
  ].
proof.
    proc; wp; skip => />.
    rewrite /msb_to_zero => />; congr.
    pose X := x.[3].
    rewrite /of_int /int2bs  /mkseq /to_list -iotaredE => />.
    rewrite andE  wordP => /> k K0 K1.
    rewrite  map2iE //  get_bits2w //.
    smt(W64.initE).
qed.

lemma ill_set_msb_to_zero: islossless M_ref4.__decode_u_coordinate4 by islossless.

lemma eq_ph_set_msb_to_zero x:
  phoare [
    M_ref4.__decode_u_coordinate4 :
    u = x
    ==>
    res = Curve25519_Operations.msb_to_zero x
  ] = 1%r.
proof.
    by conseq ill_set_msb_to_zero (eq_set_msb_to_zero_ref4 x).
qed.

equiv eq_spec_impl_decode_u_coordinate_ref4 : CurveProcedures.decode_u_coordinate ~ M_ref4.__decode_u_coordinate4:
    u'{1}                      =     W4u64.pack4 (Array4.to_list u{2})
    ==>
    res{1}                     =     inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (eq_ph_set_msb_to_zero u{2}).
    inline *; wp; skip => /> &2.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /msb_to_zero => />.
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
    rewrite /msb_to_zero => />.
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

(** step 5 : add_and_double **)
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

(** step 7 : montgomery_ladder **)
equiv eq_spec_impl_montgomery_ladder_step_ref4 :
    CurveProcedures.montgomery_ladder_step ~ M_ref4.__montgomery_ladder_step4:
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
          inzp (to_uint k'{1}) = inzpRep32 k{2}            /\
          init'{1} = inzpRep4 us{2}                        /\
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_spec_impl_montgomery_ladder_step_ref4. skip. auto => />.
        move => &1 &2 ctrR H H0 H1 H2. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        move => H3 H4 H5 H6 H7 H8 H9 H10. split.
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0. trivial. smt(W64.to_uintK).
    call eq_spec_impl_montgomery_ladder_step_ref4. wp. call eq_spec_impl_init_points_ref4. skip. done.
qed.

(** step 8 : iterated square **)
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
    while (h{1}            =    inzpRep4 x{2}            /\
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

(** step 9 : invert **)
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


(** step 10 : encode point **)
equiv eq_spec_impl_encode_point_ref4 : CurveProcedures.encode_point ~ M_ref4.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    proc.
    ecall {2} (ph_eq_to_bytes_ref4 (inzpRep4 r{2})).
    call eq_spec_impl_mul_rss_ref4.
    call eq_spec_impl_invert_ref4.
    wp; skip => /> &2 H H0 H1 H2.
    rewrite -H2. rewrite inzpRep4E. congr.
    smt(@Zplimbs).
qed.


(** step 11 : scalarmult **)

equiv eq_spec_impl_scalarmult_internal_ref4 :
    CurveProcedures.scalarmult_internal ~ M_ref4.__curve25519_internal_ref4:
        inzp(W256.to_uint k'{1}) = inzpRep32 k{2} /\
        u''{1} = inzpRep4 u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_encode_point_ref4.
    call eq_spec_impl_montgomery_ladder_ref4. wp. skip.
    done.
qed.

equiv eq_spec_impl_scalarmult_ref4 :
    CurveProcedures.scalarmult ~ M_ref4._curve25519_ref4:
        W256.to_uint k'{1} = valRep4 _k{2} /\
        to_uint u'{1} = valRep4 _u{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2} /\
        inzpRep32List (W32u8.to_list res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_ref4 => />. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7. auto => />.
    rewrite -H7.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
    call eq_spec_impl_decode_u_coordinate_ref4 => />.
    call eq_spec_impl_decode_scalar_25519_ref4 => />.
    move => &1 &2 [H] H0 [H1] H2. split. auto => />.
    move => H3 H4 H5 H6. split. auto => />.
    smt().
    move => H7. split. assumption. move => H8 H9 H10 H11.
    rewrite -H11.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
    wp. skip.
    auto => />. move => &1 &2 H H0. split. smt(@Zplimbs).
    move => H1 H2 H3 H4. split.
    smt(@Zplimbs). move => H5 H6 H7 H8.
    rewrite -H8.
    rewrite /inzpRep32List /inzpRep4 /valRep32List. congr.
    rewrite to_uint_unpack32u8. congr. congr. smt().
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
        W256.to_uint u'{1} = valRep4List (load_array4 (mem) (W64.to_uint _up))           /\
        W256.to_uint k'{1} = valRep4List (load_array4 (mem) (W64.to_uint _kp))
        ==>
        inzpRep32List(W32u8.to_list res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _rp))    /\
        res{2} = tt
    ].
proof.
    proc *.
    inline M_ref4.__curve25519_ref4_ptr. wp. sp.
    inline M_ref4.__load4 M_ref4.__store4.
    do 3! unroll for{2} ^while.
    sp. wp. auto => />.
    call eq_spec_impl_scalarmult_ref4. skip. auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    split. split.
    rewrite H6 /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. rewrite /to_list /mkseq -iotaredE. auto => />.
    rewrite !to_uintD_small !to_uint_small => />.
    move: H2. smt(). move: H1. smt(). move: H2. smt().
    rewrite H5 /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4.
    congr. congr. rewrite /to_list /mkseq -iotaredE. auto => />.
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


equiv eq_spec_impl_scalarmult_base_ref4 :
    CurveProcedures.scalarmult_base ~ M_ref4._curve25519_ref4_base:
        W256.to_uint k'{1} = valRep4 _k{2}
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4 res{2}.
proof.
    proc.
    call eq_spec_impl_scalarmult_internal_ref4 => />.
    call eq_spec_impl_decode_u_coordinate_base_ref4 => />.
    call eq_spec_impl_decode_scalar_25519_ref4.
    wp. skip. move => *. smt(@Zplimbs).
qed.


lemma eq_spec_impl_scalarmult_base_ptr_ref4 mem _rp _kp :
 equiv [CurveProcedures.scalarmult_base ~ M_ref4.__curve25519_ref4_base_ptr:
        valid_ptr (W64.to_uint _rp) 32 /\
        valid_ptr (W64.to_uint _kp) 32 /\
        Glob.mem{2} = mem /\
        rp{2} = _rp /\
        kp{2} = _kp /\
        W256.to_uint k'{1} =  valRep4List (load_array4 (Glob.mem{2}) (W64.to_uint _kp))
        ==>
        inzp (W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _rp)) /\ res{2} = tt].
proof.
    proc *. inline M_ref4.__curve25519_ref4_base_ptr M_ref4.__load4 M_ref4.__store4.
    do 2! unroll for{2} ^while. wp. sp. call eq_spec_impl_scalarmult_base_ref4.
    skip. auto => />.  move => &1 &2 H H0 H1 H2. split.
    rewrite H2. rewrite /inzpRep4List /inzpRep4 /valRep4 /valRep4List /load_array4 /to_list /mkseq -iotaredE.
    congr. congr. auto => />. rewrite !to_uintD_small !to_uint_small; smt(); smt().
    move => H3 H4 H5 H6.
    rewrite H6. rewrite /inzpRep4 /inzpRep4List /valRep4 /valRep4List.
    congr. congr. congr. rewrite /to_list /mkseq /load_array4 -iotaredE => />. split.
    apply (load_store_pos mem _rp H5 0). rewrite /valid_ptr. smt(). smt(). split.
    apply (load_store_pos mem _rp H5 8). rewrite /valid_ptr. smt(). smt(). split.
    apply (load_store_pos mem _rp H5 16). rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H5 24). rewrite /valid_ptr. smt(). smt().
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
        W256.to_uint k'{1} = valRep4List (load_array4 (Glob.mem{2}) (W64.to_uint np{2})) /\
        to_uint u'{1}      = valRep4List (load_array4 (Glob.mem{2}) (W64.to_uint pp{2}))
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref4.jade_scalarmult_curve25519_amd64_ref4. wp. sp.
    call (eq_spec_impl_scalarmult_ptr_ref4 mem _qp _np _pp). skip. auto => />.
    move => &1 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite -H9. rewrite to_uint_unpack32u8. rewrite /inzpRep32List /valRep32List.
    congr. congr. congr. smt().
qed.


lemma eq_spec_impl_scalarmult_jade_base_ref4  mem _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M_ref4.jade_scalarmult_curve25519_amd64_ref4_base:
        valid_ptr (W64.to_uint _qp)  32                                                          /\
        valid_ptr (W64.to_uint _np)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        W256.to_uint k'{1} = valRep4List (load_array4 (Glob.mem{2}) (W64.to_uint np{2}))
        ==>
        inzp(W256.to_uint res{1}) = inzpRep4List (load_array4 Glob.mem{2} (W64.to_uint _qp))     /\
        res{2} = W64.zero].
proof.
    proc *. inline M_ref4.jade_scalarmult_curve25519_amd64_ref4_base. wp. sp.
    call (eq_spec_impl_scalarmult_base_ptr_ref4 mem _qp _np). skip. done.
qed.
