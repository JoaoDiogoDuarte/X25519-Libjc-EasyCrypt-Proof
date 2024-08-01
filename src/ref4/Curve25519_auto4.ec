require import AllCore StdOrder IntDiv Bool List BitEncoding StdRing Pervasive Logic.
require import Zp_25519 W64limbs Zplimbs Curve25519_Spec Curve25519_Procedures Curve25519_Ref4 EClib.

from Jasmin require import JWord JWord_array JModel JUtils.

import Zp Curve25519_Procedures Curve25519_Ref4 Array4 Array32 StdOrder.IntOrder Array4 BitEncoding.BS2Int EClib.

equiv eq_spec_impl_add_rrs_ref4 : CurveProcedures.add  ~ M_ref4.__add4_rrs:
    f{1} = inzpRep4 f{2} /\
    g{1} = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc; simplify.
    admit.
qed.

equiv eq_spec_impl_sub_rrs_ref4 : CurveProcedures.sub ~ M_ref4.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sub_rsr_ref4 : CurveProcedures.sub ~ M_ref4.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul_a24_rs_ref4 : CurveProcedures.mul_a24 ~ M_ref4.__mul4_a24_rs:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_mul_rss_ref4 : CurveProcedures.mul ~ M_ref4.__mul4_rss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
   proc.
    admit.
qed.

equiv eq_spec_impl_mul_pp_ref4 : CurveProcedures.mul ~ M_ref4._mul4_pp:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_sqr_ref4 : CurveProcedures.sqr ~ M_ref4.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sqr_ss__ref4 : CurveProcedures.sqr ~ M_ref4.__sqr4_ss:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.

    admit.
qed.

equiv eq_spec_impl_sqr_rs_ref4 : CurveProcedures.sqr ~ M_ref4.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_sqr_p_ref4 : CurveProcedures.sqr ~ M_ref4._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

(** step 1 : decode_scalar_25519 **)
equiv eq_spec_impl_decode_scalar_25519_ref4 : CurveProcedures.decode_scalar ~ M_ref4.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==>
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}.
proof.
proc.
    admit. (* AUTO *)
qed.



(** step 3 : ith_bit **)
equiv eq_spec_impl_ith_bit_ref4 : CurveProcedures.ith_bit ~ M_ref4.__ith_bit :
    k'{1} = W32u8.pack32 (to_list k{2}) /\
    ctr{1}                   =  to_uint ctr{2}
    ==>
    res{1}                = res{2}.[0].
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10 : encode point **)
equiv eq_spec_impl_encode_point_ref4 : CurveProcedures.encode_point ~ M_ref4.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.
