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


equiv eq_spec_impl_ith_bit_ref4 : CurveProcedures.ith_bit ~ M_ref4.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\
    (ctr{1}                   = to_uint ctr{2})
    ==>
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


lemma eq_to_bytes_ref4 r:
  hoare [M_ref4.__tobytes4 :
      r = inzpRep4 f
      ==>
      pack4 (to_list res) = (W256.of_int (asint r))
  ].
proof.
    proc.
    admit.
qed.

lemma ill_eq_to_bytes_ref4 : islossless M_ref4.__tobytes4 by islossless.

lemma ph_eq_to_bytes_ref4 r:
  phoare [M_ref4.__tobytes4 :
      r = inzpRep4 f
      ==>
      pack4 (to_list res) = (W256.of_int (asint r))
  ] = 1%r.
proof.
    by conseq ill_eq_to_bytes_ref4 (eq_to_bytes_ref4 r).
qed.
