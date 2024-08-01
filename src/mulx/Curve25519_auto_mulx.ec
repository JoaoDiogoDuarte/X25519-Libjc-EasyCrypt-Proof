require import Int StdOrder Ring IntDiv Bool List Real BitEncoding.
require import Zp_25519 W64limbs Zplimbs Curve25519_Spec Curve25519_Operations Curve25519_Procedures Curve25519_mulx.

from Jasmin require import JWord JWord_array JModel JUtils.

import Zp Curve25519_Procedures Curve25519_Operations Curve25519_mulx Array4 Array32 Ring.IntID StdOrder.IntOrder Array4.

(* Probably needs to be moved elsewhere, such as W64limbs *)

(** step 0 : add sub mul sqr - all done by auto **)

equiv eq_spec_impl_add_rrs_mulx : CurveProcedures.add ~ M_mulx.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sub_rrs_mulx : CurveProcedures.sub ~ M_mulx.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_spec_impl_sub_rsr_mulx : CurveProcedures.sub ~ M_mulx.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

(* inline mul4_c0 mul4_c1 mul4_c2 mul4_c3 *)

equiv eq_spec_impl_mul_a24_mulx : CurveProcedures.mul_a24 ~ M_mulx.__mul4_a24_rs:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul_rsr_mulx : CurveProcedures.mul ~ M_mulx.__mul4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul__rpr_mulx : CurveProcedures.mul ~ M_mulx.__mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl__sqr_rr_mulx : CurveProcedures.sqr ~ M_mulx.__sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl__sqr_rr_mulx_rev : M_mulx.__sqr4_rr ~ CurveProcedures.sqr:
    f{2}   = inzpRep4 f{1}
    ==>
    res{2} = inzpRep4 res{1}.
proof.
    proc *.
    admit.
qed.

(** step 3 : ith_bit **)
equiv eq_spec_impl_ith_bit_mulx : CurveProcedures.ith_bit ~ M_mulx.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\
    (ctr{1}                   = to_uint ctr{2})
    ==>
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.

lemma eq_to_bytes_mulx r:
  hoare [M_mulx.__tobytes4 :
      r = inzpRep4 f
      ==>
      pack4 (to_list res) = (W256.of_int (asint r))
  ].
proof.
    proc.
    admit.
qed.

lemma ill_eq_to_bytes_mulx : islossless M_mulx.__tobytes4 by islossless.

lemma ph_eq_to_bytes_mulx r:
  phoare [M_mulx.__tobytes4 :
      r = inzpRep4 f
      ==>
      pack4 (to_list res) = (W256.of_int (asint r))
  ] = 1%r.
proof.
    by conseq ill_eq_to_bytes_mulx (eq_to_bytes_mulx r).
qed.
