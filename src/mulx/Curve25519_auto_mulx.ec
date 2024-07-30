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

(** step 1 : decode_scalar_25519 **)
equiv eq_spec_impl_decode_scalar_25519_mulx : CurveProcedures.decode_scalar ~ M_mulx.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==>
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}.
proof.
    admit. (* AUTO *)
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


(** step 10 : encode point **)
equiv eq_spec_impl_encode_point_mulx : CurveProcedures.encode_point ~ M_mulx.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.
