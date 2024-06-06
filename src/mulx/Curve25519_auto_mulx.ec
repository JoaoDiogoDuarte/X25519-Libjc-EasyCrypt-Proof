require import Int Bool Zp_25519 List.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_mulx.
require import W64limbs.

from Jasmin require import JWord JWord_array.

import Zp_25519 Curve25519_Spec Curve25519_Hop2 Curve25519_mulx Array4 Array32.

(* Probably needs to be moved elsewhere, such as W64limbs *)

(** step 0 : add sub mul sqr - all done by auto **)

equiv eq_h4_add_rrs_mulx : MHop2.add ~ M_mulx.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof. 
    proc.  
    admit.
qed.

equiv eq_h4_add_sss_mulx : MHop2.add ~ M_mulx.__add4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof. 
    proc.  
    admit.
qed.

equiv eq_h4_add_ssr_mulx : MHop2.add ~ M_mulx.__add4_ssr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof. 
    proc.  
    admit.
qed.


equiv eq_h4_sub_rrs_mulx : MHop2.sub ~ M_mulx.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_sss_mulx : MHop2.sub ~ M_mulx.__sub4_sss:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_rsr_mulx : MHop2.sub ~ M_mulx.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_ssr_mulx : MHop2.sub ~ M_mulx.__sub4_ssr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

(* inline mul4_c0 mul4_c1 mul4_c2 mul4_c3 *)

equiv eq_h4_mul_a24_mulx : MHop2.mul_a24 ~ M_mulx.__mul4_a24_rs:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a24_ss_mulx : MHop2.mul_a24 ~ M_mulx.__mul4_a24_ss:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_rsr_mulx : MHop2.mul ~ M_mulx.__mul4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul__rpr_mulx : MHop2.mul ~ M_mulx.__mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_rpr_mulx : MHop2.mul ~ M_mulx.__mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_rsr__mulx : MHop2.mul ~ M_mulx._mul4_rsr_:
    f{1}   = inzpRep4 _fs{2} /\
    g{1}   = inzpRep4 _g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul__ssr_mulx : MHop2.mul ~ M_mulx.__mul4_ssr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_sss_mulx : MHop2.mul ~ M_mulx.__mul4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_rss_mulx : MHop2.mul ~ M_mulx.__mul4_rss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr__rr_mulx : MHop2.sqr ~ M_mulx.__sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_rr_mulx : MHop2.sqr ~ M_mulx._sqr4_rr_:
    f{1}   = inzpRep4 _f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss_mulx : MHop2.sqr ~ M_mulx.__sqr4_ss:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_rs_mulx : MHop2.sqr ~ M_mulx.__sqr4_rs:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519_mulx : MHop2.decode_scalar ~ M_mulx.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==> 
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}. 
proof.
    admit. (* AUTO *)
qed.


(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate_mulx : MHop2.decode_u_coordinate ~ M_mulx.__decode_u_coordinate4:
    inzp (W256.to_uint u'{1}) = inzpRep4 u{2}
    ==> 
    res{1}                    = inzpRep4 res{2}.
proof.
    admit. (* AUTO MSB already 0 -  ask tiago *)
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit_mulx : MHop2.ith_bit ~ M_mulx.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  
    (ctr{1}                   = to_uint ctr{2}) 
    ==> 
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10 : encode point **)
equiv eq_h4_encode_point_mulx : MHop2.encode_point ~ M_mulx.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\ 
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.
    

