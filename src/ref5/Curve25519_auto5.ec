require import Int Bool Zp_25519 List.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Ref5.
require import W64limbs.

from Jasmin require import JWord JWord_array.

import Zp_25519 Curve25519_Spec Curve25519_Hop2 Curve25519_Ref5 Array4 Array32 Array5.

(** ref5 **)



equiv eq_h4_add_rrs_ref5 : MHop2.add ~ M_ref5.__add5_rrs:
   f{1}   = inzpRep5 f{2} /\
   g{1}   = inzpRep5 g{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_add_sss_ref5 : MHop2.add ~ M_ref5.__add5_sss:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 gs{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_add_ssr_ref5 : MHop2.add ~ M_ref5.__add5_ssr:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 g{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.



equiv eq_h4_sub_rss_ref5 : MHop2.sub ~ M_ref5.__sub5_rrs:
   f{1}   = inzpRep5 f{2} /\
   g{1}   = inzpRep5 gs{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_sss_ref5 : MHop2.sub ~ M_ref5.__sub5_sss:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 gs{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_rsr_ref5 : MHop2.sub ~ M_ref5.__sub5_rsr:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 g{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_ssr_ref5 : MHop2.sub ~ M_ref5.__sub5_ssr:
   f{1}   = inzpRep5 fs{2} /\
   g{1}   = inzpRep5 g{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_rss_ref5 : MHop2.mul ~ M_ref5.__mul5_rss:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_sss_ref5 : MHop2.mul ~ M_ref5.__mul5_sss:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_pp_ref5 : MHop2.mul ~ M_ref5._mul5_pp:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_ss_ref5 : MHop2.mul ~ M_ref5._mul5_ss_:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_rs_ref5 : MHop2.sqr ~ M_ref5.__sqr5_rs:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss_ref5 : MHop2.sqr ~ M_ref5.__sqr5_ss:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_p_ref5 : MHop2.sqr ~ M_ref5._sqr5_p:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_ss__ref5 : MHop2.sqr ~ M_ref5._sqr5_ss_:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_s_ref5 : MHop2.sqr ~ M_ref5._sqr5_s_:
    f{1}   = inzpRep5 x{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


(** step 1_ref5 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519_ref5 : MHop2.decode_scalar ~ M_ref5.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==> 
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}. 
proof.
    admit. (* AUTO *)
qed.


(** step 2_ref5 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate_ref5 : MHop2.decode_u_coordinate ~ M_ref5.__decode_u_coordinate5:
    inzp (W256.to_uint u'{1}) = inzpRep4 t{2}
    ==> 
    res{1}                    = inzpRep5 res{2}.
proof.
    admit. (* AUTO MSB already 0 -  ask tiago *)
qed.

(** step 3_ref5 : ith_bit **)
equiv eq_h4_ith_bit_ref5 : MHop2.ith_bit ~ M_ref5.__ith_bit:
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  
    (ctr{1}                   = to_uint ctr{2}) 
    ==> 
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10_ref5 : encode point **)
equiv eq_h4_encode_point_ref5 : MHop2.encode_point ~ M_ref5.__encode_point5:
    x2{1}                 = inzpRep5 x2{2} /\ 
    z2{1}                 = inzpRep5 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.
