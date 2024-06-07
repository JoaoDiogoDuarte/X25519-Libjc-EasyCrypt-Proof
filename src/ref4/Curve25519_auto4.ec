require import Int Bool Zp_25519 List.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Ref4.
require import W64limbs.

from Jasmin require import JWord JWord_array.

import Zp_25519 Curve25519_Spec Curve25519_Hop2 Curve25519_Ref4 Array4 Array32.

(* Probably needs to be moved elsewhere, such as W64limbs *)

(** step 0 : add sub mul sqr - all done by auto **)

equiv eq_h4_add_rrs_ref4 : MHop2.add ~ M_ref4.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof. 
    proc.  
    admit.
qed.

equiv eq_h4_sub_rrs_ref4 : MHop2.sub ~ M_ref4.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. 
    admit.
qed.

equiv eq_h4_mul_a24_rs_ref4 : MHop2.mul_a24 ~ M_ref4.__mul4_a24_rs:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. 
    admit.
qed.

equiv eq_h4_mul_rss_ref4 : MHop2.mul ~ M_ref4.__mul4_rss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. 
    admit.
qed.

equiv eq_h4_sqr_ref4 : MHop2.sqr ~ M_ref4.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. 
    admit.
qed.


equiv eq_h4_sub_rsr_ref4 : MHop2.sub ~ M_ref4.__sub4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_pp_ref4 : MHop2.mul ~ M_ref4._mul4_pp:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_ss__ref4 : MHop2.sqr ~ M_ref4.__sqr4_ss:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. 
    
    admit.
qed.


equiv eq_h4_sqr_rs_ref4 : MHop2.sqr ~ M_ref4.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_p_ref4 : MHop2.sqr ~ M_ref4._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.



(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519_ref4 : MHop2.decode_scalar ~ M_ref4.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==> 
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}. 
proof.
    admit. (* AUTO *)
qed.


(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate_ref4 : MHop2.decode_u_coordinate ~ M_ref4.__decode_u_coordinate4:
    inzp (W256.to_uint u'{1}) = inzpRep4 u{2}
    ==> 
    res{1}                    = inzpRep4 res{2}.
proof.
    admit. (* AUTO MSB already 0 -  ask tiago *)
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit_ref4 : MHop2.ith_bit ~ M_ref4.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  
    (ctr{1}                   = to_uint ctr{2}) 
    ==> 
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10 : encode point **)
equiv eq_h4_encode_point_ref4 : MHop2.encode_point ~ M_ref4.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\ 
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.
    

