require import Int Bool Zp_25519 List Zp_25519.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_ref4.
require import Curve25519_ref5.
require import W64limbs.

from Jasmin require import JWord JWord_array.

import Zp_25519 Curve25519_Spec Curve25519_Hop2 Curve25519_ref4 Array4 Array32 Array5.

(* Probably needs to be moved elsewhere, such as W64limbs *)

(** step 0 : add sub mul sqr - all done by auto **)

equiv eq_h4_add : MHop2.add ~ M.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof. 
    proc.  
    admit.
qed.

equiv eq_h4_sub : MHop2.sub ~ M.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a24 : MHop2.mul_a24 ~ M.__mul4_a24_rs:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_rss : MHop2.mul ~ M.__mul4_rss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr : MHop2.sqr ~ M.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_h4_add_ssr : MHop2.add ~ M.__add4_ssr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_add_sss : MHop2.add ~ M.__add4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_add_rrs : MHop2.add ~ M.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_ssr : MHop2.sub ~ M.__sub4_ssr:
    f{1} = inzpRep4 fs{2} /\
    g{1} = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_rsr : MHop2.sub ~ M.__sub4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_sss : MHop2.sub ~ M.__sub4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a24_ss : MHop2.mul_a24 ~ M.__mul4_a24_ss:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_sss : MHop2.mul ~ M.__mul4_sss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_pp : MHop2.mul ~ M._mul4_pp:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_ss : MHop2.mul ~ M._mul4_ss_:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_rs : MHop2.sqr ~ M.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss : MHop2.sqr ~ M._sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss_ : MHop2.sqr ~ M.__sqr4_ss:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_s_ : MHop2.sqr ~ M._sqr4_s_:
    f{1}   = inzpRep4 x{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_p : MHop2.sqr ~ M._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519 : MHop2.decode_scalar ~ M.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep4 k{2}
    ==> 
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}. 
proof.
    admit. (* AUTO *)
qed.


(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate : MHop2.decode_u_coordinate ~ M.__decode_u_coordinate4:
    inzp (W256.to_uint u'{1}) = inzpRep4 u{2}
    ==> 
    res{1}                    = inzpRep4 res{2}.
proof.
    admit. (* AUTO MSB already 0 -  ask tiago *)
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit : MHop2.ith_bit ~ M.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  
    (ctr{1}                   = to_uint ctr{2}) 
    ==> 
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10 : encode point **)
equiv eq_h4_encode_point : MHop2.encode_point ~ M.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\ 
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep4 res{2}.
proof.
    admit. (* AUTO *)
qed.

(** ref5 **)



equiv eq_h4_add_ref5 : MHop2.add ~ M_ref5.__add5_rrs:
    f{1}   = inzpRep5 f{2} /\
    g{1}   = inzpRep5 g{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof. 
    proc.  
    admit.
qed.

equiv eq_h4_sub_ref5 : MHop2.sub ~ M_ref5.__sub5_rrs:
   f{1}   = inzpRep5 f{2} /\
   g{1}   = inzpRep5 gs{2}
   ==>
   res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a25_r : MHop2.mul_a24 ~ M_ref5.__mul5_a25_rss:
    f{1}   = inzpRep5 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a25_s : MHop2.mul_a24 ~ M_ref5.__mul5_a25_rss:
    f{1}   = inzpRep5 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_rss : MHop2.mul ~ M_ref5.__mul5_rss:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr : MHop2.sqr ~ M_ref5.__sqr5_rs:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_h4_add_ssr : MHop2.add ~ M_ref5.__add5_ssr:
    f{1}   = inzpRep5 fs{2} /\
    g{1}   = inzpRep5 g{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_add_sss : MHop2.add ~ M_ref5.__add5_sss:
    f{1}   = inzpRep5 fs{2} /\
    g{1}   = inzpRep5 gs{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_add_rrs : MHop2.add ~ M_ref5.__add5_rrs:
    f{1}   = inzpRep5 f{2} /\
    g{1}   = inzpRep5 g{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sub_ssr : MHop2.sub ~ M_ref5.__sub5_ssr:
    f{1} = inzpRep5 fs{2} /\
    g{1} = inzpRep5 g{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_rsr : MHop2.sub ~ M_ref5.__sub5_rsr:
    f{1}   = inzpRep5 fs{2} /\
    g{1}   = inzpRep5 g{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sub_sss : MHop2.sub ~ M_ref5.__sub5_sss:
    f{1}   = inzpRep5 fs{2} /\
    g{1}   = inzpRep5 gs{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_a25_ss : MHop2.mul_a24 ~ M_ref5.__mul5_a25_ss:
    f{1}   = inzpRep5 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_sss : MHop2.mul ~ M_ref5.__mul5_sss:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_mul_pp : MHop2.mul ~ M_ref5._mul5_pp:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_mul_ss : MHop2.mul ~ M_ref5._mul5_ss_:
    f{1}   = inzpRep5 xa{2} /\
    g{1}   = inzpRep5 ya{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_h4_sqr_rs : MHop2.sqr ~ M_ref5.__sqr5_rs:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss : MHop2.sqr ~ M_ref5._sqr5_ss_:
    f{1} = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_ss_ : MHop2.sqr ~ M_ref5.__sqr5_ss:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_s_ : MHop2.sqr ~ M_ref5._sqr5_s_:
    f{1}   = inzpRep5 x{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_h4_sqr_p : MHop2.sqr ~ M_ref5._sqr5_p:
    f{1}   = inzpRep5 xa{2}
    ==>
    res{1} = inzpRep5 res{2}.
proof.
    proc.
    admit.
qed.


(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519 : MHop2.decode_scalar ~ M_ref5.__decode_scalar:
    inzp (W256.to_uint k'{1})  = inzpRep5 k{2}
    ==> 
    inzp (W256.to_uint res{1}) = inzpRep32 res{2}. 
proof.
    admit. (* AUTO *)
qed.


(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate : MHop2.decode_u_coordinate ~ M_ref5.__decode_u_coordinate5:
    inzp (W256.to_uint u'{1}) = inzpRep5 u{2}
    ==> 
    res{1}                    = inzpRep5 res{2}.
proof.
    admit. (* AUTO MSB already 0 -  ask tiago *)
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit : MHop2.ith_bit ~ M_ref5.__ith_bit :
    inzp (W256.to_uint k'{1}) = inzpRep32 k{2} /\  
    (ctr{1}                   = to_uint ctr{2}) 
    ==> 
    b2i res{1}                = to_uint res{2}.
proof.
    proc.
    admit. (* AUTO *)
qed.


(** step 10 : encode point **)
equiv eq_h4_encode_point : MHop2.encode_point ~ M_ref5.__encode_point5:
    x2{1}                 = inzpRep5 x2{2} /\ 
    z2{1}                 = inzpRep5 z2r{2}
    ==>
    inzp (to_uint res{1}) = inzpRep5 res{2}.
proof.
    admit. (* AUTO *)
qed.
