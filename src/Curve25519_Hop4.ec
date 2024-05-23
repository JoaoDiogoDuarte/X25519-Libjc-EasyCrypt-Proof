require import AllCore Bool List Int IntDiv CoreMap Real Zp_25519 Ring EClib Array4.
from Jasmin require import JModel JWord_array.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Hop3.
require import Curve25519_ref4.
import Zp_25519 ZModpRing.
import Curve25519_Spec Curve25519_Hop1 Curve25519_Hop2 Curve25519_ref4 Array4.
require import W64limbs.

(** representation : move to another file/use rep3/5 **)
type Rep4 = W64.t Array4.t.
op valRep4  (x : Rep4) : int = val_limbs64 (Array4.to_list x).
op inzpRep4 (x : Rep4) : zp  = inzp (valRep4 x) axiomatized by inzpRep4E.
abbrev zpcgrRep4 (x : Rep4) (z : int) : bool = zpcgr (valRep4 x) z.
(** ************************************* **)

(** step 0 : add sub mul sqr **)

equiv eq_h4_add : MHop2.add ~ M.__add4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
 admit.
qed.

equiv eq_h4_sub : MHop2.sub ~ M.__sub4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_a24 : MHop2.mul_a24 ~ M.__mul4_a24_rs:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
 admit.
qed.

equiv eq_h4_mul_rss : MHop2.mul ~ M.__mul4_rss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr : MHop2.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_h4_add_ssr : MHop2.add ~ M.__add4_ssr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_add_sss : MHop2.add ~ M.__add4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_add_rrs : MHop2.add ~ M.__add4_rrs:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
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
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sub_sss : MHop2.sub ~ M.__sub4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_a24_ss : MHop2.mul_a24 ~ M.__mul4_a24_ss:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_sss : MHop2.mul ~ M.__mul4_sss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_mul_pp : MHop2.mul ~ M.__mul4_pp:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_mul_sss : MHop2.mul ~ M.__mul4_s_:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.


equiv eq_h4_sqr_rs : MHop2.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_ss : MHop2.sqr ~ M.__sqr4_ss:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_ss_ : MHop2.sqr ~ M.__sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

equiv eq_h4_sqr_p : MHop2.sqr ~ M._sqr4_p:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
proc.
admit.
qed.

(** loading, storing and init **)

equiv eq_h4_tobytes :
    MHop2.tobytes ~ M.__tobytes4:
true ==> true.
proof.
  admit.
qed

equiv eq_h4_load :
    MHop2.load ~ M.__load4:
true ==> true.
proof.
  admit.
qed

equiv eq_h4_store :
    MHop2.store ~ M.__store4:
true ==> true.
proof.
  admit.
qed

equiv eq_init_point4 :
    MHop2.init_points ~ M.__init_points4 :
true ==> true.
proof
  admit.
qed.


(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519 :
  MHop2.decode_scalar_25519 ~ M.__decode_scalar:
  true ==> true.
proof.
admit.
qed.

(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate :
  MHop2.decode_u_coordinate ~ M.__decode_u_coordinate4:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_decode_u_coordinate_base :
  MHop2.decode_u_coordinate_base~ M.__decode_u_coordinate_base4:
  true ==> true.
proof.
admit.
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit :
  MHop2.ith_bit ~ M.__ith_bit:
  true ==> true.
proof.
admit.
qed.

(** step 4 : cswap **)
equiv eq_h4_cswap :
  MHop2.cswap ~ M.__cswap4:
  x2{1}         = inzpRep4 x2{2}  /\
  z2{1}         = inzpRep4 z2r{2} /\
  x3{1}         = inzpRep4 x3{2}  /\
  z3{1}         = inzpRep4 z3{2}  /\
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
  rcondt {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64 /=. smt(@W64).
    rewrite !mask_set /=.
    have lxor1 : forall (x1 x2:W64.t),  x1 `^` (x2 `^` x1) = x2.
      move=> *. rewrite xorwC -xorwA xorwK xorw0 //.
    have lxor2 : forall (x1 x2:W64.t),  x1 `^` (x1 `^` x2) = x2.
      move=> *. rewrite xorwA xorwK xor0w //. 
  rewrite !lxor1 !lxor2.
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
             congr. apply Array4.ext_eq. smt(@Array4).
  rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. smt(@W64).
    rewrite !mask_not_set !andw0 !xorw0.
    smt(@Array4).
qed.

(** step 5 : add_and_double **)
equiv eq_h4_add_and_double :
  MHop2.add_and_double ~ M.__add_and_double4:
  init{1} = inzpRep4 init{2} /\
  x2{1}   = inzpRep4 x2{2}   /\
  z2{1}   = inzpRep4 z2r{2}  /\
  x3{1}   = inzpRep4 x3{2}   /\
  z3{1}   = inzpRep4 z3{2}
  ==>
  res{1}.`1 = inzpRep4 res{2}.`1 /\
  res{1}.`2 = inzpRep4 res{2}.`2 /\
  res{1}.`3 = inzpRep4 res{2}.`3 /\
  res{1}.`4 = inzpRep4 res{2}.`4.
proof.
proc => /=.
 admit.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_h4_montgomery_ladder_step :
 MHop2.montgomery_ladder_step ~ M.__montgomery_ladder_step4:
 true ==> true.
proof.
admit.
qed.   

(** step 7 : montgomery_ladder **)
equiv eq_h4_montgomery_ladder :
  MHop2.montgomery_ladder ~ M.__montgomery_ladder4 :
  true ==> true.
proof.
admit.
qed.

 (** step 8 : iterated square, may be error in variable names, ened to chec  **)
equiv eq_h4_it_sqr :
 MHop2.it_sqr ~ M._it_sqr4_s_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   i{1}            <=   W64.modulus   /\
    2              <=   i{1}          /\
   i{1} %% 2        =   0
   ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
(*
  while (f{1}            =    inzpRep4 r{2}            /\ 
         i{1}            =    to_uint i{2}             /\
         i{1}            <=   W64.modulus              /\
         0               <=   i{1}                     /\
         i{1}            %%   2 = 0 /\
         r{2} = (i{2} = W64.zero)).
  swap 2 3 3. wp. conseq(_: _ ==> f{1} = inzpRep4 f{2}).
  move=> &1 &2 [#] ????? ->> ?? ??? /=.
    rewrite /DEC_64 /rflags_of_aluop_nocf64 /ZF_of_w64 => /=.
    progress.
    smt(@W64). move : H1; smt(). smt(). smt(). smt(@W64). smt(@W64).
  by do 2! call eq_h4_sqr; skip; done.
  swap 3 4 4. wp. conseq(_: _ ==> f{1} = inzpRep4 f{2}).
  move=> &1 &2 [#] /= ->> ->> ??? ?? ->> /=.
    rewrite /DEC_64 /rflags_of_aluop_nocf64 /ZF_of_w64 => /=.
    progress.
    smt(@W64). move : H1; smt(). smt(). smt(). smt(@W64). smt(@W64).
  by do 2! call eq_h4_sqr; wp; skip; done.
  *)
admit.
qed.

equiv eq_h4_it_sqr_p :
 MHop2.it_sqr ~ M._it_sqr4_p:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   i{1}            <=   W64.modulus   /\
    2              <=   i{1}          /\
   i{1} %% 2        =   0
   ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.
admit.
qed.
(** step 9 : invert **)
equiv eq_h4_invert :
  MHop2.invert ~ M.__invert4 : 
     z1'{1} = inzpRep4 fs{2}
  ==> res{1} = inzpRep4 res{2}.
proof.
proc.
  admit.
qed.

equiv eq_h4_it_sqr_ss_ :
 MHop2.it_sqr ~ M._it_sqr4_ss_:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   i{1}            <=   W64.modulus   /\
    2              <=   i{1}          /\
   i{1} %% 2        =   0
   ==>
   res{1} = inzpRep4 res{2}.
proof.
  proc.

(** step 10 : encode point **)
equiv eq_h4_encode_point : 
  MHop2.encode_point ~ M.__encode_point4:
  true ==> true.
proof.
admit.
qed.

(** step 11 : scalarmult **)

equiv eq_h4_scalarmult_internal :
  MHop2.scalarmult_internal ~ M.__curve25519_internal_ref4:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult :
  MHop2.scalarmult ~ M._curve25519_ref4:
  true ==> true.
proof.
admit.
qed.


equiv eq_h4_scalarmult_ptr :
  MHop2.scalarmult ~ M.__curve25519_ref4_ptr:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_base :
  MHop2.scalarmult_base ~ M._curve25519_ref4_base:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_base_ptr :
  MHop2.scalarmult_base ~ M._curve25519_ref4_base_ptr:
  true ==> true.
proof.
admit.
qed.


equiv eq_h4_scalarmult_jade :
  MHop2.scalarmult_jade ~ M.jade_scalarmult_curve25519_amd64_ref4:
  true ==> true.
proof.
admit.
qed.

equiv eq_h4_scalarmult_jade_base :
  MHop2.scalarmult_jade_base ~ M.jade_scalarmult_curve25519_amd64_ref4_base:
  true ==> true.
proof.
admit.
qed.
