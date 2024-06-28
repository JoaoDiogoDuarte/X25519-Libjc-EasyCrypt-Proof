require import Int StdOrder Ring IntDiv Bool Zp_25519 List Real.
require import Curve25519_Spec.
require import Curve25519_Hop1.
require import Curve25519_Hop2.
require import Curve25519_Ref4.
require import W64limbs.
require import StdOrder.
from Jasmin require import JWord JWord_array JModel JUtils.

import Zp_25519 Curve25519_Spec Curve25519_Hop2 Curve25519_Ref4 Array4 Array32 Ring.IntID StdOrder.IntOrder Array4.

op modulus : int = W64.modulus ^ 4.

lemma modulusE: modulus = W64.modulus ^ 4 by rewrite /modulus.

type limb = W64.t.


module GenericOperations = {
    proc addn (a : int, b : int) : bool * int = {
        var c : bool;
        var r : int;

        c <- modulus <= a + b;
        r <- (a + b) %% modulus;

        return (c, r);
    }
    
    proc maskOnCarry (m: int, r: W64.t, cf: bool): W64.t = {
        (cf, r) <- subc r r cf;
        r <- r `&` W64.of_int m;
        return r;
    }
    
    proc addcR (a b: Rep4, c: bool): bool * Rep4 = {
        var r: Rep4;
        var i, x;
        r <- witness;
        i <- 0;
        while (i < 4) {
            (c, x) <- addc a.[i] b.[i] c;
            r.[i] <- x;
            i <- i + 1;
        }
        return (c,r);
      }
      
    proc addcR2 (a b: Rep4): bool * Rep4 =     {
        var i, x, c;
        c <- false;
        i <- 0;
        
        while (i < 4) {
            (c, x) <- addc a.[i] b.[i] c;
            a.[i] <- x;
            i <- i + 1;
        }
        return (c,a);
    }
    
    proc addcR3 (a: Rep4, z: limb, c: bool): bool * Rep4 =     {
        var i : int;
        var x : limb; 
        
        i <- 0;

        (c, x) <- addc a.[i] z c;
        a.[0] <- x;
        i <- 1;
        while (i < 4) {
            (c, x) <- addc a.[i] W64.zero  c;
            a.[i] <- x;
            i <- i + 1;
        }
        return (c,a);
    }
    
    proc reduce_after_sum(h: Rep4, c : bool) : Rep4 = {
        var z : limb;
        var z0 : Rep4;
        z <- W64.zero;
        z <@ maskOnCarry(38, z, c);
        (c, h) <@ addcR3(h, z, false);
        z <@ maskOnCarry(38, z, c);
        h.[0] <- h.[0] + z;  
        return h;
    }
    
    
    proc addl (a b: Rep4) : Rep4 = {
        var h, z0 : Rep4;
        var z, tt : limb;    
        var c, t0 : bool;
        var i : int;
        h <- a;
        z <- W64.zero;
        
        (c, h) <@ addcR2(h, b);
        h <@ reduce_after_sum(h, c);
  
        return h;
    }

}.


equiv eq_h4_add_rrs_proc : M_ref4.__add4_rrs ~ GenericOperations.addl:
   f{1}   =  a{2} /\
   g{1}   =  b{2}
   ==> 
   res{1} = res{2}. 
proof.
    proc. inline *. do 2! unroll for{2} ^while. do 2! unroll for{1} ^while.   
    wp. skip => />. 
qed.


(** step 0 : add sub mul sqr - all done by auto **)

lemma lex_lt x1 x2 m y1 y2:
    0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
    (y1*m + x1 < y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 < x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_le x1 x2 m y1 y2:
    0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
    (y1*m + x1 <= y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 <= x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_eq x1 x2 m y1 y2:
    0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
    (y1*m + x1 = y2*m + x2) = (y1 = y2 /\ x1 = x2)
by smt().

lemma modz_pow (a b d: int):
 0 <= b => a ^ b %% d = (a %% d) ^ b %% d.
proof.
    elim/natind: b.
    by move => n *; rewrite (_:n=0) 1:/# !expr0.
    move=> n Hn IH H.
    rewrite !exprS 1..2://.
    by rewrite eq_sym -modzMmr -IH 1:// modzMmr modzMml.
qed.


lemma addcP' (x y: limb, c :  bool):
    to_uint (W64.addc x y c).`2 = to_uint x + to_uint y + b2i c - b2i (carry_add x y c) * W64.modulus.
proof.
    rewrite addcE /= /carry_add.
    case: (W64.modulus <= to_uint x + to_uint y + b2i c) => E.
    rewrite to_uintD of_uintK b2i1 /= (modz_small (b2i c)); first smt(ge2_modulus).
    rewrite to_uintD modzDml -(modzMDr (-1)) modz_small //=.
    case: c E; rewrite /b2i /=; move: W64.to_uint_cmp; smt(). rewrite !b2i0 => />.  
    smt(W64.to_uintD_small W64.of_uintK modz_small W64.to_uint_cmp ge2_modulus bound_abs).
qed.

lemma addcPP (a b: limb, c: bool):
    to_uint (W64.addc a b c).`2 = to_uint a + to_uint b + b2i c - b2i (W64.addc a b c).`1 * W64.modulus.
proof.
    by rewrite addcP' /addc /= /carry_add.
qed.


op dig (x: Rep4) (i:int): int = to_uint x.[i]*W64.modulus^i.

lemma digE (x: Rep4) (i:int): dig x i = to_uint x.[i]*W64.modulus^i by rewrite /dig.
hint simplify digE.

(* BigInt value for a prefix of an array *)
op valRep4_partial (k:int) (x:Rep4): int = 
    foldr Int.(+) 0 (map (dig x) (range 0 k)).

op valRep4_full (x : Rep4) : int = 
    valRep4_partial 4 x.

lemma eq_valRep4_full (x : Rep4):
     valRep4_full x = valRep4 x.
proof.
    by rewrite /valRep4_full valRep4E /val_digits /valRep4_partial  /range /to_list /mkseq -iotaredE => />; ring.
qed.

lemma valRep4_partialN (k: int,  x : Rep4): 
    k <= 0 => valRep4_partial k x = 0.
proof. 
    move => ?; rewrite /valRep4_partial /range -iotaredE => />. smt(@List). 
qed.

lemma valRep4_partial0 (x: Rep4): 
    valRep4_partial 0 x = 0.
proof. 
    by rewrite valRep4_partialN. 
qed.

(* less generic, but we only care about 4 limbs *)
lemma valRep4_partialS (k: int, x : Rep4): 
    0 <= k <= 4 => valRep4_partial (k+1) x = dig x k + valRep4_partial k x.
proof. 
    case: (k=0) => E.
    + by rewrite E /= /valRep4_partial rangeS range_geq 1://. 
    case: (k=1) => E0.
    rewrite E0 /= /valRep4_partial /range -iotaredE => />. ring. 
    case: (k=2) => E1.
    rewrite E1 /= /valRep4_partial /range -iotaredE => />. ring. 
    case: (k=3) => E2.
    rewrite E2 /= /valRep4_partial /range -iotaredE => />. ring.
    case: (k=4) => E3.
    rewrite E3 /= /valRep4_partial /range -iotaredE => />. ring.
    auto => />. smt().
qed.

lemma valRep4_partial1 x: 
    valRep4_partial 1 x = dig x 0.
proof. 
    by rewrite -(add0z 1) valRep4_partialS 1:/# digE expr0 valRep4_partial0. 
qed.


lemma valRep4_partial_cmp (k : int,  x : Rep4): 0 <= k <= 4 =>  0 <= valRep4_partial k x < W64.modulus^k.
proof.
    case: (k=0) => E.
        + rewrite E valRep4_partial0 !expr0. smt().
    case: (k=1) => E1.
        + rewrite E1. rewrite /valRep4_partial /range -iotaredE => />. split. smt(W64.to_uint_cmp).
        + move => H. move: W64.to_uint_cmp x.[0]  => />. move => H0. smt().
    case: (k=2) => E2.
        + rewrite E2. rewrite /valRep4_partial /range -iotaredE => />. split. smt(W64.to_uint_cmp).
        + move => H. smt(@W64 @JUtils).
    case: (k=3) => E3.
        + rewrite E3. rewrite /valRep4_partial /range -iotaredE => />. split. smt(W64.to_uint_cmp).
        + move => H. smt(@W64 @JUtils).
    case: (k=4) => E4.
        + rewrite E4. rewrite /valRep4_partial /range -iotaredE => />. split. smt(W64.to_uint_cmp).
        + move => H. smt(@W64 @JUtils).
    auto => />. smt().
qed.

lemma valRep4_partial_ltb (k : int,  x y : Rep4,  b : bool):
    0 <= k <= 4 => valRep4_partial (k+1) x < valRep4_partial (k+1) y + b2i b
    = (to_uint x.[k] < to_uint y.[k] \/ x.[k]=y.[k] /\ 
      valRep4_partial k x < valRep4_partial k y + b2i b).
proof.
    move=> [?] ?; rewrite !valRep4_partialS // !digE.
    move: (W64.to_uint_cmp x.[k]) (W64.to_uint_cmp y.[k]) =>  *.
    case: b => E; rewrite ?b2i1 ?b2i0 => *.
    rewrite !ltzS lex_le ?expr_gt0 //; move: valRep4_partial_cmp W64.to_uint_eq; smt().
    by rewrite /= lex_lt ?expr_gt0 //; move: valRep4_partial_cmp W64.to_uint_eq; smt().
qed.

lemma valRep4_partial_setO k x i y:
    0 <= k <= i < 4 => valRep4_partial k x.[i <- y]%Array4 = valRep4_partial k x.
proof.
    elim/natind: k => /=.
    by move=> k *; rewrite (_:k=0) 1:/# !valRep4_partial0.
    move=> k Hk IH H; rewrite !valRep4_partialS //. smt(). smt(). rewrite !digE !get_setE 1:/# IH /#.
qed.


op carry_add_on_k (k : int, x y: Rep4, c:bool): bool =
    iteri k (fun i r => carry_add x.[i] y.[i] r) c.

lemma carry_add_on_k0 (x y: Rep4 , c: bool) : carry_add_on_k 0 x y c = c by rewrite /carry_add_on_k iteri0.

lemma carry_add_on_kS (k : int, x y: Rep4, c:bool):
    0 <= k => carry_add_on_k (k+1) x y c = (carry_add x.[k] y.[k] (carry_add_on_k k x y c)) 
        by move=> *; rewrite /carry_add_on_k iteriS.

lemma carry_add_on_kP (k : int, x y: Rep4, c:bool):
    0 <= k <= 4 =>
    b2i (carry_add_on_k k x y c) = (valRep4_partial k x + valRep4_partial k y + b2i c) %/ W64.modulus^k.
proof.
    move => [H] H0.
    case: (k = 0) => H1.
    rewrite /carry_add_on_k H1 !valRep4_partial0 iteri0 => />.
    case: (k = 1) => H2.
    rewrite /carry_add_on_k H2 !valRep4_partial1 iteri_red // iteri0 // !digE => />.
    rewrite /carry_add. 
    case (W64.modulus <= to_uint x.[0] + to_uint y.[0] + b2i c) => H3. 
    rewrite b2i1 => />. smt(@W64 @JUtils).
    rewrite b2i0 => />. smt(@W64 @JUtils).
    case: (k = 2) => H3.
    rewrite /carry_add_on_k H3 !/valRep4_partial iteri_red  // iteri_red => />.
    rewrite iteri0 // /range -iotaredE => />. 
    case (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c)) => H4.
    rewrite b2i1 => />. smt(@W64 @JUtils).
    rewrite b2i0 => />. smt(@W64 @JUtils).
    case: (k = 3) => H4.
    rewrite /carry_add_on_k H4 !/valRep4_partial iteri_red // iteri_red // iteri_red => />.
    rewrite iteri0 // /range -iotaredE => />. 
    case (carry_add x.[2] y.[2] (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c))) => H5.
    rewrite b2i1 => />. smt(@W64 @JUtils).
    rewrite b2i0 => />. smt(@W64 @JUtils).
    case: (k = 4) => H5.
    rewrite /carry_add_on_k H5 !/valRep4_partial iteri_red // iteri_red // iteri_red // iteri_red => />.
    rewrite iteri0 // /range -iotaredE => />. 
    case (carry_add x.[3] y.[3] (carry_add x.[2] y.[2] (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c)))) => H6.
    rewrite b2i1 => />. smt(@W64 @JUtils).
    rewrite b2i0 => />. smt(@W64 @JUtils).
    auto => />. smt(). 
qed.

lemma carry_add_on_kE (k : int,  x y : Rep4, c : bool):
    0 <= k <= 4 => carry_add_on_k k x y c = (W64.modulus^k <= valRep4_partial k x + valRep4_partial k y + b2i c).
proof.
    move => [H] H0.
    case: (k = 0) => H1.
    rewrite H1 /carry_add_on_k !valRep4_partial0 iteri0 // => />. smt().
    case (k = 1) => H2.
    rewrite H2 /carry_add_on_k /valRep4_partial /range -iotaredE iteri_red // iteri0 //.
    case (k = 2) => H3.
    rewrite H3 /carry_add_on_k /valRep4_partial /range -iotaredE iteri_red // iteri_red //  iteri0 // => />.
    case (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c)) => H4.
    smt(@W64 @JUtils). smt(@W64 @JUtils).
    case (k = 3) => H4.
    rewrite H4 /carry_add_on_k /valRep4_partial /range -iotaredE iteri_red // iteri_red // iteri_red // iteri0 // => />.
    case (carry_add x.[2] y.[2] (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c))) => H5.
    smt(@W64 @JUtils). smt(@W64 @JUtils).
    case (k = 4) => H5.
    rewrite H5 /carry_add_on_k /valRep4_partial /range -iotaredE iteri_red // iteri_red // iteri_red  // iteri_red // iteri0 // => />.
    case (carry_add x.[3] y.[3] (carry_add x.[2] y.[2] (carry_add x.[1] y.[1] (carry_add x.[0] y.[0] c)))) => H6.
    smt(@W64 @JUtils). smt(@W64 @JUtils).
    auto => />. smt().
qed.


lemma addcR_h aa bb cc:
  hoare [ GenericOperations.addcR:
          aa = a /\ bb = b /\ cc = c
          ==>
          res.`1 = modulus <=  valRep4_full aa + valRep4_full bb +  b2i cc
          /\ valRep4_full res.`2 = ( valRep4_full aa + valRep4_full  bb + b2i cc) %% modulus
        ].
proof.
    proc => /=.
    while (0 <= i <= 4 /\ a = aa /\ b = bb /\
        c = carry_add_on_k i aa bb cc /\
        valRep4_partial i r = valRep4_partial i aa + valRep4_partial i bb + b2i cc - b2i c * W64.modulus^i
    ).
    wp. skip => &hr [[[H H0]]] /> H1 H2.
    split; first smt().
    split.
    rewrite addcE !carry_add_on_kS /= // /carry_add.    
    rewrite !valRep4_partialS // !digE get_setE //= valRep4_partial_setO 1:/# H1.
    by rewrite addcP' !exprS // !/carry_add_on_k addcE !/carry_add /=; ring.
    wp; skip => />; auto => />.
    do split.
    + by rewrite carry_add_on_k0.
    + by rewrite !valRep4_partial0 // expr0 /#.
    move => H H0  H1  H2 H3 H5. split.
   
    move: valRep4_partial_cmp. smt(@JUtils).
    move: valRep4_partial_cmp. smt(@JUtils).
qed.

lemma addcR_ll: islossless GenericOperations.addcR.
proof.
    proc. unroll for ^while.
    islossless.
qed.

lemma addcR_ph aa bb cc:
 phoare [ GenericOperations.addcR:
          aa = a /\ bb = b /\ cc = c
          ==>
          res.`1 = modulus <=  valRep4_full aa + valRep4_full bb +  b2i cc
          /\ valRep4_full res.`2 = ( valRep4_full aa + valRep4_full  bb + b2i cc) %% modulus
        ] = 1%r.
proof. by conseq addcR_ll (addcR_h aa bb cc). qed.

equiv addc_spec:
 GenericOperations.addcR2 ~ GenericOperations.addn:
  valRep4_full a{1} = a{2} /\ valRep4_full b{1} =  b{2}
  ==> res{1}.`1=res{2}.`1 /\ valRep4_full res{1}.`2 =  res{2}.`2.
proof.
    transitivity 
    GenericOperations.addcR
    ( ={a,b} /\ !c{2} ==> ={res} )
    ( valRep4_full a{1} =  a{2} /\ valRep4_full b{1} =  b{2} /\ !c{1}
    ==> res{1}.`1 = res{2}.`1 /\ valRep4_full res{1}.`2 = res{2}.`2 ).
    + by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
    + by move=> /> *.
    + proc. simplify.
    unroll {2} 3; rcondt {2} 3; first by auto.
    unroll {1} 3; rcondt {1} 3; first by auto.
    exlim a{1}, b{1} => aa bb.
    while (={i,b} /\ 1 <= i{2} <= 4 /\
         (c,aa){1}=(c,a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k]) /\
         (forall k, i{2} <= k < 4 => a{1}.[k] = aa.[k])).
    wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
    split => *; first smt().
    split => *; first smt().
    split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?. by rewrite !set_eqiE /#. by rewrite !set_neqiE /#.
    move=> k Hk1 Hk2. by rewrite set_neqiE /#.
    wp. skip => /> &1. 
    move=> Hc; split => *. 
    split => k *.
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
    by rewrite set_neqiE /#.
    by apply ext_eq; smt().
    + proc. simplify.
    transitivity {1}
        { (c,r) <@ GenericOperations.addcR(a,b,c); }
        ( ={a,b,c} ==> ={c,r} )
        (  valRep4_full a{1} = a{2} /\ valRep4_full b{1}=  b{2} /\ !c{1} ==> ={c} /\ valRep4_full r{1} =  r{2} ).
    by move=> /> &1 &2; exists a{1} b{1} false.
  + by auto.
  + by inline *; sim.
  + ecall {1} (addcR_ph a{1} b{1} c{1}); wp; skip => /> &1 &2 &m H0 Hc  /=.
qed.

lemma maskOnCarry_h mask _r _cf:
 hoare [ GenericOperations.maskOnCarry :
         _cf=cf /\ mask=m /\ _r=r ==> res = if _cf then W64.of_int mask else W64.zero ].
proof.
    proc; simplify.
    wp; skip => />.
    have ->: (subc _r _r _cf).`2 = if _cf then W64.onew else W64.zero.
    rewrite /subc /=.
    have ->: _r - (_r + W64.of_int (b2i _cf)) = -W64.of_int (b2i _cf) by ring.
    case: _cf => E.
    by rewrite b2i1 minus_one.
    by rewrite b2i0; ring.
    case: _cf => Ecf.
    by rewrite W64.and1w.
    by rewrite W64.and0w.
qed.

lemma maskOnCarry_ll: islossless GenericOperations.maskOnCarry.
proof. by islossless. qed.

lemma valRep4mod (x: Rep4) :
    valRep4_full x %% modulus^4 = valRep4_full x.
    rewrite modz_small !/valRep4_full !/valRep4_partial /range -iotaredE => />.
    split. smt(@JUtils).
    rewrite modulusE => />.  
    smt(@W64 @JUtils).
qed.

lemma maskOnCarry_ph (mask: int, _r: limb,  _cf: bool):
 phoare [ GenericOperations.maskOnCarry :
         mask=m /\ _cf=cf /\ r = _r ==> res = if _cf then W64.of_int mask else W64.zero ] = 1%r.
proof. by conseq maskOnCarry_ll (maskOnCarry_h mask _r _cf). qed.

lemma reduce_addition (f : Rep4, cf : bool) : 
    hoare [GenericOperations.reduce_after_sum : 
           f = h  /\ cf = c /\ c = false ==>  valRep4_full res = if (addc_carry f.[3] W64.zero (addc_carry f.[2] W64.zero (addc_carry f.[1] W64.zero (addc_carry f.[0] W64.zero false)))) then reduce (valRep4_full f) else valRep4_full f]. 
proof.
    proc. simplify. wp.
    ecall (maskOnCarry_h 38 z c).
    inline 3.
    unroll for ^while. wp. simplify.
    ecall (maskOnCarry_h 38 z c).
    wp. skip => />.
    case (addc_carry f.[3] W64.zero (addc_carry f.[2] W64.zero (addc_carry f.[1] W64.zero (addc_carry f.[0] W64.zero false)))) => C.
    smt(@W64). 
    smt(@W64 @Array4).
qed.
    
equiv eq_h4_add_rrs_ref4 : MHop2.add ~ M_ref4.__add4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 g{2}
   ==> 
   res{1} = inzpRep4 res{2}.
proof.
    
qed.

equiv eq_h4_sub_rrs_ref4 : MHop2.sub ~ M_ref4.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
 s  res{1} = inzpRep4 res{2}.
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
   proc.  
   
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
    

