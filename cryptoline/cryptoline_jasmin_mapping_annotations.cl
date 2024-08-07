# comparison with __add4_rrs(reg u64[4] f, stack u64[4] g) -> reg u64[4]
(*
    inline int i;
    reg bool cf;
    reg u64[4] h;
    reg u64 z;
*)


# 4 limb addition with carry
proc main (uint64 a0, uint64 a1, uint64 a2, uint64 a3,
           uint64 b0, uint64 b1, uint64 b2, uint64 b3) =
{
  true
&&
  true
}



# values from gas output, moving inputs into said addresses
## not in jasmin code, but may be done implicitly
mov L0x7fffffffd970 a0;
mov L0x7fffffffd978 a1;
mov L0x7fffffffd980 a2;
mov L0x7fffffffd988 a3;

mov L0x7fffffffd990 b0;
mov L0x7fffffffd998 b1;
mov L0x7fffffffd9a0 b2;
mov L0x7fffffffd9a8 b3;

# rax will hold non determinant value
nondet rax@uint64;

# move first limb to registers r8 to r1
## functions as  h = #copy(f);
mov r8 L0x7fffffffd970;
mov r9 L0x7fffffffd978;
mov r10 L0x7fffffffd980;
mov r11 L0x7fffffffd988;



## zeroing out z is not done

# r8, carry = r8 + valueAtAddress L0x7fffffffd990
## cf, h[0] += g[0];
adds carry r8 r8 L0x7fffffffd990;

# r9, carry = r9 + valueAtAddress L0x7fffffffd998 + carry
## for i=1 to 4 { cf, h[i] += g[i] + cf; }
adcs carry r9 r9 L0x7fffffffd998 carry;
adcs carry r10 r10 L0x7fffffffd9a0 carry;
adcs carry r11 r11 L0x7fffffffd9a8 carry;

# substract with borrow, rax, carry = rax - rax + carry
## _, z -= z - cf;

ghost carryo@bit:
      carryo = carry && carryo = carry;

sbbs carry rax rax rax carry;

assert true && carry = carryo;
assume carry = carryo && true;

and rax@uint64 rax 0x26@uint64;

assert true && or [and [carry = 0@1, rax=0@64], and [carry = 1@1, rax=0x26@64]];
assume rax = carry*0x26 && true;



# begin second round of addition, so r8 = r8 + 38 or r8 = r8
## cf, h[0] += z;
adds carry r8 r8 rax;
# propegate carry through limbs r9 and r11
## for i=1 to 4 { cf, h[i] += 0 + cf; }

adcs carry r9 r9 0@uint64 carry;
adcs carry r10 r10 0@uint64 carry;
# move r9, which has its carry dealt with, to the result address
mov L0x7fffffffd9b8 r9;
adcs carry r11 r11 0@uint64 carry;
# move r10, which has its carry dealt with, to the result address
mov L0x7fffffffd9c0 r10;

ghost carryoo@bit:
      carryoo = carry && carryoo = carry;

# any other carries? same as above
## _, z -= z - cf;
sbbs carry rax rax rax carry;

assert true && carry = carryoo;
assume carry = carryoo && true;


# move r11 to result address
mov L0x7fffffffd9c8 r11;
# either 0 or -38
## z &= 38;
and rax@uint64 rax 0x26@uint64;

assert true && or [and [carry = 0@1, rax=0@64], and [carry = 1@1, rax=0x26@64]];
assume rax = carry*0x26 && true;

# final propegation, carry should be 0
## h[0] += z;
adds carry r8 r8 rax;

(* NOTE: cannot carry *)
assert true && carry=0@1;
assume carry=0 && true;

# move r8 to result address
mov L0x7fffffffd9b0 r8;

# move results into registers
## return h;
mov r0 L0x7fffffffd9b0;
mov r1 L0x7fffffffd9b8;
mov r2 L0x7fffffffd9c0;
mov r3 L0x7fffffffd9c8;


{
  eqmod (limbs 64 [r0, r1, r2, r3])
         (limbs 64 [a0, a1, a2, a3] + limbs 64 [b0, b1, b2, b3])
         ((2**255)-19)
&&
    true
  # the addition of both limbs are congruent 2^255 - 19
}
