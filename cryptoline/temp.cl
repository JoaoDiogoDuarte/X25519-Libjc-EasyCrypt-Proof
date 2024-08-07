proc main (uint64 a0, uint64 a1, uint64 a2, uint64 a3,
           uint64 b0, uint64 b1, uint64 b2, uint64 b3) =
{
  true
  &&
  true
}

mov L0x7fffffffdb60 a0;
mov L0x7fffffffdb68 a1;
mov L0x7fffffffdb70 a2;
mov L0x7fffffffdb78 a3;

mov L0x7fffffffdb80 b0;
mov L0x7fffffffdb88 b1;
mov L0x7fffffffdb90 b2;
mov L0x7fffffffdb98 b3;

nondet rdx@uint64;
nondet rdi@uint64;

mov rax rdx;
mov rbp L0x7fffffffdb80;
mov rdx L0x7fffffffdb60;
mov rcx L0x7fffffffdb88;
mov r14 L0x7fffffffdb90;
mov r15 L0x7fffffffdb98;
mull rax r8 rdx rbp;

mov rdi 0@uint64;

clear carry;
clear overflow;

mull rbx r9 rdx rcx;
adcs carry r9 r9 rax carry;
mull rax r10 rdx r14;
adcs carry r10 r10 rbx carry;
mull r12 r11 rdx r15;
mov rdx L0x7fffffffdb68;
adcs carry r11 r11 rax carry;
mov L0x7fffffffdb10 r14;
adcs carry r12 r12 rdi carry;

assert true && carry = 0@1;
assume carry = 0 && true;

mull rbx rax rdx rbp;
adcs overflow r9 r9 rax overflow;
adcs carry r10 r10 rbx carry;
mull rbx rax rdx rcx;
adcs overflow r10 r10 rax overflow;
adcs carry r11 r11 rbx carry;
mull rbx rax rdx r14;
adcs overflow r11 r11 rax overflow;
adcs carry r12 r12 rbx carry;
mull r13 rax rdx r15;
mov rdx L0x7fffffffdb70;
adcs overflow r12 r12 rax overflow;
adcs carry r13 r13 rdi carry;
adcs overflow r13 r13 rdi overflow;

assert true && and [carry=0@1, overflow=0@1];
assume and [carry=0, overflow=0] && true;

mull rbx rax rdx rbp;
adcs carry r10 r10 rax carry;
adcs overflow r11 r11 rbx overflow;
mull rbx rax rdx rcx;
adcs carry r11 r11 rax carry;
adcs overflow r12 r12 rbx overflow;
mull rbx rax rdx r14;
adcs carry r12 r12 rax carry;
adcs overflow r13 r13 rbx overflow;
mull r14 rax rdx r15;
mov rdx L0x7fffffffdb78;
adcs carry r13 r13 rax carry;
adcs overflow r14 r14 rdi overflow;
adcs carry r14 r14 rdi carry;

assert true && and [carry=0@1, overflow=0@1];
assume and [carry=0, overflow=0] && true;

mull rbx rax rdx rbp;
adcs overflow r11 r11 rax overflow;
adcs carry r12 r12 rbx carry;
mull rbx rax rdx rcx;
adcs overflow r12 r12 rax overflow;
adcs carry r13 r13 rbx carry;
mull rbx rax rdx L0x7fffffffdb10;
adcs overflow r13 r13 rax overflow;
adcs carry r14 r14 rbx carry;
mull r15 rax rdx r15;

mov rdx 0x26@uint64;


adcs overflow r14 r14 rax overflow;
adcs carry r15 r15 rdi carry;
adcs overflow r15 r15 rdi overflow;

assert true && and [carry=0@1, overflow=0@1];
assume and [carry=0, overflow=0] && true;

mull rbx rax rdx r12;
adcs carry r8 r8 rax carry;
adcs overflow r9 r9 rbx overflow;
mull rbx rax rdx r13;
adcs carry r9 r9 rax carry;
adcs overflow r10 r10 rbx overflow;
mull rbx rax rdx r14;
adcs carry r10 r10 rax carry;
adcs overflow r11 r11 rbx overflow;
mull r12 rax rdx r15;
adcs carry r11 r11 rax carry;
adcs overflow r12 r12 rdi overflow;
adcs carry r12 r12 rdi carry;
mull dontcare r12 rdx r12;

assert true && and [dontcare = 0@64,carry=0@1,overflow=0@1];
assume and [dontcare = 0,carry=0,overflow=0] && true;

adds carry r8 r8 r12;
adcs carry r9 r9 0x0@uint64 carry;
adcs carry r10 r10 0x0@uint64 carry;
adcs carry r11 r11 0x0@uint64 carry;

ghost carryo@bit:
      carryo = carry && carryo = carry;

sbbs carry rax rax rax carry;

assert true && carry = carryo;
assume carry = carryo && true;

mov overflow carry;
not zero@bit carry;
and rax@uint64 rax 0x26@uint64;

assert true && or [ and [carry=0@1, rax=0@64],
                    and [carry=1@1, rax=0x26@64]];
assume rax = carry*0x26 && true;

adds carry r8 r8 rax;

assert true && carry=0@1;
assume carry=0 && true;

mov L0x7fffffffdba8 r9;
mov L0x7fffffffdbb0 r10;
mov L0x7fffffffdbb8 r11;
mov L0x7fffffffdba0 r8;

mov c0 L0x7fffffffdba0;
mov c1 L0x7fffffffdba8;
mov c2 L0x7fffffffdbb0;
mov c3 L0x7fffffffdbb8;


{
  eqmod (limbs 64 [c0, c1, c2, c3])
        (limbs 64 [a0, a1, a2, a3] * limbs 64 [b0, b1, b2, b3])
        ((2**255)-19)
  &&
  true
}
