# Comparing libjade and libjc implementation of X25519

## Ref4

### Addition

Addition in libjc is implemented as a single function called `add` whilst there are multiple variants in the libjade version. The equivalent of `add` in libjade is `__add4_rrs`. Other functions include `__add_rss` and the main difference are the input and output types.

The libjc implementation is more naive, for example,

```
  for i = 0 to 4 {
    if(i == 0) {
       cf, x[0] += ya[0];
    }
    else {
       cf, x[i] += ya[i] + cf;
    }
  }
```

is simplified in libjade to,

```
  cf, h[0] += g[0];
  for i=1 to 4 {
      cf, h[i] += g[i] + cf;
  }
```

There are also minor differences, like working on a copy of the input rather than the input itself.

### Subtraction

Similar situation as addition. 

### Reduction

Identical.

### Multiplication
#### Generic

Identical, but libjade also includes more functions similar to subtraction and addition. Furthermore, there exist other implementations in libjade which works directly with register pointers and another with inline u64 variables.

#### Multiplication by 121666

Does not exist in libjade.

### Squaring

#### Generic
Identical, but with libjade once again has more implementations (e.g. using stack pointers instead of registers).

#### Iterated

There is a big difference, iterated square is written in an "exhaustive way" while a call to squaring with pointers then a DEC_32 instruction is used until there are no more carry bits. 

### CSwap

Completely different as the libjade implementation includes masking and utilises copy

### Montgomery ladder

The initial difference is the the libjc function accepts stack arrays and outputs stack arrays, whereby the libjade also utilises register arrays. Furthermore, the montgomery ladder in libjc also initializes the points inline whilst the libjade calls `__init_points4(u)`.
Furthermore, the montgomery ladder step is done by calling the `montgomery_ladder_step4`, which also calls the `__cswap4` function. 

Libjc also calls a function called `ladderstep` but delegates the `cswap` function call to the "highest level" montgomery ladder function rather than `ladderstep`. This function also performs the add and double whilst libjade has a function for that. The code for the add and double function is quite different in both implementations.

### Invert

Invert is very similar in both implementations, but there are less square operations in the libjade version.

### Unpacking

This is done in the `unpack_point` in the libjc implementation but is embedded into the `curve25519_ref4` function in libjade. Same for the unpacking of secrets.

### Packing

This is done in the `pack` function in libjc which does does a lot of the calculations inline. In libjade, this is done int he `__encode_point4`.

### Curve25519 Ref

Again, similar code but there is more modularity in the libjade.