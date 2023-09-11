# Primitive Component: XoShiRo256++


`prim_xoshiro256pp` is a PRNG with 256-bit state.
For more information refer to [this page](https://arxiv.org/pdf/1805.01407.pdf).

## Parameters

Name         | type   | Description
-------------|--------|----------------------------------------------------------
OutputDw     | int    | Width of the PRNG output. Must be a multiple of 64.
DefaultSeed  | logic  | Initial 256-bit state of the PRNG, must be nonzero.

## Signal Interfaces

Name                 | In/Out | Description
---------------------|--------|---------------------------------
seed_en_i            | input  | External seed input enable
seed_i[256]          | input  | External seed input
xoshiro_en_i         | input  | PRNG enable
entropy_i[256]       | input  | Entropy input
data_o[OutputDw]     | output | PRNG output
all_zero_o           | output | Impossible all-zero state

# Theory of Operations

```
             /----------------\
seed_en_i    |                |
------------>|  xoshiro256++  |
seed_i       |                |  data_o
=====/======>|                |=====/=======>
 [256]       |                |  [OutputDw]
xoshiro_en_i |                |
------------>|    OutputDw    |
entropy_i    |   DefaultSeed  |  all_zero_o
=====/======>|                |------------->
 [256]       |                |
             |                |
             \----------------/
```

Xoshiro256++ PRNG consists of:
 * A 256-bit state
 * A single-cycle state-update function.
 * A state output function.

The basic xoshiro256++ PRNG has a 64-bit output.
This implementation supports an output size of any multiple of 64 bits.
The output size is controlled using the `OutputDW` parameter.

The xoshiro256++ module has an enable input and an additional entropy input that is
XORed into the PRNG state (connect to zero if this feature is unused).
As the PRNG may jump into the all-zero state (e.g. due to an active attack), the PRNG
state-update function contains a lockup protection which re-seeds the state with
`DefaultSeed` and raises the alert signal `all_zero_o`, once this condition is detected.

When the seed enable signal `seed_en_i` is raised, the internal state of xoshiro256++ is updated
with the value provided at the 256-bit input 'seed_i'.
The state is internally updated in every clock cycle whenever the enable signal `xoshiro_en_i` is raised.
The timing diagram below visualizes this process.

```wavejson
{
  signal: [
    {name: 'clk', wave: 'p......|....'},
    {name: 'xoshiro_en_i', wave: '0...1..|..0.'},
    {name: 'seed_en_i', wave: '010....|....'},
    {name:'seed_i',     wave: '3..x...|....', data: 'Seed' },
    {name: 'state', wave: 'x.3..45|678.', data: 'Seed'}
  ]
}
```
