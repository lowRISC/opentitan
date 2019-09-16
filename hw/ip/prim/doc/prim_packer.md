{{% lowrisc-doc-hdr Primitive Component: Packer }}

{{% section1 Overview }}

`prim_packer` is a module that receives partial writes then packs and creates
full configurable width writes. It is one of a set of shared primitive modules
available for use within OpenTitan as referred to in the Comportability
Specification section on shared primitives.

{{% section2 Parameters }}

Name | type | Description
-----|------|-------------
InW  | int  | Input data width
OutW | int  | Output data width

{{% section2 Signal Interfaces }}

Name         | In/Out | Description
-------------|--------|-------------
valid_i      | input  |
data_i[InW]  | input  |
mask_i[InW]  | input  | input bit mask. ones in the mask_i shall be contiguous.
ready_o      | output | Indicates if prim_packer is able to accept the data or not.
valid_o      | output |
data_o[OutW] | output |
mask_o[OutW] | output |
ready_i      | input  |
flush_i      | input  | If 1, send out remnant and clear state
flush_done_o | output | Indicates flush operation is completed

{{% section1 Theory of Opeations }}

```code
           /----------\
valid_i    |          |      valid_o
---------->|          |--------------->
data_i     | stacked  |       data_o
=====/====>| register |=======/=======>
  [InW]    |          |    [OutW]
mask_i     |          |       mask_o
=====/====>| InW+OutW |=======/=======>
ready_o    |----------|      ready_i
<----------|          |<---------------
           |          |
           \----------/
```

`prim_packer` accepts `InW` bits of data and bitmask signals. If `valid_i` is
asserted, `prim_packer` stores it to internal register if the size isn't big
enough to `OutW` data width and repeats it until it exceeds `OutW`. In most
case, `mask_o` is full bits write, `{OutW{1'b1}}`. But when `flush_i` is
asserted, `prim_packer` tries to sends out any remaining data in the internal
storage. In this case, `mask_o` may become partial 1.

The internal register size is `InW + OutW` bits to safely store the incoming
data and sends out the data to `data_o` port.


```wavejson
{ signal: [
  { name: 'valid_i',     wave: '01.01.....0.'},
  { name: 'data_i[3:0]', wave: 'x==x===.==x.', data:'0 1 2 3 4 5 6'},
  { name: 'mask_i[3:0]', wave: 'x==x===.==x.', data:'F F F F F F F'},
  { name: 'ready_o',     wave: '1.....01....'},
  { name: 'valid_o',     wave: '0.10101.1010'},
  { name: 'data_o[5:0]', wave: 'x.=x=x=.=x=x', data:'10h 08h 03h 15h 06h'},
  { name: 'mask_o[5:0]', wave: 'x.=x=x=.=x=x', data:'3Fh 3Fh 3Fh 3Fh Fh '},
  { name: 'ready_i',     wave: '1.....01....'},
  { name: 'flush_i',     wave: '0.........10'},
  ],

  head:{
    text: 'prim_packer',
    tick: ['0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18    ']
  }
}
```

Above waveform shows the case of InW := 4 and OutW := 6. After the first
transaction, `prim_packer` has `0h` in the storage. So when second `valid_i` is
asserted, it combines `0h` and incoming data `1h` and creates output `10h`,
`6'b01_0000`. And store `2'b00` into the internal storage from `data_i[3:2]`.
Next transaction combines this and input data `2h` then creates `6'b00_1000`.

If `read_i` is dropped as seen at pos 6, `prim_packer` drops the `ready_o` as it
cannot store the incoming data. To reduce the internal logic complexity, it
drops the ready even above case can store the incoming data as 4bit is
available.

At the end of the transaction, if `flush_i` is asserted, it sends out the
remaining data.  In this case, `mask_o` isn't full ones but representing only
available bits `6'b00_1111`.

`prim_packer` only supports pack to right. If any design to support pack to left
(filling MSB first), the design needs to reverse the bit order (in some case,
reversing the byte-order is necessary like HMAC) before pushing to the packer
and reverse back after the data output.
