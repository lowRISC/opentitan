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
valid_i      | input  | Input data available.
data_i[InW]  | input  | Input data.
mask_i[InW]  | input  | Input bit mask. Ones in the mask must be contiguous.
ready_o      | output | Indicates if prim_packer is able to accept data.
valid_o      | output | Indicates if output data is available.
data_o[OutW] | output | Output data.
mask_o[OutW] | output | Output bit mask.
ready_i      | input  | Output data can be drained.
flush_i      | input  | Send out stored data and clear state.
flush_done_o | output | Indicates flush operation is completed.

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

`prim_packer` accepts `InW` bits of data and bitmask signals. On a `valid_i`/
`ready_o` handshake, `data_i` is stored to internal registers and accumulated
until `OutW` data has been gathered. In the normal case, `mask_o` will be a
full width write (`{OutW{1'b1}}`). However, when `flush_i` is asserted,
`prim_packer` attempts to drain out all remaining data in the internal
storage. In this case, `mask_o` might be partial.

The internal register size is `InW + OutW` bits to safely store the incoming
data and send outgoing data to the `data_o` port.


```wavejson
{ signal: [
  { name: 'valid_i',      wave: '01.01.....0.'},
  { name: 'data_i[3:0]',  wave: 'x==x===.==x.', data:'0 1 2 3 4 5 6'},
  { name: 'mask_i[3:0]',  wave: 'x==x===.==x.', data:'F F F F F F F'},
  { name: 'ready_o',      wave: '1.....01....'},
  { name: 'valid_o',      wave: '0.10101..010'},
  { name: 'data_o[5:0]',  wave: 'x.=x=x=.=x=x', data:'10h 08h 03h 15h 06h'},
  { name: 'mask_o[5:0]',  wave: 'x.=x=x=.=x=x', data:'3Fh 3Fh 3Fh 3Fh Fh '},
  { name: 'ready_i',      wave: '1.....01....'},
  { name: 'flush_i',      wave: '0.........10'},
  { name: 'flush_done_o', wave: '0.........10'},
  ],

  head:{
    text: 'prim_packer',
    tick: ['0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18    ']
  }
}
```

The above waveform shows the case of InW := 4 and OutW := 6. After the first
transaction, `prim_packer` has `0h` in the storage. When the second `valid_i`
is asserted, it combines `0h` and incoming data `1h` and creates output `10h`
(`6'b01_0000`). The remaining `2'b00` is put into the internal storage from
`data_i[3:2]`. The next transaction combines this and input data `2h` to create
`6'b00_1000`.

`prim_packer` deasserts `ready_o` to indicate it cannot accept further data.
`ready_o` is deasserted when `ready_i` is deasserted and there is insufficient
internal storage available to store incoming data, as shown in cycle 6 above.

At the end of the sequence, `flush_i` is asserted, and the remaining data is
drained. In this case, `mask_o` isn't full to indicate only partial data is
available (`6'b00_1111`). `flush_done_o` is asserted as soon as the remaining
data is drained.

`prim_packer` only supports packing to the right. To use `prim_packer` in a
design requiring packing to the left (filling MSB first), the design needs to
reverse the bit order (and in some cases, the byte order) before pushing to the
packer, then reverse the data output.
