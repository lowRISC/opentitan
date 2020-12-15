# OTBN Tracer

The tracer consists of a module (`otbn_tracer.sv`) and an interface
(`otbn_trace_if.sv`). The interface is responsible for directly probing the
design and implementing any basic tracking logic that is required. The module
takes an instance of this interface and uses it to produce trace data.

Trace output is provided to the simulation environment by calling the
`accept_otbn_trace_string` function which is imported via DPI (the simulator
environment provides its implementation). Each call to
`accept_otbn_trace_string` provides a trace record and a cycle count. There is
at most one call per cycle. Further details are below.

A typical setup would bind an instantiation of `otbn_trace_if` and
`otbn_tracer` into `otbn_core` passing the `otbn_trace_if` instance into the
`otbn_tracer` instance. However this is no need for `otbn_tracer` to be bound
into `otbn_core` provided it is given a `otbn_trace_if` instance.

## Trace Format

Trace output is generated as a series of records. Each record consists of a
number of lines that begin with a single character that identifies the category
of the line and relate to activity occurring in the cycle the record is
associated with.  The format following that within the line depends upon the
category (see the XPrefix parameters below for the possible categories).

A record may start with an 'E' or 'S' (instruction execute or stall) line, then
has other lines.  Ordering for the other lines is not guaranteed. A record will
never be empty. It is expected that all records begin with an 'E' or 'S' line. A
record without an 'E' or 'S' line indicates a bug in OTBN. It is not the
tracer's responsibility to detect bugs; the simulation environment should flag
these as errors in a suitable way.

Whilst the tracer does not aim to detect bugs there may be instances where the
signals it traces do something unexpected that requires special behaviour. Where
this happens 'ERR' will be placed somewhere in the line that contains
information about the unexpected signals. See information on Memory Write (`W`)
lines below for an example. 'ERR' will not be present in trace output for any
other reason.

### Record examples
(The first line of each example illustrates the instruction being traced to aid the example and
is not part of the record)

Executing `BN.SID x26++, 0(x25)` at PC 0x00000158:
```
E PC: 0x00000158, insn: 0x01acd08b
< w20: 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be57d4_fecd21a1_b9dd0141
< x25: 0x00000020
< x26: 0x00000014
> x26: 0x00000015
W [0x00000020]: 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be57d4_fecd21a1_b9dd0141
```

Executing `BN.ADD w3, w1, w2` at PC 0x000000e8:
```
E PC: 0x000000e8, insn: 0x002081ab
< w01: 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be586e_9866bb3b_53769ada
< w02: 0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999
> w03: 0x1296659f_bbc28370_23634ee9_22168ae8_613491bf_0357f208_320054d4_ed103473
> FLAGS0: {C: 1, M: 0, L: 1, Z: 0}
```

## Line formats

### Instruction Execute (`E`) and Stall (`S`) lines

Indicates an instruction is executing or stalling. An 'E' line indicates the
instruction completed in the trace record's cycle. An instruction that is
stalled will first produce a record containing an 'S' line and will producing a
matching 'E' line in a future record the cycle it unstalls and finishes. The
line provides the PC and raw instruction bits. 

Instruction at 0x0000014c is 0x01800d13 and stalling (a future record will
contain a matching 'E' line):
```
S PC: 0x0000014c, insn: 0x01800d13
```

Instruction at 0x00000150 is 0x01acc10b is executing and will complete:
```
E PC: 0x00000150, insn: 0x01acc10b
```

### Register Read (`<`) and Write (`>`) lines

Indicates data that has been read or written to either register files or special
purpose registers (such as ACC or the bignum side flags).  The line provides the
register name and the data read/written

Register x26 was read and contained value 0x00000018:
```
< x26: 0x00000018
```

Register w24 had value
`0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_d0beb533_1234abcd` 
written to it:
```
> w24: 0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_d0beb533_1234abcd
```

Accumulator had value
`0x00000000_00000000_00311bcb_5e157313_a2fd5453_c7eb58ce_1a1d070d_673963ce`
written to it:
```
> ACC: 0x00000000_00000000_00311bcb_5e157313_a2fd5453_c7eb58ce_1a1d070d_673963ce
```

Flag group 0 had value `{C: 1, M: 1, L: 1, Z: 0}` written to it:
```
> FLAGS0: {C: 1, M: 1, L: 1, Z: 0}
```

### Memory Read (`R`) and Write (`W`) lines

Indicates activity on the Dmem bus. The line provides the address and data
written/read. For a read the data is always WLEN bits and the address is WLEN
aligned (for an execution of LW only a 32-bit chunk of that data is required).
For a write the write mask is examined. Where the mask indicates a bignum side
write (BN.SID) full WLEN bit data is provided and the address is WLEN aligned.
Where the mask indicates a base side write (SW) only 32-bit data is provided and
the address is 32-bit aligned (giving the full address of the written chunk).

Address `0x00000040` was read and contained value
`0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_baadf00d_1234abcd`:
```
R [0x00000040]: 0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_baadf00d_1234abcd
```

Address `0x00000004` had value `0xd0beb533` written to it:
```
W [0x00000004]: 0xd0beb533
```

In the event of an OTBN bug that produces bad memory masks on writes (where the
write is neither to a full 256 bits nor a aligned 32-bit chunk), an error line
is produced giving the full mask and data
```
W [0x00000080]: Mask ERR Mask: 0xfffff800_0000ffff_ffffffff_00000000_00000000_00000000_00000000_00000000 Data: 0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_baadf00d_1234abcd
```

## Using with dvsim

To use this code, depend on the core file. If you're using dvsim,
you'll also need to include `otbn_tracer_sim_opts.hjson` in your
simulator configuration and add `"{tool}_otbn_tracer_build_opts"` to
the `en_build_modes` variable.
