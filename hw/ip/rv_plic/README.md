# RISC-V Platform-Level Interrupt Controller

RV_PLIC module is to manage multiple interrupt events generated from the
peripherals. It implements [Platform-Level Interrupt Controller in RISC-V
Privileges specification Section
7](https://people.eecs.berkeley.edu/~krste/papers/riscv-privileged-v1.9.pdf#page=73).

## `reg_rv_plic.py`

The tool is to create register Hjson and top module `rv_plic.sv` files given
values of number of sources, number of targets, and max value of priority. By
default `sources` is **32**, `target` is **1** and `priority` is **7** (8 level of priorities
supported)

To change the value and to re-create hjson,

```console
$ util/reg_rv_plic.py -s 32 -t 1 -p 7 data/rv_plic.hjson.tpl > data/rv_plic.hjson
$ util/reg_rv_plic.py -s 32 -t 1 -p 7 data/rv_plic.sv.tpl > rtl/rv_plic.sv
```
