{{% lowrisc-doc-hdr RV_PLIC FPV Plan }}
{{% import_testplan ../data/rv_plic_fpv_testplan.hjson }}

{{% toc 4 }}

## Goals
* Verify all the RV_PLIC outputs by writing assumptions and assertions with a
  FPV based testbench
* Verify TileLink device protocol compliance with a FPV based testbench

## Current status
* [Design & verification stage](../../../../doc/project/hw_dashboard.md)
  * [HW development stages](../../../../doc/ug/hw_stages.md)
* FPV dashboard (link TBD)

## Design features
For detailed information on RV_PLIC design features, please see the
[RV_PLIC design specification](rv_plic.md).

## Testbench architecture
RV_PLIC FPV testbench has been constructed based on the [formal
architecture](../../../formal/README.md)

### Block diagram
![Block diagram](fpv.svg)

#### TLUL assertions
* The `../fpv/tb/rv_plic_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md)
  to rv_plic to ensure TileLink interface protocol compliance
* TODO: Plan to implement csr assertions under `../fpv/vip/` to assert the
  TileLink writes and reads correct CSRs

#### RV_PLIC assertions
The `../fpv/tb/rv_plic_bind.sv` binds the `rv_plic_assert` under
`../fpv/vip/rv_plic_assert.sv`. The assertion file ensures RV_PLIC's outputs
(`irq_o` and `irq_id_o`) and important signals (`ip`) are being asserted.

##### Symbolic variables
Due to there are large number of input interrupt sources, the symbolic variable
is used to reduce the number of repeated assertions code. In RV_PLIC, we
declared two symbolic variables `src_sel` and `tgt_sel` to represent the index for
interrupt source and interrupt target.
Detailed explanation is listed in the
[Symbolic Variables](../../../formal/README.md#symbolic-variables) section.

## Testplan
{{% insert_testplan x }}
