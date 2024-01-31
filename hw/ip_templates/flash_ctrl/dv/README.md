# FLASH_CTRL DV document

## Goals
* **DV**
  * Verify all `flash_ctrl` IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Simulation results](https://reports.opentitan.org/hw/ip/flash_ctrl/dv/latest/report.html)

## Design features
For detailed information on `flash_ctrl` design features, please see the [`flash_ctrl` HWIP technical specification](../README.md).
The design-under-test (DUT) wraps the `flash_ctrl` IP, `flash_phy` and the TLUL SRAM adapter that converts the incoming TL accesses from the from host (CPU) interface into flash requests.
These modules are instantiated and connected to each other and to the rest of the design at the top level.
For the IP level DV, we replicate the instantiations and connections in `flash_ctrl_wrapper` module maintained in DV, located at `hw/ip/flash_ctrl/dv/tb/flash_ctrl_wrapper.sv`.
In future, we will consider having the wrapper maintained in the RTL area instead.

## Testbench architecture
The `flash_ctrl` UVM DV testbench has been constructed based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Block diagram
![Block diagram](./doc/tb.svg)

### Top level testbench
Top level testbench is located at `hw/ip/flash_ctrl/dv/tb/tb.sv`.
It instantiates the `flash_ctrl_wrapper`.
In addition, the testbench instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md)
* [TileLink host interface for the flash controller](../../../dv/sv/tl_agent/README.md)
* [TileLink host interface for the eflash](../../../dv/sv/tl_agent/README.md)
* TileLink host interface for the prim registers
* Interrupts ([`pins_if`](../../../dv/sv/common_ifs/README.md)
* [Memory backdoor utility](../../../dv/sv/mem_bkdr_util/README.md)
* Secret key interface from the OTP
* Interface from the life cycle manager
* Interface to the `keymgr` and `pwrmgr`

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### TL_agent
`flash_ctrl` UVM environment instantiates a (already handled in CIP base env) [tl_agent](../../../dv/sv/tl_agent/README.md) which provides the ability to drive and independently monitor random traffic via TL host interface into `flash_ctrl` device.
There are two additional instances of the `tl_agent`.
* Host interface to the `flash_phy`, to directly fetch the contents of the flash memory, bypassing the `flash_ctrl`.
* Host interface to the `prim registers`.

The `tl_agent` monitor supplies partial TileLink request packets as well as completed TileLink response packets over the TLM analysis port for further processing within the `flash_ctrl` scoreboard.

### UVM RAL Model
The `flash_ctrl` RAL model is created with the [`ralgen`](../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`](../../../../util/reggen/doc/setup_and_use.md):

#### Sequence cfg
An efficient way to develop test sequences is by providing some random variables that are used to configure the DUT / drive stimulus.
The random variables are constrained using weights and knobs that can be controlled.
These weights and knobs take on a "default" value that will result in the widest exploration of the design state space, when the test sequence is randomized and run as-is.
To steer the randomization towards a particular distribution or to achieve interesting combinations of the random variables, the test sequence can be extended to create a specialized variant.
In this extended sequence, nothing would need to be done, other than setting those weights and knobs appropriately.
This helps increase the likelihood of hitting the design corners that would otherwise be difficult to achieve, while maximizing reuse.

This object aims to provide such run-time controls.
An example of such a knob is `num_en_mp_regions`, which controls how many flash memory protection regions to configure, set to 'all' by default.

#### Env cfg
The `flash_ctrl_env_cfg`, environment configuration object provides access to the following elements:
* Build-time controls to configure the UVM environment composition during the `build_phase`
* Downstream agent configuration objects for ease of lookup from any environment component
  * This includes the `tl_agent_cfg` objects for both TL interfaces
* All virtual interfaces that connect to the DUT listed above (retrieved from the `uvm_config_db`)
* Sequence configuration object described above

All environment components contain a handle to an instance of this class (that was created in the test class via the parent `dv_base_test`).
By housing all of the above, all pertinent information is more easily shared with all environment components.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/flash_ctrl/dv/env/seq_lib`.
The `flash_ctrl_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `flash_ctrl_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows: From `hw/ip/flash_ctrl/dv/env/seq/flash_ctrl_base_vseq.sv`,
* reset_flash
  Reset flash controller and initialize flash device using back door interface.
* flash_ctrl_start_op
  Start operation on the flash controller
* flash_ctrl_write
  Send data to `prog_fifo`. This task is used for `program operation` from controller combined with `flash_ctrl_start_op`.
* flash_ctrl_read
  Read data from `rd_fifo`. This task is used for `read operation` from controller combined with `flash_ctrl_start_op`.
* wait_flash_op_done
  Polling `op_status` until op_status.done is set.
* do_direct_read
  Task to read flash from the host interface. Transaction size is 4 byte per transaction.
* flash_ctrl_intr_read
  Task to program flash with interrupt mode.
* flash_ctrl_intr_write
  Task to read flash with interrupt mode.
* send_rma_req
  Task to initiate rma request. Once rma started, task polls `rma ack` until it completes.

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
`hw/ip/flash_ctrl/dv/env/flash_ctrl_env_cov.sv`
* control_cg
  Collects operation types, partition and cross coverage of both.
* erase_susp_cg
  Check if request of erase suspension occurred.
* msgfifo_level_cg
  Covers all possible fifo status to generate interrupt for read / program.
* eviction_cg
  Check whether eviction happens at all 4 caches with write / erase operation.
  Also check each address belongs to randomly enabled scramble and ecc.
* error_cg
  Check errors defined in error code registers.
### Self-checking strategy
#### Scoreboard
The `flash_ctrl_scoreboard` is primarily used for csr transaction integrity.
Test bench also maintains a reference memory model (associative array) per partition.
The reference model is updated on each operation and used for expected partition values at the end of test check.
Given large memory size (mega bytes), maintaining an associative array per operation until the end of the test causes huge simulation overhead.
Also, this model is not suitable for read only test, same address write test, descramble tests and error injection test for ecc.
To address such issues, `on-the-fly` method is also used on top of legacy test component.
In `on-the-fly` test mode, test does not rely on reference memory mode.
Instead, it creates reference data for each operation.
For the program(write) operation, rtl output is collected from flash phy interface and compared with each operation's pre calculated write data.
For the read operation, the expected data is written via memory backdoor interface, read back, and compared.
The `flash_ctrl_otf_scoreboard` is used for `on-the-fly` mode flash transaction integrity check, while `flash_ctrl_scoreboard` is still used for csr transaction integrity check.
Since there is still uncovered logic within the model before data reaches the actual device, we add extra scoreboard to check that path and call it `last mile scoreboard`.
The `last mile scoreboard` is added to compensate `on-the-fly` model.
For the write transaction, `on-the-fly` model collects rtl data at the boundary of the controller and flash model.

#### Assertions
* TLUL assertions: The `hw/ip/flash_ctrl/dv/sva/flash_ctrl_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

### Global types and methods
All common types and methods defined at the package level can be found in
`flash_ctrl_env_pkg`. Some of them in use are:
```systemverilog
** types and enums
// Interrupt enums
  typedef enum int {
    FlashCtrlIntrProgEmpty = 0,
    FlashCtrlIntrProgLvl   = 1,
    FlashCtrlIntrRdFull    = 2,
    FlashCtrlIntrRdLvl     = 3,
    FlashCtrlIntrOpDone    = 4,
    FlashCtrlIntrErr       = 5,
    NumFlashCtrlIntr       = 6
  } flash_ctrl_intr_e;

// Flash initialization mode
  typedef enum {
    FlashMemInitCustom,     // Initialize flash (via bkdr) with custom data set.
    FlashMemInitSet,        // Initialize with all 1s.
    FlashMemInitClear,      // Initialize with all 0s.
    FlashMemInitRandomize,  // Initialize with random data.
    FlashMemInitInvalidate, // Initialize with Xs.
    FlashMemInitEccMode     // Flash init for ecc_mode
  } flash_mem_init_e;

// Ecc test mode
  typedef enum {
    FlashEccDisabled,    // No ecc enable
    FlashEccEnabled,     // Ecc enable but no error injection
    FlashSerrTestMode,   // Ecc enable and single bit error injection
    FlashDerrTestMode,   // Ecc enable and double bit error injection
    FlashIerrTestMode    // Ecc enable and integrity error injection
  } ecc_mode_e;

// 4-states flash data type
typedef logic [TL_DW-1:0] data_4s_t;
// flash address type
typedef bit [TL_AW-1:0] addr_t;
// Queue of 4-states data words
typedef data_4s_t data_q_t[$];
// Flash op struct
typedef struct packed {
    flash_dv_part_e  partition;   // data or one of the info partitions
    flash_erase_e    erase_type;  // erase page or the whole bank
    flash_op_e       op;          // read / program or erase
    flash_prog_sel_e prog_sel;    // program select
    uint             num_words;   // number of words to read or program (TL_DW)
    addr_t           addr;        // starting addr for the op
    // addres for the ctrl interface per bank, 18:0
    bit [flash_ctrl_pkg::BusAddrByteW-2:0] otf_addr;
  } flash_op_t;

```

## Building and running tests
We are using our in-house developed [regression tool](../../../../util/dvsim/README.md) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a smoke test:
```console
$ cd $REPO_TOP
$ ./util/dvsim/dvsim.py hw/ip/flash_ctrl/dv/flash_ctrl_sim_cfg.hjson -i flash_ctrl_smoke
```

## Testplan
[Testplan](../data/flash_ctrl_testplan.hjson)
