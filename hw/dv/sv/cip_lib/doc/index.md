# Comportable IP Testbench Architecture


## Overview
Going along the lines of what it takes to design an IP that adheres to the
[Comportability Specifications](/doc/rm/comportability_specification),
we attempt to standardize the DV methodology for developing the IP level
testbench environment as well by following the same approach. This document describes
the Comportable IP (CIP) library, which is a complete UVM environment framework that
each IP level environment components can extend from to get started with DV. The goal
here is to maximize code reuse across all test benches so that we can improve the
efficiency and time to market. The features described here are not exhaustive,
so it is highly recommended to the reader that they examine the code directly. In
course of development, we also periodically identify pieces of verification logic that
might be developed for one IP but is actually a good candidate to be added to
these library classes instead. This doc is instead intended to provide the user
a foray into what these are and how are the meant to be used.


## CIP environment block diagram
![CIP environment block diagram](env.svg)

## CIP library classes
The CIP library includes the base ral model, env cfg object, coverage
object, virtual sequencer, scoreboard, env, base virtual sequence and finally
the test class. To achieve run-time polymorphism, these classes are type
parameterized to indicate what type of child objects are to be created. In the
IP environments, the extended classes indicate the correct type parameters.

### cip_base_env_cfg
This class is intended to contain all of the settings, knobs, features, interface
handles and downstream agent cfg handles. Features that are common to all IPs in
accordance with the comportability spec are made a part of this base class, while the
extended IP env cfg class will contain settings specific to that IP. An instance of
the env cfg class is created in `cip_base_test::build_phase` and the handle is
passed over uvm_config_db for the CIP env components to pick up. This allows
the handle to the env cfg object to be available in the env's build_phase. Settings
in the env cfg can then be used to configure the env based on the test needs.

A handle to this class instance is passed on to the scoreboard, virtual
sequencer and coverage objects so that all such common settings and features
are instantly accessible everywhere.

This class is type parameterized in the following way:
```systemverilog
class cip_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;
```
The IP env cfg class will then extend from this class with the RAL_T parameter set
to the actual IP RAL model class. This results in IP RAL model getting factory
overridden automatically in the base env cfg itself during creation, so there is no
need for manual factory override. We follow the same philosophy in all CIP library
classes.

The following is a list of common features and settings:
* **clk_rst_if**: A handle to the clk_rst_if that controls the main clk and reset
  to the DUT.
* **intr_vif**: This is a handle to the `pins_if #(NUM_MAX_INTERRUPTS=64)` interface
  instance created in the tb to hookup the DUT interrupts. The actual number of
  interrupts might be much less than 64, but that is ok - we just connect as
  many as the DUT provides. The reason for going with a fixed width pins_if is
  to allow the intr_vif to be available in this base env cfg class (which does not
  know how many interrupt each IP DUT provides).
* **devmode_vif**: THis is a handle to the `pins_if #(1)` interface instance created
  in the tb to hookup the DUT input `devmode`.
* **tl_agent_cfg**: The downstream TileLink host agent created in the cip_base_env
  class requires the agent cfg handle to tell it how to configure the agent.
* **alert_agent_cfgs**: Similar to tl_agent_cfg, the downstream alert device agent
  created in the cip_base_env class requires the agent cfg handles to tell it how to
  configure the agent. In default, alert agent is configured in device mode,
  asynchronous, active and the ping coverage is turned off.
* **ral**: This is the instance to the auto-generated RAL model that is
  extended from `dv_base_reg_block`. In the base class, this is created using
  the RAL_T class parameter which the extended IP env cfg class sets correctly.

Apart from these, there are several common settings such as `zero_delays`,
`clk_freq_mhz`, which are randomized as well as knobs such as `en_scb` and
`en_cov` to turn on/off scoreboard and coverage collection respectively.

The base class provides a virtual method called `initialize()` which is called
in `cip_base_test::build_phase` to create some of the objects listed above. If
the extended IP env cfg class has more such objects added,  then the `initialize()`
method is required to be overridden to create those objects as well.

We make all downstream interface agent cfg handles as a part of IP extension of
cip_base_env_cfg so that all settings for the env and all downstream agents are
available within the env cfg handle. Since the env cfg handle is passed to all cip
components, all those settings are also accessible.

### cip_base_env_cov
This is the base coverage object that contain all functional coverpoints and
covergroups. The main goal is to have all functional coverage elements
implemented in a single place. This class is extended from `uvm_component`
so that it allows items to be set via `'uvm_config_db` using the component's
hierarchy. This is created in cip_base_env and a handle to it is passed to the
scoreboard and the virtual sequencer. This allows coverage to be sampled in
scoreboard as well as the test sequences.

This class is type parameterized with the env cfg class type `CFG_T` so that it
can derive coverage on some of the env cfg settings.
```systemverilog
class cip_base_env_cov #(type CFG_T = cip_base_env_cfg) extends uvm_component;
```

The following covergroups are defined outside of the class for use by all IP
testbenches:
* `intr_cg`: Covers individual and cross coverage on intr_enable and intr_state for all interrupts in IP
* `intr_test_cg`: Covers intr_test coverage and its cross with intr_enable and intr_state for all interrupts in IP
* `intr_pins_cg`: Covers values and transitions on all interrupt output pins of IP
* `sticky_intr_cov`: Covers sticky interrupt functionality of all applicable interrupts in IP

Covergroups `intr_cg`, `intr_test_cg` and `intr_pins_cg` are instantiated
and allocated in `cip_base_env_cov` by default in all IPs.
On the other hand, `sticky_intr_cov` is instantiated with string key.
The string key represents the interrupts names that are sticky. This is specific
to each IP and is required to be created and instantiated in extended `cov` class.

### cip_base_virtual_sequencer
This is the base virtual sequencer class that contains a handle to the
`tl_sequencer` to allow layered test sequences to be created. The extended IP
virtual sequencer class will include handles to the IP specific agent
sequencers.

This class is type-parameterized with the env cfg class type `CFG_T` and coverage
class type `COV_T` so that all test sequences can access the env cfg settings and
sample the coverage via the `p_sequencer` handle.
```systemverilog
class cip_base_virtual_sequencer #(type CFG_T = cip_base_env_cfg,
                                   type COV_T = cip_base_env_cov) extends uvm_sequencer;
```

### cip_base_scoreboard
This is the base scoreboard component that already connects with the TileLink
agent monitor to grab tl packets via analysis port at the address and the data
phases. It provides a virtual task called `process_tl_access` that the extended
IP scoreboard needs to implement. Please see code for additional details. The
extended IP scoreboard class will connect with the IP-specific interface monitors
if applicable to grab items from those analysis ports.

This class is type-parameterized with the env cfg class type `CFG_T`, ral class
type `RAL_T` and the coverage class type `COV_T`.
```systemverilog
class cip_base_scoreboard #(type RAL_T = dv_base_reg_block,
                            type CFG_T = cip_base_env_cfg,
                            type COV_T = cip_base_env_cov) extends uvm_component;
```
There are several virtual tasks and functions that are to be overridden
in extended IP scoreboard class. Please take a look at the code for more
details.

### cip_base_env
This is the base UVM env that puts all of the above components together
and creates and makes connections across them. In the build phase, it retrieves
the env cfg class type handle from `uvm_config_db` as well as all the virtual
interfaces (which are actually part of the env cfg class). It then uses the env
cfg settings to modify the downstream agent cfg settings as required. All of
the above components are created based on env cfg settings, along with the TileLink
host agent and alert device agents if the module has alerts. In the connect phase,
the scoreboard connects with the monitor within the TileLink agent to be able to
grab packets from the TL interface during address and the data phases. The scoreboard
also connects the alert monitor within the alert_esc_agent to grab packets
regarding alert handshake status. In the end of elaboration phase, the ral
model within the env cfg handle is locked and the ral sequencer and adapters are
set to be used with the TileLink interface.

This class is type parameterized with env cfg class type CFG_T, coverage class type
`COV_T`, virtual sequencer class type `VIRTUAL_SEQUENCER_T` and scoreboard class
type `SCOREBOARD_T`.
```systemverilog
class cip_base_env #(type CFG_T               = cip_base_env_cfg,
                     type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer,
                     type SCOREBOARD_T        = cip_base_scoreboard,
                     type COV_T               = cip_base_env_cov) extends uvm_env;
```

### cip_base_vseq
This is the base virtual sequence class that will run on the cip virtual
sequencer. This base class provides 'sequencing' set of tasks such as
`dut_init()` and `dut_shutdown()` which are called within `pre_start` and
`post_start` respectively. This sequence also provides an array of
sub-sequences some of which are complete tests within themselves, but
implemented as tasks. The reason for doing so is SystemVerilog does not
support multi-inheritance so all sub-sequences that are identified as being
common to all IP benches implemented as tasks in this base virtual sequence class.
Some examples:
* **task run_csr_vseq_wrapper**: This is a complete CSR test suite in itself -
  Extended IP CSR vseq can simply call this in the body. This is paired with a
  helper function `add_csr_exclusions`.
* **function add_csr_exclusions**: This is extended in the IP CSR vseq to add
  exclusions when running the CSR suite of tests.
* **task tl_access**: This is a common generic task to create a read or a write
  access over the TileLink host interface.
* **task cfg_interrupts, check_interrupts**: All interrupt CSRs are standardized
  according to the comportability spec, which allows us to create common tasks
  to turn on / off interrupts as well as check them.
* **task run_tl_errors_vseq**: This task will test all kinds of TileLink error
  cases, including unmapped address error, protocol error, memory access error
  etc. All the items sent in this task will trigger d_error and won't change the
  CSR/memory value.
* **task run_stress_all_with_rand_reset_vseq**: This task runs 3 parallel threads,
  which are ip_stress_all_vseq, run_tl_errors_vseq and reset sequence. After
  reset occurs, the other threads will be killed and then all the CSRs will be read
  for check. This task runs multiple iterations to ensure DUT won't be broken after
  reset and TL errors.
  To ensure the reset functionality works correctly, user will have to disable
  any internal reset from the stress_all sequence. Below is an example of
  disabling internal reset in `hmac_stress_all_vseq.sv`:
* **task run_same_csr_outstanding_vseq**: This task tests the same CSR with
  non-blocking accesses as the regular CSR sequences don't cover that due to
  limitation of uvm_reg.
* **task run_mem_partial_access_vseq**: This task tests the partial access to the
  memories by randomizing mask, size, and the 2 LSB bits of the address. It also runs
  with non-blocking access enabled.
  ```
  // randomly trigger internal dut_init reset sequence
  // disable any internal reset if used in stress_all_with_rand_reset vseq
  if (do_dut_init) hmac_vseq.do_dut_init = $urandom_range(0, 1);
  else hmac_vseq.do_dut_init = 0;
  ```

This class is type parameterized with the env cfg class type `CFG_T`, ral class type
`RAL_T` and the virtual sequencer class type `VIRTUAL_SEQUENCER_T` so that the
env cfg settings, the ral CSRs are accessible and the `p_sequencer` type can be
declared.

```systemverilog
class cip_base_vseq #(type RAL_T               = dv_base_reg_block,
                      type CFG_T               = cip_base_env_cfg,
                      type COV_T               = cip_base_env_cov,
                      type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer) extends uvm_sequence;
```
All virtual sequences in the extended IP will eventually extend from this class and
can hence, call these tasks and functions directly as needed.

### cip_base_test
This basically creates the IP UVM env and its env cfg class instance. Any env cfg
setting that may be required to be controlled externally via plusargs are looked
up here, before the env instance is created. This also sets a few variables that
pertain to how / when should the test exit on timeout or failure. In the run
phase, the test calls `run_seq` which basically uses factory to create the
virtual sequence instance using the `UVM_TEST_SEQ` string that is passed via
plusarg. As a style guide, it is preferred to encapsulate a complete test within
a virtual sequence and use the same `UVM_TEST` plusarg for all of the tests (which
points to the extended IP test class), and only change the `UVM_TEST_SEQ` plusarg.

This class is type parameterized with the env cfg class type `CFG_T` and the env
class type `ENV_T` so that when extended IP test class creates the env and env cfg
specific to that IP.
```systemverilog
class cip_base_test #(type CFG_T = cip_base_env_cfg,
                      type ENV_T = cip_base_env) extends uvm_test;
```

## Extending from CIP library classes
Let's say we are verifying an actual comportable IP `uart` which has `uart_tx`
and `uart_rx` interface. User then develops the `uart_agent` to be able to talk
to that interface. User invokes the `ralgen` tool to generate the `uart_reg_block`,
and then starts developing UVM environment by extending from the CIP library
classes in the following way.

### uart_env_cfg
```systemverilog
class uart_env_cfg extends cip_base_env_cfg #(.RAL_T(uart_reg_block));
```
User adds the `uart_agent_cfg` object as a member so that it remains as a
part of the env cfg and can be accessed everywhere. In the base class's
`initialize()` function call, an instance of `uart_reg_block` is created, not
the `dv_base_reg_block`, since we override the `RAL_T` type.

### uart_env_cov
```systemverilog
class uart_env_cov extends cip_base_env_cov #(.CFG_T(uart_env_cfg));
```
User adds `uart` IP specific coverage items and uses the `cov` handle in
scoreboard and test sequences to sample the coverage.

### uart_virtual_sequencer
```systemverilog
class uart_virtual_sequencer extends cip_base_virtual_sequencer #(.CFG_T(uart_env_cfg),
                                                                  .COV_T(uart_env_cov));
```
User adds the `uart_sequencer` handle to allow layered test sequences
to send traffic to / from TileLink as well as `uart` interfaces.

### uart_scoreboard
```systemverilog
class uart_scoreboard extends cip_base_scoreboard #(.CFG_T(uart_env_cfg),
                                                    .RAL_T(uart_reg_block),
                                                    .COV_T(uart_env_cov));
```
User adds analysis ports to grab packets from the `uart_monitor` to
perform end-to-end checking.

### uart_env
```systemverilog
class uart_env extends cip_base_env #(.CFG_T               (uart_env_cfg),
                                      .COV_T               (uart_env_cov),
                                      .VIRTUAL_SEQUENCER_T (uart_virtual_sequencer),
                                      .SCOREBOARD_T        (uart_scoreboard));
```
User creates `uart_agent` object in the env and use it to connect with the
virtual sequencer and the scoreboard. User also uses the env cfg settings to
manipulate the uart agent cfg settings if required.

### uart_base_vseq
```systemverilog
class uart_base_vseq extends cip_base_vseq #(.CFG_T               (uart_env_cfg),
                                             .RAL_T               (uart_reg_block),
                                             .COV_T               (uart_env_cov),
                                             .VIRTUAL_SEQUENCER_T (uart_virtual_sequencer));
```
User adds a base virtual sequence as a starting point and adds common tasks and
functions to perform `uart` specific operations. User then extends from
`uart_base_vseq` to add layered test sequences.

### uart_base_test
```systemverilog
class uart_base_test extends cip_base_test #(.ENV_T(uart_env), .CFG_T(uart_env_cfg));
```
User sets `UVM_TEST` plus arg to `uart_base_test` so that all tests create the UVM env
that is automatically tailored to UART IP. Each test then sets the
`UVM_TEST_SEQ` plusarg to run the specific test sequence, along with additional
plusargs as required.

## Configure Alert Device Agent from CIP library classes

To configure alert device agents in block level testbench environment that extended
from this CIP library claaes, please follow the steps below:
* **${ip_name}_env_pkg.sv**: Add parameter `LIST_OF_ALERTS[]` and `NUM_ALERTS`.
  Please make sure the alert names and order are correct.
  For example in `otp_ctrl_env_pkg.sv`:
  ```systemverilog
  parameter string LIST_OF_ALERTS[] = {"fatal_macro_error", "fatal_check_error"};
  parameter uint NUM_ALERTS         = 2;
  ```
* **${ip_name}_env_cfg.sv**: In function `initialize()`, assign `LIST_OF_ALERTS`
  parameter to `list_of_alerts` variable which is created in `cip_base_env_cfg.sv`.
  Note that this assignment should to be written before calling `super.initialize()`,
  so that creating alert host agents will take the updated `list_of_alerts` variable.
  For example in `otp_ctrl_env_cfg.sv`:
  ```systemverilog
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = otp_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
  ```
* **tb.sv**: Add `DV_ALERT_IF_CONNECT` macro that declares alert interfaces,
  connect alert interface wirings with DUT, and set alert_if to uvm_config_db.
  Then connect alert_rx/tx to the DUT ports.
  For example in otp_ctrl's `tb.sv`:
  ```systemverilog
  `DV_ALERT_IF_CONNECT
  otp_ctrl dut (
    .clk_i                      (clk        ),
    .rst_ni                     (rst_n      ),
    .alert_rx_i                 (alert_rx   ),
    .alert_tx_o                 (alert_tx   ),
  ```
Note that if the testbench is generated from `uvmdvgen.py`, using the `-hr` switch
will automatically generate the skeleton code listed above for alert device agent.
Details on how to use `uvmdvgen.py` please refer to the
[uvmdvgen document]({{< relref "util/uvmdvgen/README" >}}).

## CIP Testbench
![CIP testbench diagram](tb.svg)
The block diagram above shows the CIP testbench architecture, that puts
together the static side `tb` which instantiates the `dut`, and the dynamic
side, which is the UVM environment extended from CIP library. The diagram
lists some common items that need to be instantiated in `tb`
and set into `uvm_config_db` for the testbench to work.
