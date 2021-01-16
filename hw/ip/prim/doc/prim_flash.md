---
title: "Primitive Component: Flash Wrapper"
---

# Overview
`prim_flash` is a wrapper interface for technology specific flash modules.

As the exact details of each technology can be different, this document mainly describes the interface requirements and their functions.
The wrapper however does assume that all page sizes are the same (they cannot be different between data and info partitions, or different types of info partitions).

## Parameters

Name           | type   | Description
---------------|--------|----------------------------------------------------------
NumBanks       | int    | Number of flash banks.  Flash banks are assumed to be identical, asymmetric flash banks are not supported
InfosPerBank   | int    | Maximum number of info pages in the info partition.  Since info partitions can have multiple types, this is max among all types.
InfoTypes      | int    | The number of info partition types, this number can be 1~N.
InfoTypesWidth | int    | The number of bits needed to represent the info types.
PagesPerBank   | int    | The number of pages per bank for data partition.
WordsPerPage   | int    | The number of words per page per bank for both information and data partition.
DataWidth      | int    | The full data width of a flash word (inclusive of metadata)
MetaDataWidth  | int    | The metadata width of a flash word
TestModeWidth  | int    | The number of test modes for a bank of flash


## Signal Interfaces

### Overall Interface Signals
Name                    | In/Out | Description
------------------------|--------|---------------------------------
clk_i                   | input  | Clock input
rst_ni                  | input  | Reset input
flash_req_i             | input  | Inputs from flash protocol and physical controllers
flash_rsp_o             | output | Outputs to flash protocol and physical controllers
prog_type_avail_o       | output | Available program types in this flash wrapper: Currently there are only two types, program normal and program repair
init_busy_o             | output | The flash wrapper is undergoing initialization
tck_i                   | input  | jtag tck
tdi_i                   | input  | jtag tdi
tms_i                   | input  | jtag tms
tdo_o                   | output | jtag tdo
bist_enable_i           | input  | lc_ctrl_pkg :: On for bist_enable input
scanmode_i              | input  | dft scanmode input
scan_en_i               | input  | dft scan shift input
scan_rst_ni             | input  | dft scanmode reset
flash_power_ready_h_i   | input  | flash power is ready (high voltage connection)
flash_power_down_h_i    | input  | flash wrapper is powering down (high voltage connection)
flash_test_mode_a_i     | input  | flash test mode values (analog connection)
flash_test_voltage_h_i  | input  | flash test mode voltage (high voltage connection)
flash_err_o             | output | flash level error interrupt indication, cleared on write 1 to status register
flash_alert_po          | output | flash positive detector alert
flash_alert_no          | output | flash negative detector alert
flash_alert_ack         | input  | single pulse ack
flash_alert_trig        | input  | alert force trig by SW
tl_i                    | input  | TL_UL  interface for rd/wr registers access
tl_o                    | output | TL_UL  interface for rd/wr registers access
### Flash Request/Response Signals

Name               | In/Out | Description
-------------------|--------|---------------------------------
rd                 | input  | read request
prog               | input  | program request
prog_last          | input  | last program beat
prog_type          | input  | type of program requested: currently there are only two types, program normal and program repair
pg_erase           | input  | page erase request
bk_erase           | output | bank erase request
erase_suspend      | input  | erase suspend request
addr               | input  | requested transaction address
part               | input  | requested transaction partition
info_sel           | input  | if requested transaction is information partition, the type of information partition accessed
he                 | input  | high endurance enable for requested address
prog_data          | input  | program data
ack                | output | transction acknowledge
rd_data            | output | transaction read data
done               | output | transaction done



# Theory of Operations

## Transactions

Transactions into the flash wrapper follow a req / ack / done format.
A request is issued by raising one of `rd`, `prog`, `pg_erase` or `bk_erase` to 1.
When the flash wrapper accepts the transaction, `ack` is returned.
When the transaction fully completes, a `done` is returned as well.

Depending on the type of transaction, there may be a significant gap between `ack` and `done`.
For example, a read may have only 1 or 2 cycles between transaction acknowledgement and transaction complete.
Whereas a program or erase may have a gap extending up to uS or even mS.

It is the flash wrapper decision on how many outstanding transaction to accept.
The following are examples for read, program and erase transactions.

### Read
{{< wavejson >}}
{signal: [
  {name: 'clk_i',     wave: 'p.................'},
  {name: 'rd_i',      wave: '011..0.1..0.......'},
  {name: 'addr_i',    wave: 'x22..x.2..x.......'},
  {name: 'ack_o',     wave: '010.10...10.......'},
  {name: 'done_o',    wave: '0....10...10....10'},
  {name: 'rd_data_o', wave: 'x....2x...2x....2x'},
]}
{{< /wavejson >}}

### Program
{{< wavejson >}}
{signal: [
  {name: 'clk_i',       wave: 'p................'},
  {name: 'prog_i',      wave: '011...0.1....0...'},
  {name: 'prog_type_i', wave: 'x22...x.2....x...'},
  {name: 'prog_data_i', wave: 'x22...x.2....x...'},
  {name: 'prog_last_i', wave: '0.......1....0...'},
  {name: 'ack_o',       wave: '010..10.....10...'},
  {name: 'done_o',      wave: '0..............10'},
]}
{{< /wavejson >}}

### Erase
{{< wavejson >}}
{signal: [
  {name: 'clk_i',     wave: 'p................'},
  {name: '*_erase_i', wave: '01.0.........1.0.'},
  {name: 'ack_o',     wave: '0.10..........10.'},
  {name: 'done_o',    wave: '0.....10.........'},
]}
{{< /wavejson >}}

## Initlialization

The flash wrapper may undergo technology specific intializations when it is first powered up.
During this state, it asserts the `init_busy` to inform the outside world that it is not ready for transactions.
During this time, if a transaction is issued towards the flash wrapper, the transaction is not acknowledged until the initialization is complete.

## Program Beats

Since flash programs can take a significant amount of time, certain flash wrappers employ methods to optimize the program operation.
This optimization may place an upper limit on how many flash words can be handled at a time.
The purpose of the `prog_last` is thus to indicate when a program burst has completed.

Assume the flash wrapper can handle 16 words per program operation.
Assume a program burst has only 15 words to program and thus will not fill up the full program resolution.
On the 15th word, the `prog_last` signal asserts and informs the flash wrapper that it should not expect a 16th word and should proceed to complete the program operation.

## Program Type
The `prog_type` input informs the flash wrapper what type of program operation it should perform.
A program type not supported by the wrapper, indicated through `prog_type_avail` shall never be issued to the flash wrapper.

## Erase Suspend
Since erase operations can take a significant amount of time, sometimes it is necessary for software or other components to suspend the operation.
The suspend operation input request starts with `erase_suspend_req` assertion. Flash wrapper circuit acks when wrapper starts suspend.
When the erase suspend completes, the flash wrapper circuitry also asserts `done` for the ongoing erase transaction to ensure all hardware gracefully completes.

The following is an example diagram
{{< wavejson >}}
{signal: [
  {name: 'clk_i',                wave: 'p................'},
  {name: 'pg_erase_i',           wave: '01.0..............'},
  {name: 'ack_o',                wave: '0.10...10........'},
  {name: 'erase_suspend_i',      wave: '0.....1.0........'},
  {name: 'done_o',               wave: '0............10..'},
 ]
  }
{{< /wavejson >}}

## Error Interrupt
The `flash_err_o` is a level interrupt indication, that is asserted whenever an error event occurs in one of the Flash banks.
An Error status register is used to hold the error source of both banks, and it is cleared on writing 1 to the relevant bit.
Clearing the status register trigs deassertion of the interrupt.
