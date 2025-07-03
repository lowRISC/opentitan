# Programmer's Guide

This section discusses how firmware can interface with EDN.

## Module enable and disable

EDN may only be enabled if CSRNG is enabled.
Once disabled, EDN may only be re-enabled after CSRNG has been disabled and re-enabled.
The only exception to this is when firmware takes care of properly uninstantiating the associated CSRNG instance before disabling EDN.
EDN can then be safely re-enabled without disabling and re-enabling CSRNG first.
For details, refer to [Uninstantiating CSRNG instance through EDN](#uninstantiating-csrng-through-edn).

The recommended enable sequence for the entropy complex is to first enable ENTROPY_SRC, then CSRNG, and finally EDN.

## Uninstantiating CSRNG through EDN

To disable and re-enable EDN without disabling and re-enabling CSRNG, firmware must ensure the associated CSRNG instance is properly uninstantiated.
Otherwise, EDN and the associated CSRNG application interface may get out of sync at which point both EDN and CSRNG have to be disabled and re-enabled.
This means unrelated CSRNG instances and EDNs also get disabled and then need to be re-configured.

The procedure for uninstantiating the associated CSRNG instance depends on the mode in which EDN is operating.
- When running in **Software Port Mode**, firmware has to individually trigger commands via the [`SW_CMD_REQ`](registers.md#sw_cmd_req) register.
  The status of the current command can be inferred using the [`SW_CMD_STS`](registers.md#sw_cmd_sts) register.
  For details, refer to [Interaction with CSRNG Application Interface Ports](./theory_of_operation.md#interaction-with-CSRNG-application-interface-ports).
  In case the current command is a `generate` command, firmware must wait for all entropy generated from this command to be consumed before the command is acknowledged by CSRNG (indicated by the `CMD_ACK` bit of the [`SW_CMD_STS`](registers.md#sw_cmd_sts) register being set).
  Firmware can then issue an `uninstantiate` command to destroy the associated CSRNG instance.
  Once the `uninstantiate` command is acknowledged, firmware can safely reconfigure EDN.

- When running in **[Boot-Time Request Mode](./theory_of_operation.md#boot-time-request-mode)**, firmware must first de-assert the `BOOT_REQ_MODE` and `AUTO_REQ_MODE` fields in [`CTRL`](registers.md#ctrl) and then must wait for all boot-time entropy to be consumed.
  EDN then automatically issues an `uninstantiate` command to destroy the associated CSRNG instance.
  Upon completion, the state machine of EDN enters the `SWPortMode` state.
  At this point, EDN has entered Software Port Mode (see above) and firmware can then safely reconfigure EDN.

- When running in **[Auto Request Mode](./theory_of_operation.md#auto-request-mode)**, firmware must first de-assert the `AUTO_REQ_MODE` and `BOOT_REQ_MODE` fields in [`CTRL`](registers.md#ctrl) and then must wait for the current command to complete, after which the state machine of EDN enters the `SWPortMode` state.
  At this point, EDN has entered Software Port Mode (see above), and firmware can issue an `uninstantiate` command to destroy the associated CSRNG instance.
  Once the `uninstantiate` command is acknowledged, firmware can safely reconfigure EDN.

Notes:
- Firmware can infer the EDN state using the [`MAIN_SM_STATE`](registers.md#main_sm_state) register.
- The de-assertion of the `BOOT_REQ_MODE` and `AUTO_REQ_MODE` fields in [`CTRL`](registers.md#ctrl) is only registered by the EDN state machine upon completion of the current command.
  In case of the `generate` command, this means to wait for all entropy generated from this command to have been consumed, which depending on the configuration of the system, may take a very long time.
  To accelerate this process, firmware can for example do the following:
  - For EDN0, repeatedly trigger reseeding operations of the AES PRNGs via the [`PRNG_RESEED` bit of the AES `TRIGGER` register](../../aes/doc/registers.md#trigger--prng_reseed).
    Once all entropy is consumed, the reseed operation doesn't finish anymore and the [`IDLE` bit of the AES `STATUS` register](../../aes/doc/registers.md#status--idle) remains de-asserted.
  - For EDN1 which only interfaces the RND port of OTBN, load and repeatedly run an OTBN program snippet that reads from the RND port such as [`randomness.s`](https://github.com/lowRISC/opentitan/blob/master/sw/otbn/code-snippets/randomness.s).
    Once all entropy is consumed, the program doesn't finish anymore and the [`STATUS` register](../../otbn/doc/registers.md#status) remains at `BUSY_EXECUTE`.

  Future versions of EDN will likely support an automated way for consuming any remaining entropy, see also [Issue #22850](https://github.com/lowRISC/opentitan/issues/22850).

## Running EDN in Auto Request Mode with ENTROPY_SRC disabled

Once the entropy complex has been enabled and all configured CSRNG instances have been seeded with entropy, firmware can again disable ENTROPY_SRC (and the PTRNG noise source to e.g. save power) while CSRNG and EDN remain running to keep serving entropy to consumers.

Depending on the mode in which EDN and the associated CSRNG instance are running, firmware can use a different mechanism to efficiently operate the entropy complex without having the ENTROPY_SRC continuously running:

### Regular, non-deterministic mode

The same guidance applies as for [CSRNG](../../csrng/doc/programmers_guide.md#regular-non-deterministic-mode).

### Fully deterministic mode

The same guidance applies as for [CSRNG](../../csrng/doc/programmers_guide.md#fully-deterministic-mode).
However, the `generate` and `reseed` commands including the additional data fields can only be configured before starting **[Auto Request Mode](./theory_of_operation.md#auto-request-mode)** via the [`GENERATE_CMD`](registers.md#generate_cmd) and [`RESEED_CMD`](registers.md#reseed_cmd) FIFOs.
To inject fresh entropy, firmware thus has to [uninstantiate the CSRNG instance through EDN](#uninstantiating-csrng-through-edn), disable EDN, configure the FIFOs and then re-enable EDN in Auto Request Mode, and finally trigger the `instantiate` command.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_edn.h)
