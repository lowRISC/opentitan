# Programmer's Guide

RACL Control can be configured through its [registers](./registers.md).

## RACL Policies

Each RACL policy has a register named after the policy which contains a permission bitmap for read and write permissions for each of the roles defined in the top-level configuration.
The exact register layout is defined in [RACL: Register Access Control List](../../../../../doc/contributing/hw/racl/README.md#racl-policies).
Once set, the policies (i.e. permission bitmaps) are distributed to all subscribing IPs and used for subsequent RACL access checks.

## Interrupts

When a RACL error occurs, an interrupt is raised.
Interrupts are disabled by default but can be enabled via the [`INTR_ENABLE`](./registers.md#intr_enable) register.

## Error Logs

When a RACL error occurs, the following information about the error is logged in the [`ERROR_LOG`](./registers.md#error_log) and [`ERROR_LOG_ADDRESS`](./registers.md#error_log_address) registers.

- `ERROR_LOG_ADDRESS` contains the address, shifted by 2 bits to the right, on which a RACL violation occurred.
- `ERROR_LOG.valid` indicates that the log registers contain valid data.
- `ERROR_LOG.overflow` indicates that a RACL error occurred while the `valid` bit was set or that more than one error was reported in the same clock cycle.
- `ERROR_LOG.read_access` states whether the RACL error occurred due to a read (`1`) or write (`0`) operation.
- `ERROR_LOG.role` states the RACL roles that caused the error.
- `ERROR_LOG.ctn_uid` contains the CTN UID that caused the error.

The log can be cleared by writing `1` to the `error_log.valid` field.

## Programming Sequence

### Initializing the IP

A typical programming sequence for initializing the IP looks as follows:

1. For each of the `POLICY_*` registers, program them with the desired read/write permissions for each of the roles. This step is only necessary if the default values are not sufficient.
2. Set up an interrupt service routine for the interrupt of this IP and configure the PLIC accordingly.
2. Enable interrupts by writing to the [`INTR_ENABLE`](./registers.md#intr_enable) register.
3. Optionally, check if any RACL error has occured before interrupts were enabled by reading `ERROR_LOG.valid`.

### Checking for and handling RACL errors

A typical programming sequence for checking the RACL errors is as follows:

1. Wait for a RACL interrupt or periodically poll the `ERROR_LOG.valid` bit.
2. Read the `ERROR_LOG_ADDRESS` register.
3. Read the `ERROR_LOG` register.
4. Handle the error
5. Clear the log entry by writing `1` to the `ERROR_LOG.valid` bit.
