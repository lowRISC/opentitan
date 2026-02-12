${"#"} Theory of Operation

${"##"} Block Diagram

![RACL Ctrl Block Diagram](./racl_ctrl_block_diagram.svg)

${"##"} Distribution of policies

RACL policies on the system can be configured through [registers](./registers.md) in `racl_ctrl`.
Each policy is specified in a register named after that policy.
The set of policies is then distributed by `racl_ctrl` through a single vector called `racl_policies_o`.

${"##"} Error logs

A subscribing IP can log an error with `racl_ctrl` using the IP's item in the `racl_error_i` port.
Similarly, a RACL error from outside of OpenTitan can be reported through a particular index of the `racl_error_external_i` port.
If multiple errors are logged at the same cycle, arbitration will record the one with the lowest index in this list:
- Items from `racl_error_i` (internal errors)
- Items from `racl_error_external_i` (errors from outside of OpenTitan)
- An error reported by `racl_ctrl` itself.

If there is more than one error reported (concurrently or over several cycles), the `error_log.overflow` field will be set.
The log can be cleared by writing `1` to the `error_log.valid` field.
During a RACL error, `error_log.valid` is set and an interrupt is raised.

${"##"} Alerts and security

A TileLink transaction with incorrect integrity bits will cause a TL integrity error.
This generates a `fatal_fault` alert.
% if enable_shadow_reg:

This instantiation of `racl_ctrl` uses shadowed policy registers.
A storage error (meaning that the shadowed copy is not an inverse) causes the `fatal_fault` alert.
An update error causes the `recov_ctrl_update_err` alert, which is not fatal.
% endif
