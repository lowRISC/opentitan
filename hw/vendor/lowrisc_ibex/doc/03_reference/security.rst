.. _security:

Security Features
=================

Ibex implements a set of extra features (when the SecureIbex parameter is set) to support security-critical applications.
All features are runtime configurable via bits in the **cpuctrl** custom CSR.

Outputs
-------

Ibex has two alert outputs for signalling security issues.
The major alert (**alert_major_o**) indicates a critical security issue from which the core cannot recover.
The minor alert (**alert_minor_o**) indicates potential security issues which can be monitored over time by a system.

Data Independent Timing
-----------------------

When enabled (via the **data_ind_timing** control bit in the **cpuctrl** register), execution times and power consumption of all instructions shall be independent of input data.
This makes it more difficult for an external observer to infer secret data by observing power lines or exploiting timing side-channels.

In Ibex, most instructions already execute independent of their input operands.
When data-independent timing is enabled:
* Branches execute identically regardless of their taken/not-taken status
* Early completion of multiplication by zero/one is removed
* Early completion of divide by zero is removed

Dummy Instruction Insertion
---------------------------

When enabled (via the **dummy_instr_en** control bit in the **cpuctrl** register), dummy instructions will be inserted at random intervals into the execution pipeline.
The dummy instructions have no functional impact on processor state, but add some difficult-to-predict timing and power disruption to executed code.
This disruption makes it more difficult for an attacker to infer what is being executed, and also makes it more difficult to execute precisely timed fault injection attacks.

The frequency of injected instructions can be tuned via the **dummy_instr_mask** bits in the **cpuctrl** register.

+----------------------+----------------------------------------------------------+
| **dummy_instr_mask** | Interval                                                 |
+----------------------+----------------------------------------------------------+
| 000                  | Dummy instruction every 0 - 4 real instructions          |
+----------------------+----------------------------------------------------------+
| 001                  | Dummy instruction every 0 - 8 real instructions          |
+----------------------+----------------------------------------------------------+
| 011                  | Dummy instruction every 0 - 16 real instructions         |
+----------------------+----------------------------------------------------------+
| 111                  | Dummy instruction every 0 - 32 real instructions         |
+----------------------+----------------------------------------------------------+

Other values of **dummy_instr_mask** are legal, but will have a less predictable impact.

The interval between instruction insertion is randomized in the core using an LFSR.
Sofware can periodically re-seed this LFSR with true random numbers (if available) via the **secureseed** CSR.
This will make the insertion interval of dummy instructions much harder for an attacker to predict.

Note that the dummy instruction feature inserts multiply and divide instructions.
The core must be configured with a multiplier (`RV32M != ibex_pkg::RV32MNone`) or errors will occur using this feature.

Register file ECC
-----------------

When Ibex is configured with the SecureIbex parameter, ECC checking is added to all reads of the register file.
This can be useful to detect fault injection attacks since the register file covers a reasonably large area.
No attempt is made to correct detected errors, but an external alert is raised for the system to take action.

Hardened PC
-----------

This adds a check that the PC driven from the IF stage has not been modified.
A check is asserted that the current IF stage PC equals the previous PC plus the correct increment.
The check is disabled after branches and after reset.
If a mismatch is detected, a major alert is signaled.

Shadow CSRs
-----------

Certain critical CSRs (`mstatus`, `mtvec`, `cpuctrl`, `pmpcfg` and `pmpaddr`) have extra glitch detection enabled.
This creates a second copy of the register which stores a complemented version of the main CSR data.
A constant check is made that the two copies are consistent, and a major alert is signalled if not.
