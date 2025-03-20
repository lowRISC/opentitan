# RACL: Register Access Control Architecture

## Introduction
A System-on-Chip (SOC) must provide differentiated security on access to registers in the SOC and the CPU.
This document outlines the requirements for such a framework.
The architecture defined in this document follows a multi-level security model.

Each processing element in the SOC, i.e. each component that can actively generate a register read and/or write request, is a subject.
A subject may have one or more roles associated with it and the subject may be allowed to switch between the roles.
For example, a CPU processing element may switch between multiple roles based on the mode of execution.
The set of roles that can be assumed by a subject may also change temporally.
For example, the role of CPU core to configure the system may be restricted to an early window at boot.

Each register that can be accessed by processing elements is an object.
For each object or group of objects, an access-control-list (ACL) is defined that determines if the subject in its current role can read the object and if the subject in its current role can write the object.

The registers that hold the ACL may be hard-wired or may be writable.
If they are writable then the write must be allowed only from the local RoT (Root of Trust) role.

### Subjects and Roles
A role is defined by a 4-bit encoding.
The role encoding is determined by the implementer, and may have different meaning depending on their use case.
The implementation shall provide an abstraction to allow different implementers defining their role assignments based on their needs.

## Register-Access Control List (RACL)

![RACL structure](racl.svg)

In this example, the source processing element can pick between 3 roles - `RoleID0`, `RoleID1`, and `RoleID2`.
The RoleSelector - selects the current role - muxes out the ID corresponding to the current role onto the fabric.
At the target the RACL uses the role and the attributes of the transaction - Read/Write, address, and size - to determine if the access is allowed or denied.
If the access is denied then the error is logged into the Error-Log register.
Source processing elements may have a static role assignment or can support a dynamic role assignment, like in this example.

### RACL rules
1. The IP may group the set of registers in the IP based on this access control model into one or more control groups.
   For each control group there will be a RACL policy picked from one of the [standard RACL policies](#racl-policies).
   An IP should not use a RACL policy other than those specified here.

2. Each RACL takes the form of a pair of permission bitmaps.
   For each RACL implemented by the IP there must be two permission bitmap registers - ReadPerm and WritePerm where each bit in the register corresponds to a role.
   These two registers must be mapped to the control network (CTN) outside of the RoT and must be only readable and writable by the RoT role, i.e., be part of a special ROT_PRIVATE policy (see [RACL policies](#racl-policies)).
   These registers should have reset default defined at design time but these can be updated by RoT at reset if required.

|                 | Role 0 | Role 1 | Role 2 | Role 3 | Role 4 | Role 5 | Role 6 | Role 7 |
|-----------------|:------:|:------:|:------:|:------:|:------:|:------:|:------:|:------:|
| *Bit position:* | *0*    | *1*    | *2*    | *3*    | *4*    | *5*    | *6*    | *7*    |
| `WritePerm`     |        |        |        |        |        |        |        |        |
| `ReadPerm`      |        |        |        |        |        |        |        |        |

3. Each ReadPerm bit indicates if the corresponding role (see column header) has read permission to the group of registers controlled by this ACL.
   Each WritePerm bit indicates if the corresponding role has write permission.
   When the bit is 1, the corresponding permission is provided and when it is 0 it is denied.

4. The following rules must be observed by the IP on a register access:
   - An IP should enforce alignment
      i.  The access must not be wider than the register width and the address of the access must be naturally aligned to the size of the access.
      ii. Not allow a read or write to span multiple registers.
   - If alignment property is violated then treat as if access violates RACL
   - If the transaction is a read then use the “Role” to index into the ReadPerm bitmap of the ACL governing this register to locate the PermR bit.
   - If the transaction is a write then use the “Role” to index into the WritePerm  bitmap of the ACL governing this register to locate the PermW bit.
   - If the transaction is a read and if PermR==0 then RACL is violated.
      + Complete the transaction with dummy data (e.g. 0).
        A design parameter dictates if a bus error is returned or not.
      + Note: It is not okay to hang by not returning a completion as this may be used as a way to mount a denial of service (DoS) attacks by adversaries.
   - If the transaction is a write and if PermW==0 then: RACL is violated:
      + If the transaction semantics is
        * Posted then drop the write
        * Posted-with-Completion-with-no-data then returns a completion.
        * Posted-with-Completion-with-data then returns completion with dummy data (e.g, all 1 or all 0).
        * Note: It is not okay to hang by not returning a completion.
        * A design parameter dictates if a bus error is returned or not.
   - If the RACL was violated
      + If a previously logged error is present then set the overflow bit else Log an error in an error logging register

5. Error-logging register (8-bit) - used to log errors due to RACL violation.
   This register is readable and writable by ROT role and so is governed by the special `ROT_PRIVATE` policy.
   This register should be CTN mapped.
   This register is primarily intended as a debug aid and is not intended to cause any kind of alerts.
   + Bit 6 - `ErrorValid`
     * Set to 1 if a valid error is logged in the register.
   + Bit 5 - `Overflow`
     * A second error occurred when ErrorValid was 1
   + Bit 4 - `Read-or-Write`
     * Set to 0 if a read request violated the RACL
     * Set to 1 if a write/read-modify-write that violated the RACL
   + Bits 3:0 - Role that violated the RACL

## Fabric Requirements
The fabric has a 4-bit field defined in the transaction to carry the role that originated the transaction request such that the ACL rules can be enforced based on the role.
In the case of TLUL, the a_user bits 21 through 18 are used to carry this information.

## Processing Element Requirements
1. Processing elements must not allow the role encodings for a transaction to be mutable under firmware control to a role that is not defined for that processing element.
2. The processing element may obtain the encodings for each role through a set of straps from the SOC.
   Alternatively, the processing element may support a configurable register that allows configuring encodings for each role.
   If such a configurable register exists that register must be access controlled such that it can be only updated by the ROT role.
3. Where an IP supports selecting multiple roles, the mechanism to select the role must be restricted such that a lower privileged entity cannot request a higher privileged role.

## Pass-through processing elements
Some processing elements pass-through transactions received upstream to fabric downstream.
Examples of such processing elements include I/O bridges.
Such bridges must pass through the role verbatim from the upstream to downstream and must not substitute their own role for the downstream transaction.

## RACL policies
A standard set of  RACL policies are defined for the SoC.
The registers that implement the `readPerm` and `writePerm` policy bitmaps shall be mapped at identical CTN addresses in all subsystems and laid out as follows.
The uniform location in each subsystem address space is to simplify RoT firmware if it needs to update these and also for verification simplification.

A single policy called `ALL_RD_WR` is defined to allow all RACL roles to perform read and write access and is defined in the standard set of policies.
A second standard policy `ROT_PRIVATE` is defined to allow only the OpenTitan role to access the registers.
All other policies are custom to the implementer with their needs.
The following table defines the layout for 10 different policies including the two required policies.
Note, the policy registers shall be 64-bit aligned to allow room for future use.

| Name          | Offset | Bits 31:16  | Bits 15:0  |
|---------------|:------:|:-----------:|:----------:|
| `ALL_RD_WR`   | 0x000  | `writePerm` | `readPerm` |
|               | 0x004  | reserved    | reserved   |
| `ROT_PRIVATE` | 0x008  |             | `readPerm` |
|               | 0x00c  | reserved    | reserved   |
| Policy 2      | 0x010  | `writePerm` | `readPerm` |
|               | 0x014  | reserved    | reserved   |
| Policy 3      | 0x018  | `writePerm` | `readPerm` |
|               | 0x01c  | reserved    | reserved   |
| Policy 4      | 0x020  | `writePerm` | `readPerm` |
|               | 0x024  | reserved    | reserved   |
| Policy 5      | 0x028  | `writePerm` | `readPerm` |
|               | 0x02c  | reserved    | reserved   |
| Policy 6      | 0x030  | `writePerm` | `readPerm` |
|               | 0x034  | reserved    | reserved   |
| Policy 7      | 0x038  | `writePerm` | `readPerm` |
|               | 0x03c  | reserved    | reserved   |
| Policy 8      | 0x040  | `writePerm` | `readPerm` |
|               | 0x044  | reserved    | reserved   |
| Policy 9      | 0x048  | `writePerm` | `readPerm` |
|               | 0x04c  | reserved    | reserved   |

### `ALL_RD_WR`
This policy allows read/write access to all RACL roles.
This is intended for use with registers in the SoC that can be written at runtime including by the OS/VMM/drivers operating in S-mode.

|                 | Role 0 | Role 1 | Role 2 | Role 3 | Role 4 | Role 5 | Role 6 | Role 7 |      |
|-----------------|:------:|:------:|:------:|:------:|:------:|:------:|:------:|:------:|------|
| *Bit position:* | *0*    | *1*    | *2*    | *3*    | *4*    | *5*    | *6*    | *7*    |      |
| `WritePerm`     | 1      | 1      | 1      | 1      | 1      | 1      | 1      | 1      | 0xFF |
| `ReadPerm`      | 1      | 1      | 1      | 1      | 1      | 1      | 1      | 1      | 0xFF |

### RACL and other Countermeasures
RACL offers a lightweight, fine-grained access control mechanism to restrict CSR access to specific originators, unlike comprehensive memory safety solutions like CHERI (Capability Hardware Enhanced RISC Instructions).
CHERI is a hardware architecture designed to enhance memory safety in computer systems.
It achieves this by introducing capabilities, which are restricted pointers that only allow access to specific memory regions.
By limiting memory access to these capabilities, CHERI helps prevent memory-related vulnerabilities like buffer overflows and use-after-free attacks.
RACL and CHERI target different needs, are complementary, and can be used in conjunction with.

## Security
RACL is currently not protected against fault attacks.

### RACL_001

- **Asset:**  Registers protected by RACL policy
- **Threat:** Faking RACL role
- **Actor:**
  + Privileged SW adversary in M/S/HS
  + Devices connected to SoC
- **Attack Point(s):** Fabric transactions

Privilege escalation by allowing untrusted roles to tamper/modify registers protected by RACL.

**HW mitigation**
- RACL roles are immutable and cannot be changed by hardware or firmware.
- Where an endpoint can originate multiple roles, the hardware restricts the set of roles that can be selected but not the role ID itself.

### RACL_002

- **Asset:**  RACL policy registers
- **Threat:** Changing policy registers to allow register access by untrusted roles
- **Actor:**
  + Privileged SW adversary in M/S/HS
  + Devices connected to SoC
- **Attack Point(s):** Fabric transactions to read/write RACL policy registers

Privilege escalation by allowing untrusted roles to tamper/modify registers protected by RACL.

**HW mitigation**
- RACL policy registers can be written only by the ROT role.
- Only RoT is allowed to assume the ROT role.
- RACL policy registers reset defaults configured to not allow unprivileged roles by default in the RACL policies.

### RACL_003

- **Asset:**  Registers protected by RACL
- **Threat:** M/S/HS-mode attempting to cause privilege escalation for transactions passing through bridges
- **Actor:**
  + Privileged SW adversary in M/S/HS privilege.
- **Attack Point(s):** Fabric transactions

Components that bridge fabric transactions may substitute the role in incoming transactions with a higher privileged role leading to privilege escalation by allowing untrusted roles to tamper/modify registers protected by RACL.

**HW mitigation**
- Components that bridge fabric requests may substitute the role in incoming transactions must do one of following
  + Pass through the role carried in the original request
  + Demote the role to a lower role

## Implementation

This section describes the proposed tooling enhancements and microarchitectural implementation of RACL.

### Top-level Role and Policy Mapping

The top-level role definition and policy mapping is done via a file racl.hjson.
That file is top-specific and defined by the integrator.
Two keys are defined, roles and policies.
Roles define up to 16 different roles.
The entry policies define an arbitrary number of different policies via policy groups.
In this example the group `default_group` is used.
A policy group contains policies that aggregate different roles for read and write permissions.
One rule must set `rot_private` to `true`, indicating that this policy is used for ROT private register protection.
For every policy group, the tooling creates a register IP that contains the defined policy registers.
```
{
 roles: [
   { name: "ROT",   role_id: 0 }
   { name: "Role1", role_id: 1 }
   { name: "SOC",   role_id: 2 }
 ]
 policies: {
   "default_group": [
     { name: "ALL_RD_WR"
       allowed_rd: [ "ROT", "Role1", "SOC" ]
       allowed_wr: [ "ROT", "Role1", "SOC" ]
     }
     { name: "ROT_PRIVATE"
       rot_private: true
       allowed_rd: [ "ROT" ]
       allowed_wr: [ "ROT" ]
     }
     { name: "SOC_ROT"
       allowed_rd: [ "ROT", "SOC" ]
       allowed_wr: [ "ROT", "SOC" ]
     }
    ]
  }
}
```

### Instance-level Policy Mapping

RACL policies apply on a per-instance basis, meaning that different instances of the same IP have a different RACL policy.
To do so, the integrator has to define a mapping of each register of an instance to one of the policies defined in `racl.hjson`.
An example mapping can be seen below, defining the mapping for a SPI host.
The mapping is defined as a single HJSON file per instance, and is added as a new entry in the top-level HJSON definition:
```
{
 policy_group: "default_group"
 policy_mapping: {
   "INTR_STATE"   : "ROT_PRIVATE"
   "INTR_ENABLE"  : "ROT_PRIVATE"
   "INTR_TEST"    : "ROT_PRIVATE"
   "ALERT_TEST"   : "ROT_PRIVATE"
   "CONTROL"      : "ROT_PRIVATE"
   "STATUS"       : "ALL_RD_WR"
   "CONFIGOPTS"   : "ROT_PRIVATE"
   "CSID"         : "ROT_PRIVATE"
   "COMMAND"      : "ROT_PRIVATE"
   "RXDATA"       : "ROT_PRIVATE"
   "TXDATA"       : "ROT_PRIVATE"
   "ERROR_ENABLE" : "ROT_PRIVATE"
   "ERROR_STATUS" : "SOC_ROT"
   "EVENT_ENABLE" : "ROT_PRIVATE"
 }
}
```

This instance mapping is added to the instantiation in the top-level HJSON as defined as follows.
If no RACL mapping is provided to an instance, the instance does not use RACL and no overhead is generated.
```
{ name: "mbx0",
  type: "mbx",
  clock_srcs: {clk_i: "main"}
  clock_group: "infra",
  reset_connections: {rst_ni: "lc"},
  base_addrs: {
   core: {hart: "0x22000000"},
   soc:  {soc_mbx: "0x01465000"},
  },
  racl: {
   soc: "mbx_soc_racl_mapping.hjson"
 }
}
```

In this example, RACL is only inferred for the SOC interface of the mailbox. If the racl entry is not provided, no RACL logic is generated.

### RTL Implementation

RACL is opt-in.
If no `racl.hjson` is defined in the top-level HJSON and no RACL mappings are used there, no RACL logic is generated.
There will be no logic overhead to the design (see [System with No RACL Use](#system-with-no-racl-use) for details).

![Implementation structure](implementation.svg)

For every RACL group defined in a top-specific `racl.hjson`, the tooling will generate a parametrized RACL policy widget.
This widget implements the policy registers (statically protected via the ROT_PRIVATE policy) and exposes all policies via a top-level vector.

![Connections](connections.svg)

The RACL policy vector gets distributed to all IPs that assign to that RACL group.
The RACL policy vector, along with a static per-instance selection vector is routed to the IP that subscribes to RACL.
A RACL supported IP’s top-level I/O interface is changed to include the following IO signals:
```
input  racl_policy_t racl_policies_i[N_POLICIES],
input  int           racl_policy_sel_i[N_IP_REGS],
output logic         racl_violation_o,
output logic [3:0]   racl_violating_role_o
```

These wires are routed to the internal reg\_top.
If IPs use more than one reg\_top, each reg\_top will get a dedicated selection vector.
- `racl_policies_i`: A vector of all possible policies defined by `racl.hjson`.
  This is coming from the RACL policy widget.
- `racl_policy_sel_i`: A vector of indices that select the policy from the policy vector.
  Entry 0 of this array defines the policy selection for register 0 in that IP, entry 1 defines the selection for register 1, etc.
  In the example from above, the vector might look like `[1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 1]`.
  + If an IP features multiple reg\_tops, each will have its own `racl_policy_sel_<reg_top_name>_i` policy selector input.
    `racl_violation_o` will then be the OR combination of violations among reg\_tops.
    The current architecture is designed to handle only one RACL violation at a time.
    If multiple RACL violations can occur simultaneously, for instance, when the same policy widget is used across different TLUL crossbar hierarchies, it becomes necessary to separate the RACL policy widgets.
    To address this, an additional RACL policy widget should be instantiated for each crossbar hierarchy.
    This ensures that only one violation can occur within each hierarchy at any given time.

#### RACL Integration to IPs
While adding new inputs might be an intrusive change, it gives the system the most flexibility.
RACL is designed to protect registers, thus the protection at register-level is natural.
At this stage, i.e., at reg_top level, all the necessary register decoding is already existing, such that the permission checks have the least RTL impact.
Furthermore, by including RACL at the IP level, it makes it possible to use IPs and RACL in a non-topgen architecture, where IPs are manually instantiated.

Further, the integration to TLUL seems not the right choice.
TLUL provides the physical layer for supporting RACL, i.e., providing the user bits.
RACL itself, however, can be implemented on other bus fabrics.
In a larger SoC, there might be even different bus fabrics available.

#### System with No RACL Use
The system supports instantiating IPs with and without RACL alongside.
If an IP is instantiated in a non-RACL use case, no overhead is added to the IP.
The additional inputs are tied off, and the outputs are left open.
Inside the IP, the RACL comparison logic is gated via a per-instance synthesis parameter, hence the (unused) RACL logic appears neither in synthesis nor in DV.
If the system does not use RACL at all, there is no overhead in terms of additional transported bits in the crossbar.
