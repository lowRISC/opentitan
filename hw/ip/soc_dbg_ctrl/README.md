# SoC Debug Control (soc_dbg_ctrl)

## Debug Categories

Debugging in RISC-V can be done using one of the following mechanisms:

1. Category 1 - Native debugging (a.k.a. self-hosted debug) through M-mode using debug ISA
Please see Section 4 of the RISC-V debug specification for more details.
2. Category 2: Hardware debuggers using  the debug non-ISA (including direct bus access)
Debug features (e.g., fabric trace, etc.) made available to customers.
3. Category 3: Hardware debuggers using DFD/DFT features such as array freeze/dump, scan, etc.
4. Category 4: Hardware debuggers using DFD/DFT features such as array freeze/dump, scan, etc. on an unfused/pre-production part.

Category 1, i.e., the native debugging is completely under control of software and needs no additional security controls.

The Category 2 and Category 3 debuggers are a security concern.
With Category 2 and 3 debuggers an attacker can walk up to a machine running a production software stack and have run control on the software.
This can be used to for example subvert secure boot, subvert TEEs, steal secrets from operating systems (e.g., login credentials, etc.), etc. Category 3 is further invasive and could lead to loss of IP.
Further, these capabilities can be used as part of a supply chain poisoning attack where attack devices connected to the JTAG pins on the motherboard may be used to subvert targeted victims.

Category 4 debugging is enabled on unfused/pre-production parts. No debug authorization is required on such parts.
Category 3 debugging is controlled through vendor provisioned debug authorization.
Category 2 debugging is controlled through an owner-provided debug authorization.
The debug authorization for Category 3 will be based on part-unique secrets provisioned by the vendor. The debug authorization for Category 2 may be based on a global secret or a per-part secret.

At early boot (please see Integrated OpenTitan: Design for Test and Debug Support) RoT opens up the debug authorization window and if a debug is authorized (Category 2 and/or Category 3 and/or Category 4), the RoT drives the debug policy bus to all TAPs/DebugModules.
The TAPs/DebugModules reject any requests classified as Category 3 unless a Category 3 or Category 4 debug is authorized.
The TAP/debugModules reject any requests classified as Category 2 unless Category 2 or Category 3 or Category 4 debugging is authorized.

If a Category 3 debug is authorized, then the debug enabled is fed into the creator root key derivation.
If a Category 2 debug was authorized, the debug enabled is fed into the owner root key derivation.
Note that there are no secrets in the part when Category 4 debug is authorized.

In any case the authenticated bit in dmstatus register reflects that an authorization was done.
The debug policy - CAT2_UNLOCKED and/or CAT3_UNLOCKED and/or CAT4_UNLOCKED gets broadcast to all TAPs/DebugModules in the system, which must use this debug policy to accept/reject debug commands.
For most debug modules CAT4_UNLOCKED opens up the same debug capabilities as CAT3_UNLOCKED.
Units that need to distinguish between a pre-production and post-production part can differentiate debug actions for CAT4_UNLOCKED and CAT3_UNLOCKED.

## Debug Authorization Window

The debug authorization protocol and interfaces are defined in Integrated OpenTitan: Design for Test and Debug Support.

Before the owner and creator root keys are finalized, the ROM obtains an indication from the debugger if there is an intent to debug.
If there is an intent to debug then the intent to debug is fed into the creator and/or owner root key derivation.
The authorization itself is deferred to be done by the ROM extension or  a bootstrapped firmware.
The ROM stage thereafter indicates which level authorization can be accepted by the ROM extension / bootstrap firmware.
If an intent to debug was signaled then the ROM extension / bootstrap firmware opens up a window for accepting debug authorization before starting the creator and owner root key derivations.
If authorization is not performed in this window then no further authorization is allowed till the next reset.

Some owners may require the owner password to be also asserted to allow Category 3 debugging.
When the owner has activated this capability - owner authorized debug - the RoT will require the debugger to first authorize for Category 2 before authorizing for Category 3.

During this flow, the ROT firmware drives all status bits related to the debug control.
Integrated OpenTitan: Design for Test and Debug Support defines various status bits such as debug_auth_window/open etc.
These status bits are mirrored to the debugger accessible JTAG interface, allowing debuggers to read the debug authorization status of the system.

## Relock

Following a successful debug authorization, the debugger may wish to relock the debug interface.
In order to relock the debug interface, the debugger specifies a password which the debugger can use to re-unlock the part later by providing the password.
When relocking the device, the RELOCKED field in DEBUG_POLICY_RELOCKED shall be set to `Mubi4::True`.

## Re-unlock

The debugger can request a re-unlock with a previously provided password.
The RoT firmware clears the RELOCKED bit in DEBUG_POLICY_RELOCKED if:

1. CAT2_UNLOCKED or CAT3_UNLOCKED bit is `Mubi4::True`
2. The password matches the password previously provided at the time re-lock

Following a re-unlock, the RoT clears the re-unlock password.
If the debugger needs to relock it must re-establish a password.
On re-lock, the RELOCKED bit is set to `Mubi4::True` again if:

1. CAT2_UNLOCKED or CAT3_UNLOCKED bit is `Mubi4::True`

The RoT should send the updated state of the RELOCKED bit to other subsystems.

## Debug Policy Bus

The debug policy is determined by the RoT and written to the debug policy CSRs in the RoT.
The debug policy CSRs are broadcast to all TAPs/Debug modules in the SOC through a debug policy bus.

![](./doc/debug_policy_bus.svg)

The debug policy bus encompasses the fields of all three CSRs:

* Debug_policy_valid - corresponds to the valid field in the DEBUG_POLICY_VALID CSR.
* Debug_policy_relocked - corresponds to the relocked field in the DEBUG_POLICY_RELOCKED CSR.
* Debug_policy - maps to the set debug category in the DEBUG_POLICY_CATEGORY CSR.
