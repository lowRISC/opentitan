---
title: Lightweight Threat Model
---

This threat model aims to identify in-scope design assets, attacker profiles,
attack methods and attack surfaces. This is used to produce security
requirements and implementation guidelines that cover hardware, software and the
design process.

The threat model is considered for discrete and integrated instances of
OpenTitan which may include external non-volatile memory.

**Assets**

*   Secrets and configuration parameters stored in the device or on external
    memory:
    *   Private asymmetric keys (integrity and confidentiality)
    *   Symmetric keys (integrity and confidentiality)
    *   Anti-rollback and other counters (integrity)
    *   Unique identifiers and data (integrity, authenticity and partly
        confidentiality)
    *   Data requiring integrity and/or confidentiality
*   Secrets stored outside the device (e.g. in a backend system), but that are
    used to support critical functionality or lifecycle operations
*   Integrity and authorization of cryptographic operations
*   Integrity and authenticity of the code running on the device
*   Integrity and authenticity of stored data
*   Confidentiality of selected code and data
*   Quality of the entropy source used in cryptographic operations and that used
    in countermeasures
*   Correct operation and confidentiality, integrity, authenticity of
    cryptographic services.

**Attacker Profile**

*   A bad actor with physical access either during manufacturing or active
    deployment
*   Malicious device owners: *e.g.* attacking one device to develop template
    attacks
*   Malicious actors with remote device access: *e.g.* performing remote
    measurements of side channels that expose assets

**Attack Surface**

*   Chip surface
    *   Electrical stimulation and/or measurements
    *   Energy and particle exposure
    *   Inspection and reverse engineering
    *   Physical manipulation
*   Operational environment
    *   Temperature
    *   Power
*   Peripheral interfaces
*   Protocols and APIs at the boundary of the device
*   Test and debug interfaces
*   Clock, power, reset lines
*   Documentation and design data

**Attack Methods**

*Logical Attacks*

*   Software vulnerabilities (e.g. bugs) exercised through interfaces or code
    that can be run by the attacker on the device
*   Compromise of secure boot
*   Insider compromise of the personalization process
*   Cryptanalysis
*   Silicon Creator or Silicon Owner impersonation
*   Compromise through misuse of test or debug functionality

*Non-Volatile Memory Attacks*

*   Firmware downgrade
*   Data rollback
*   Data/Command playback

*Physical Access Attacks*

*   Side Channel Analysis (SCA): Passive measurement attacks where the device is
    operated normally. The attacker extracts the assets (*e.g.* secrets) via
    observation of side channels, such as: 1) execution time, 2) power
    consumption, 3) electromagnetic radiation.
*   Fault Injection (FI): Fault Injection is a class of active attacks where the
    device’s input and/or operation conditions are manipulated to make the
    device operate outside its specification. An attacker modifies device
    behavior (data and/or operations) by manipulating the internal electrical
    state of the device (voltage, current, charge) through disturbances such as
    voltage/current, EM, lasers, or body-bias injection.
*   Any combination of passive and active physical attacks.

## Read More

*   [Use Cases]({{< relref "doc/use_cases" >}})
*   [OpenTitan Security]({{< relref "../../security" >}})
