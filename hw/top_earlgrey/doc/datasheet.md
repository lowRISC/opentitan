# OpenTitan Earl Grey (Discrete Chip) Datasheet

# Overview

![Top Level Block Diagram](top_earlgrey_block_diagram.svg)

The OpenTitan Earl Grey chip is a low-power secure microcontroller that is designed for several use cases requiring hardware security.
The block diagram is shown above and shows the system configuration, including the Ibex processor and all of the memories and comportable IPs.

As can be seen in the block diagram, the system is split into a fast processor core domain that runs on a 100MHz jittery clock, and a peripheral domain that runs at 24MHz.
Further, a portion of the peripheral domain, the analog sensor top and the padring can stay always-on.
The rest of the system can be shut off as part of the sleep mode.

The OpenTitan Earl Grey chip provides the following features:

<table>
<thead style='font-size:100%'>
  <tr>
    <th colspan="2">OpenTitan Earl Grey Features</th>
  </tr>
</thead>
<tbody style='font-size:90%;line-height:110%'>
  <tr>
    <td>
      <ul>
        <li>RV32IMCB RISC-V "Ibex" core:
          <ul>
            <li>3-stage pipeline, single-cycle multiplier</li>
            <li>Support for the full ratified bit manipulation extension and some unratified subsets</li>
            <li>4KiB instruction cache with 2 ways</li>
            <li>RISC-V compliant JTAG DM (debug module)</li>
            <li>PLIC (platform level interrupt controller)</li>
            <li>U/M (user/machine) execution modes </li>
            <li>Enhanced Physical Memory Protection (ePMP)</li>
            <li>Security features:
              <ul>
                <li>Low-latency memory scrambling on the icache</li>
                <li>Dual-core lockstep configuration</li>
                <li>Data independent timing</li>
                <li>Dummy instruction insertion</li>
                <li>Bus and register file integrity</li>
                <li>Hardened PC</li>
              </ul>
            </li>
          </ul>
        </li>
        <br></br>
        <li>Security peripherals:
          <ul>
            <li>AES-128/192/256 with ECB/CBC/CFB/OFB/CTR modes</li>
            <li>HMAC / SHA2-256</li>
            <li>KMAC / SHA3-224, 256, 384, 512, [c]SHAKE-128, 256</li>
            <li>Programmable big number accelerator for RSA and ECC (OTBN)</li>
            <li>NIST-compliant cryptographically secure random number generator (CSRNG)</li>
            <li>Digital wrapper for analog entropy source with FIPS and CC-compliant health checks</li>
            <li>Key manager with DICE support</li>
            <li>Manufacturing life cycle manager</li>
            <li>Alert handler for handling critical security events</li>
            <li>OTP controller with access controls and memory scrambling</li>
            <li>Flash controller with access controls and memory scrambling</li>
            <li>ROM and SRAM controllers with low-latency memory scrambling</li>
          </ul>
        </li>
      </ul>
    </td>
    <td>
      <ul>
        <li>Memory:
          <ul>
            <li>2x512KiB banks eFlash</li>
            <li>128KiB main SRAM</li>
            <li>4KiB Always ON (AON) retention SRAM</li>
            <li>32KiB ROM</li>
            <li>2KiB (=16kibit) OTP</li>
          </ul>
        </li>
        <br></br>
        <li>IO peripherals:
          <ul>
            <li>47x multiplexable IO pads with pad control</li>
            <li>32x GPIO (using multiplexable IO)</li>
            <li>4x UART (using multiplexable IO)</li>
            <li>3x I2C with host and device modes (using multiplexable IO)</li>
            <li>SPI device (using fixed IO) with TPM, generic, flash and passthrough modes</li>
            <li>2x SPI host (using both fixed and multiplexable IO)</li>
            <li>USB device at full speed</li>
          </ul>
        </li>
        <br></br>
        <li>Other peripherals:
          <ul>
            <li>Clock, reset and power management</li>
            <li>Fixed-frequency timer</li>
            <li>Always ON (AON) timer</li>
            <li>Pulse-width modulator (PWM)</li>
            <li>Pattern Generator</li>
          </ul>
        </li>
        <br></br>
        <li>Software:
          <ul>
            <li>Boot ROM code implementing secure boot and chip configuration</li>
            <li>Bare metal top-level tests</li>
            <li>OpenTitan Crypto Library with OTBN accelerated standard algorithms for </li>
            <ul>
              <li>RSA 2K, 3K, 4K</li>
              <li>ECC with NIST P256/P384, Brainpool P256r1 or X25519/Ed25519</li>
              <li>SHA2-256, 384, 512</li>
            </ul>
            <li>SPHINCS+ PQ-secure boot using a stateless hash-based signatures scheme</li>
          </ul>
        </li>
      </ul>
    </td>
  </tr>
</tbody>
</table>

# Detailed Specification

For more detailed documentation including the pinout and system address map, see [OpenTitan Earl Grey Chip Specification](./design/README.md).
The [OpenTitan Earl Grey Chip DV Document](../dv/README.md) describes the chip-level DV environment and contains the chip-level test plan.
