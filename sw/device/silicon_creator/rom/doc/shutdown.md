# Mask ROM Shutdown Module

## Objective

The Shutdown module is responsible for securely shutting down the OpenTitan chip in the event of an unrecoverable fault during the secure boot process.
A secure shutdown should result in a system end-state where a chip reset is the only viable option.

## Dependencies

Hardware:
*   [Alert Handler](https://docs.opentitan.org/hw/ip/alert_handler/doc/)
*   OTP Controller & Shutdown OTP policy words defined.
*   Lifecycle controller

Software:
*   Alert Handler Driver
*   OTP Driver
*   PMP
*   Lifecycle Driver

## Implementation Details

The shutdown module will make use of the alert handler to detect shutdown-worthy events within the hardware.
Hardware and software shutdown events will use the alert manager to cause an escalation resulting in chip shutdown.

### Alert Class Specification

The Mask ROM will categorize shutdown events into the categories shown below.
OTP words will be used to configure how the ROM will configure Alert Handler’s response to each class of alert.

| Alert Handler Class   | Severity   | Description                                                   |
|-----------------------|------------|---------------------------------------------------------------|
| Class A               | Fatal      | Chip cannot boot.  Immediate shutdown & reboot recommended.   |
| Class B               | Near-Fatal | Intrusion detected.  Immediate shutdown & reboot recommended. |
| Class C               | Severe     | Malfunction detected.                                         |
| Class D               | Minor      | Recoverable error detected.                                   |

### Alert Escalation Per-Class

The ROM’s alert escalation policy will be defined by OTP words.
The suggested default policy is detailed in the following table.
Class A configured alerts will have their configuration locked by the Mask ROM.
All other classes may be reconfigured and locked later by either ROM\_EXT or owner code.

| Alert Handler Class   | Escalation   | Enabled by ROM   | Locked by ROM   |
|-----------------------|--------------|------------------|-----------------|
| Class A               | Shutdown     | Yes              | Yes             |
| Class B               | Shutdown     | Yes              | No              |
| Class C               | No Response  | No               | No              |
| Class D               | No Response  | No               | No              |
| Class X               | Disabled     | No               | No              |

Note: Class X isn’t a real alert handler classification.
It refers to a configuration where an alert is neither classified nor armed.

### Alert Escalation Phase Actions

The alert handler allows each alert class to enable a number of escalation phases which map to certain actions.
The specific action at each escalation phase (0-3) is left as a top-level integration decision.
In the OpenTitan first silicon, the escalation actions are detailed in the following table.

| Escalation Phase   | Action        |
|--------------------|---------------|
| Phase 0            | NMI to CPU    |
| Phase 1            | Wipe Secrets  |
| Phase 2            | Virtual Scrap |
| Phase 3            | Reset         |

### Alert Escalation Phase Configuration

For each class of alert, there are tunable counts and timers which control how the alert escalation starts and proceeds through the escalation phases.
For each class of alert, we’ll provide OTP configurations for the following:

| Name                   | Class A    | Class B    |   Class C(No response) |   Class D(No response) |
|------------------------|------------|------------|------------------------|------------------------|
| Accumulation Threshold | 0          | 0          |                      0 |                      0 |
| Timeout Cycles         | 0          | 0          |                      0 |                      0 |
| Phase 0 Cycles         | 0          | 0          |                      0 |                      0 |
| Phase 1 Cycles         | 10         | 10         |                      0 |                      0 |
| Phase 2 Cycles         | 10         | 10         |                      0 |                      0 |
| Phase 3 Cycles         | 0xFFFFFFFF | 0xFFFFFFFF |                      0 |                      0 |



### Alert Event Classification

There are approximately 30 different alert sources for the Alert Handler.
The ROM will use OTP words to assign each of these alerts a class, and thus, an escalation response.
The escalation response can vary based on the lifecycle state of the chip.
The suggested default classification is detailed in the following table.


| Name                         | ID   | RAW/TEST   | PROD   | PROD_END   | DEV   | RMA   | SCRAP   |
|------------------------------|------|------------|--------|------------|-------|-------|---------|
| Uart0FatalFault              | 0    | X          | C      | C          | X     | X     | X       |
| Uart1FatalFault              | 1    | X          | C      | C          | X     | X     | X       |
| Uart2FatalFault              | 2    | X          | C      | C          | X     | X     | X       |
| Uart3FatalFault              | 3    | X          | C      | C          | X     | X     | X       |
| GpioFatalFault               | 4    | X          | C      | C          | X     | X     | X       |
| SpiDeviceFatalFault          | 5    | X          | C      | C          | X     | X     | X       |
| SpiHost0FatalFault           | 6    | X          | C      | C          | D     | X     | X       |
| SpiHost1FatalFault           | 7    | X          | C      | C          | D     | X     | X       |
| I2c0FatalFault               | 8    | X          | C      | C          | X     | X     | X       |
| I2c1FatalFault               | 9    | X          | C      | C          | X     | X     | X       |
| I2c2FatalFault               | 10   | X          | C      | C          | X     | X     | X       |
| PattgenFatalFault            | 11   | X          | C      | C          | X     | X     | X       |
| RvTimerFatalFault            | 12   | X          | C      | C          | X     | X     | X       |
| UsbdevFatalFault             | 13   | X          | C      | C          | X     | X     | X       |
| OtpCtrlFatalMacroError       | 14   | X          | A      | A          | D     | X     | X       |
| OtpCtrlFatalCheckError       | 15   | X          | A      | A          | D     | X     | X       |
| OtpCtrlFatalBusIntegError    | 16   | X          | A      | A          | D     | X     | X       |
| LcCtrlFatalProgError         | 17   | X          | A      | A          | D     | X     | X       |
| LcCtrlFatalStateError        | 18   | X          | A      | A          | D     | X     | X       |
| LcCtrlFatalBusIntegError     | 19   | X          | A      | A          | D     | X     | X       |
| PwrmgrAonFatalFault          | 20   | X          | C      | C          | X     | X     | X       |
| RstmgrAonFatalFault          | 21   | X          | C      | C          | X     | X     | X       |
| ClkmgrAonRecovFault          | 22   | X          | C      | C          | X     | X     | X       |
| ClkmgrAonFatalFault          | 23   | X          | C      | C          | X     | X     | X       |
| SysrstCtrlAonFatalFault      | 24   | X          | C      | C          | X     | X     | X       |
| AdcCtrlAonFatalFault         | 25   | X          | C      | C          | X     | X     | X       |
| PwmAonFatalFault             | 26   | X          | C      | C          | X     | X     | X       |
| PinmuxAonFatalFault          | 27   | X          | C      | C          | X     | X     | X       |
| AonTimerAonFatalFault        | 28   | X          | C      | C          | X     | X     | X       |
| SensorCtrlRecovAlert         | 29   | X          | C      | C          | X     | X     | X       |
| SensorCtrlFatalAlert         | 30   | X          | C      | C          | X     | X     | X       |
| SramCtrlRetAonFatalIntgError | 31   | X          | B      | B          | D     | X     | X       |
| FlashCtrlRecovErr            | 32   | X          | D      | D          | D     | X     | X       |
| FlashCtrlFatalErr            | 33   | X          | A      | A          | D     | X     | X       |
| RvDmFatalFault               | 34   | X          | C      | C          | X     | X     | X       |
| RvPlicFatalFault             | 35   | X          | C      | C          | X     | X     | X       |
| AesRecovCtrlUpdateErr        | 36   | X          | D      | D          | D     | X     | X       |
| AesFatalFault                | 37   | X          | A      | A          | D     | X     | X       |
| HmacFatalFault               | 38   | X          | A      | A          | D     | X     | X       |
| KmacFatalFault               | 39   | X          | A      | A          | D     | X     | X       |
| KeymgrFatalFaultErr          | 40   | X          | A      | A          | D     | X     | X       |
| KeymgrRecovOperationErr      | 41   | X          | D      | D          | D     | X     | X       |
| CsrngRecovAlert              | 42   | X          | D      | D          | D     | X     | X       |
| CsrngFatalAlert              | 43   | X          | A      | A          | D     | X     | X       |
| EntropySrcRecovAlert         | 44   | X          | D      | D          | D     | X     | X       |
| EntropySrcFatalAlert         | 45   | X          | A      | A          | D     | X     | X       |
| Edn0FatalAlert               | 46   | X          | A      | A          | D     | X     | X       |
| Edn0RecovAlert               | 47   | X          | D      | D          | D     | X     | X       |
| Edn1FatalAlert               | 48   | X          | A      | A          | D     | X     | X       |
| Edn1RecovAlert               | 49   | X          | D      | D          | D     | X     | X       |
| SramCtrlMainFatalError       | 50   | X          | A      | A          | D     | X     | X       |
| OtbnFatal                    | 51   | X          | A      | A          | D     | X     | X       |
| OtbnRecov                    | 52   | X          | D      | D          | D     | X     | X       |
| RomCtrlFatal                 | 53   | X          | A      | A          | D     | X     | X       |
| RvCoreIbexFatalSwErr         | 54   | X          | A      | A          | D     | X     | X       |
| RvCoreIbexRecovSwErr         | 55   | X          | D      | D          | D     | X     | X       |
| RvCoreIbexFatalHwErr         | 56   | X          | A      | A          | D     | X     | X       |
| RvCoreIbexRecovHwErr         | 57   | X          | D      | D          | D     | X     | X       |

| Name                         | ID   | RAW/TEST   | PROD   | PROD_END   | DEV   | RMA   | SCRAP   |
|------------------------------|------|------------|--------|------------|-------|-------|---------|
| Alert Ping Fail              |      | X          |        |            |       | X     | X       |
| Alert Escalation Fail        |      | X          |        |            |       | X     | X       |
| Alert Integrity Fail         |      | X          |        |            |       | X     | X       |
| Integrity Escalation Fail    |      | X          |        |            |       | X     | X       |
| Bus Integrity Failure        |      | X          |        |            |       | X     | X       |
| Shadow Reg Update Failure    |      | X          |        |            |       | X     | X       |
| Shadow Reg Storage Error     |      | X          |        |            |       | X     | X       |

#### Notes
- In the RAW and TEST states, OTP may not be programmed yet.
- In the RMA state, the chip has been returned for failure analysis.  No alerts should be configured.
- In the SCRAP state the CPU cannot execute code and the cryptographic peripherals cannot perform any operations so alert configuration is irrelevant.

### Mask ROM (software) Events

There are a number of software conditions which may cause the Mask ROM to need to shut down the chip.
These shutdown events will cause the Mask ROM to use the software alert mechanism to shut down the chip.
In addition to scheduling a software alert, the shutdown module will make a best-effort to place the chip into a non-functional state.

These events include:
*   No bootable image in either flash partition.
*   Boot Policy forbids booting (e.g. policy says boot “A” with no fallback to B, but A is invalid).
*   Errors during initialization of any ROM modules.
*   Any interrupt or CPU exception.

### Software Shutdown

In the event that a software shutdown event is detected, software will perform the following actions to safely shutdown the chip:

1. Schedule a software alert escalation.
2. Disable all PMP regions except ROM. (may need to be re-ordered).
3. Disable crypto and keymanager blocks (send to virtual scrap state).
4. Disable all memories except ROM.
5. Shutdown
6. Hardened spin-loop to prevent glitching to further execution.

The software shutdown handler will be strategically located in the ROM to allow for the most severe PMP lockdown and to make glitching out more difficult.

### Proposed API

### Public APIs

```c
// Reads OTP, initializes the Alert Handler, configures all interrupts
// and exceptions to enter shutdown_finalize.
void shutdown_init(void);

// Schedules a software alert escalation, then:
// - Disable all PMP regions except ROM.
// - Disable crypto and keymgr blocks (sent to virtual scrap state).
// - Disable all memories except ROM.
// - Shutdown the chip.
// - Wait for watchdog reboot.
// - while(true) { asm("wfi"); }  // Note: this needs to be hardened against glitches.
void shutdown_finalize(rom_error_t reason);
```

### Internal APIs & Pseudo Code

```c
rom_error_t shutdown_alert_init(lifecycle_state_t state) {
  escalation = otp_read(ROM_ALERT_ESCALATION);
  // escalation is 4 packed byte-enums.
  // Set the escalation policy per class (A/B/C/D)

  for i in range(number_of_alerts) {
    alert_class = otp_read(ROM_ALERT_CLASSIFICATION[i]);
    // based on lifecycle state, program alert class.
  }

  enables = otp_read(ROM_ALERT_CLASS_EN);
  // enables is 4 packed byte-enums.
  // Enable and maybe lock per class (A/B/C/D).
}

rom_error_t shutdown_interrupt_init(void) {
  // setup an interrupt vector table which directs every interrupt
  // to enter shutdown_finalize with a reason code of
  // kErrorShutdownInterruptn where n is the interrupt number.
}

```

## Testing

Unit tests will be used to validate the initialize and shutdown flows.

Functional tests will be written to verify that the known software fault events enter the shutdown handler and cause the chip to shutdown.
