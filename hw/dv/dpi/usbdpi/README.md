# USBDPI

This DPI model is used with top-level testing of the USB device as well as forming
part of the ['Hello, USB!'](/sw/device/examples/hello_usbdev') example application.

It must meet the following requirements:

 - Implements a simple model of USB host behaviour with bus framing; in reality
   the bus frames have a periodicity of 1ms, but to reduce the simulation time the
   frame period is modified to 0.17ms.

 - *hello_usbdev*
   Sets up each of endpoints 1 and 2 as serial communications in both directions.
   Once more then two characters have been received on endpoint 1, the software
   transmits the sign-on message 'Hello, USB!' via endpoint 1.

 - *usbdev_test*
   USB endpoint 1 is used for a simple data transmission test from the DPI model
   to the USB device

 - *usbdev_streaming_test*
   USB endpoint 2 is used for bulk transfers of LFSR-generated data to the DPI model
   where the received data is checked. In parallel with that, a secondary stream
   of LSFR-generated data is sent from the DPI model to endpoint 4 of the device,
   and the test has passed when all outbound data has been sent from the software,
   and all inbound data has been received and checked successfully.

**Future development:**

 - variable timing, by separation of the STEP_ states from the frame number,
   and making the DPI model responsive to the device behaviour.

 - detection of error conditions, invalid responses etc, and signalling of
   such errors to the software so that the software can report the test status
   as failed.

 - generation of error conditions, bus resets, suspend states, and invalid
   transmissions, data corruptions and responses, probably in response to a test
   number/programme supplied by (i) the test environment, or (ii) the software
   running on the simulated CPU; this shall become the basis for a set of
   top-level verification tests in CI.

## Overview

The DPI model applies (simulated) power to the device (detected by the device via
the 'sense' input), and the device - under software control - indicates that it
is a Full Speed device. After a suitably delay, the DPI model will set the device
address and read its endpoint configuration.
