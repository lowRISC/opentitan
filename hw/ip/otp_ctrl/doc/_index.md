---
title: "OTP Controller Technical Specification"
---


# Overview

This document specifies the functionality of the one time programmable (OTP) memory controller.
The OTP controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).


## Features

## Description

# Theory of Operations

## Block Diagram

## Hardware Interfaces

### Parameters

The following table lists the main parameters used throughout the OTP controller design.

Localparam     | Default (Max)         | Top Earlgrey | Description
---------------|-----------------------|--------------|---------------

### Signals

{{< hwcfg "hw/ip/otp_ctrl/data/otp_ctrl.hjson" >}}

Signal                  | Direction        | Type                      | Description
------------------------|------------------|---------------------------|---------------


## Design Details

# Programmers Guide


## Power-up and Reset Considerations

## Initialization

## Interrupt Handling


## Register Table

{{< registers "hw/ip/otp_ctrl/data/otp_ctrl.hjson" >}}

# Additional Notes

