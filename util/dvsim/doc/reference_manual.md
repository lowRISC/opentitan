---
title: "DVSim reference manual"
---

This document provides a deep dive into the inner workings of DVSim.
Please see [DVSim design doc]({{< relref "design_doc" >}}) for more details.

DVSim progresses through these 7 stages:
- HJson configuration file parsing / loading
- Extraction of `Modes` objects (build modes, run modes, tests and regressions)
- Generation of `Deploy` class objects
- Running the scheduler
- Launching jobs to the chosen launcher system
- Assessing pass / failure
- Aggregating the reports

# DVSim stages

## Block diagram

## HJson configuration loading stage

## Creating of toolflow configuration

### Inheritance diagram

## Variable substitution

## Creation of Modes

## Creation of Deploy objects

## Scheduler

## Makefile

### Job dependency resolution

## Launching the jobs

### Supported launcher variants

### Developing a privately maintained launcher variant

### Reporting

### Assessing pass / failure

### Bucketization of common failure patterns

### Publishing reports

## Progress bar
