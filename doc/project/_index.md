---
title: "Introduction to the OpenTitan Project"
---

OpenTitan is a collaborative hardware and software development program with contributors from many organizations.
This area gives some more information about how the project itself is organized.
More information will be added over time.

## Quality standards for open hardware IP

In order to gauge the quality of the different IP that is in our repository, we define a series of [Hardware Development Stages]({{< relref "development_stages" >}}) to track the designs.
The current status of different IP is reflected in the [Hardware Dashboard]({{< relref "hw" >}}).
The final state for developed IP is *Signed Off*, indicating that design and verification is complete, and the IP should be bug free.
To make it to that stage, a [Hardware Signoff Checklist]({{< relref "checklist.md" >}}) is used to confirm completion.
[Here](https://github.com/lowRISC/opentitan/blob/master/util/uvmdvgen/checklist.md.tpl) is a template that can be used as a checklist item.

## Governance

OpenTitan is stewarded by lowRISC CIC, a not-for-profit company that uses collaborative engineering to develop and maintain open source silicon designs and tools for the long term.
As a lowRISC CIC Chartered Project, OpenTitan governance is handled via lowRISC's default Technical Charter.

As described in full detail in the [OpenTitan Technical Charter](https://static.opentitan.org/technical-charter.pdf), our governance structure consists of:
* The Project Director, Dominic Rizzo, who is a representative of the lowRISC CIC's Board of Directors within the Steering Committee.
* The Steering Committee, responsible for project oversight and agreeing the technical roadmap.
* The [Technical Committee]({{< relref "technical_committee" >}}), responsible for technical decision making required to implement the technical roadmap.

## Initiating new development

The [OpenTitan RFC process]({{< relref "rfc_process" >}}) guides developers on how to initiate new development within the program.

## Committers

Committers are individuals with repository write access.
Everyone is able and encouraged to contribute and to help with code review, but committers are responsible for the final approval and merge of contributions.
See the [Committers]({{< relref "committers.md" >}}) definition and role description for more information.
