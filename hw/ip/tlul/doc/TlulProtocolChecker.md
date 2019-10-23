---
title: "TL-UL Protocol Checker"
---

# TileLink-UL Protocol Checker


## **Overview**

This document details the protocol checker
[tlul_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/tlul/rtl/tlul_assert.sv)
for TL-UL (TileLink Uncached Lightweight), based on
[TileLink specification version 1.7.1](https://sifive.cdn.prismic.io/sifive%2F57f93ecf-2c42-46f7-9818-bcdd7d39400a_tilelink-spec-1.7.1.pdf).

The next sections list the checks for each signal of TL-UL channels A and D.
More details:

*   The source fields (`a_source` and `d_source`) identify inflight
transactions rather than physical agents. A single agent can use multiple
source IDs to track multiple outstanding transactions. See spec section 5.4
"Source and Sink Identifiers" for more details.
*   The source fields are `TL_AIW` bits wide (defined in
[tlul_pkg.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/tlul/rtl/tlul_pkg.sv)).
Therefore, there can be up to 2<sup>TL_AIW</sup> outstanding
requests at the same time. To keep track of these outstanding requests, the
protocol checker stores pending requests in the array `pend_req` of depth
`TL_AIW`, and removes them once their corresponding response has been received.
*   A request can be responded within the same cycle as the request message is
accepted. Therefore, in each clock cycle, the protocol checker first processes
requests and thereafter responses.
*   The package
[tlul_pkg.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/tlul/rtl/tlul_pkg.sv)
defines the structs for channels A and D.
*   In below tables, "known" means that a signal should have a value other
than X.
* The protocol checker has a parameter `EndpointType` which can either be
`"Host"` or `"Device"`. The difference between the `"Host"` and `"Device"`
variant is that some of the properties are formulated as SV assumptions in the
former, whereas the same properties are formulated as SV assertions in the
latter (and vice versa).  The behavior of these two checkers in DV simulations
is identical, but in formal verification, this distinction is needed (otherwise
some of the assertions would have to be disabled).

## **Request Channel (Channel A)**

Below table lists all channel A signals and their checks.
In `"Device"` mode some of these properties are assumptions (`_M` suffix) and in `"Host"` mode they are assertions (`_A` suffix).

<table>
  <tr>
   <td><strong>Signal</strong>
   </td>
   <td><strong>Checks </strong>(assertion name: description)
   </td>
  </tr>
  <tr>
   <td>a_opcode
   </td>
   <td><strong>legalAOpcode_[M/A]</strong>: Only the following 3 opcodes are legal:
Get, PutFullData, PutPartialData. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>a_param
   </td>
   <td><strong>legalAParam_[M/A]</strong>: This field is reserved, it must be 0. See
spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>a_size
   </td>
   <td><strong>sizeMatchesMask_[M/A]</strong>: a_size can be calculated from a_mask
as follows: 2<sup>a_size</sup> must equal $countones(a_mask). See spec section
4.6.
<p>
<strong>aKnown_A</strong>: Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_source
   </td>
   <td><strong>pendingReqPerSrc_[M/A]</strong>: There should be no more
than one pending request per each source ID. See spec section 5.4.
<p>
<strong>aKnown_A</strong>: Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_address
   </td>
   <td><strong>addrSizeAligned_[M/A]</strong>: a_address must be aligned to
a_size: a_address & ((1 << a_size) - 1) == 0. See spec section 4.6.
<p>
<strong>aKnown_A</strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_mask
   </td>
   <td><strong>contigMask_[M/A]</strong>: a_mask must be contiguous for Get
and PutFullData (but not for PutPartialData). See spec sections 4.6 and 6.2.
<p>
<strong>sizeMatchesMask_[M/A]</strong>: See a_size above.
<p>
<strong>aKnown_A</strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_data
   </td>
   <td><strong>aDataKnown_[M/A]</strong>: a_data should not be X for opcodes
PutFullData and PutPartialData (it can be X for Get). Bytes of a_data, whose
corresponding a_mask bits are 0, can be X. See spec section 4.6.
   </td>
  </tr>
  <tr>
   <td>a_user
   </td>
   <td><strong>aKnown_A</strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_valid
   </td>
   <td><strong>aKnown_A</strong>: Make sure it's not X (except during reset).
   </td>
  </tr>
  <tr>
   <td>a_ready
   </td>
   <td><strong>aReadyKnown_A</strong>: Make sure it's not X (except during
reset).
   </td>
  </tr>
</table>

## **Response Channel (Channel D)**

Below table lists all channel D signals and their checks.
In `"Device"` mode some of these properties are assertions (`_A` suffix) and in `"Host"` mode they are assumptions (`_M` suffix).

<table>
  <tr>
   <td><strong>Signal</strong>
   </td>
   <td><strong>Checks  </strong>(assertion name: description)
   </td>
  </tr>
  <tr>
   <td>d_opcode
   </td>
   <td><strong>respOpcode_[A/M]</strong>: If the original request was Get,
then the corresponding response must be AccessAckData. Otherwise, the response
must be AccessAck. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_param
   </td>
   <td><strong>legalDParam_[A/M]</strong>: This field is reserved, it must be 0. See
spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_size
   </td>
   <td><strong>respSzEqReqSz_[A/M]</strong>: The response must have
the same size as the original request. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_source
   </td>
   <td><strong>respMustHaveReq_[A/M]</strong>: For each response, there must have
been a corresponding request with the same source ID value. See spec section
5.4.
<p>
<strong>noOutstandingReqsAtEndOfSim_A</strong>: Make sure that there are no
outstanding requests at the end of the simulation.
<p>
<strong>dKnown_A</strong>: Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_sink
   </td>
   <td><strong>dKnown_A</strong>: Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_data
   </td>
   <td><strong>dDataKnown_[A/M]</strong>: d_data should not be X for AccessAckData.
Bytes of d_data, whose corresponding mask bits of the original request are 0,
can be X. See spec section 4.6.
   </td>
  </tr>
  <tr>
   <td>d_error
   </td>
   <td><strong>dKnown_A</strong>Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_user
   </td>
   <td><strong>dKnown_A</strong>Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_valid
   </td>
   <td><strong>dKnown_A</strong>: Make sure it's not X (except during reset).
   </td>
  </tr>
  <tr>
   <td>d_ready
   </td>
   <td><strong>dReadyKnown_A</strong>Make sure it's not X (except during
reset).
   </td>
  </tr>
</table>
