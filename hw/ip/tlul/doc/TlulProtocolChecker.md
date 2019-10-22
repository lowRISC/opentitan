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

## **Request Channel (Channel A)**

Below table lists all channel A signals and their checks.

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
   <td><strong>legalAOpcode</strong>: Only the following 3 opcodes are legal:
Get, PutFullData, PutPartialData. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>a_param
   </td>
   <td><strong>legalAParam</strong>: This field is reserved, it must be 0. See
spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>a_size
   </td>
   <td><strong>sizeMatchesMask</strong>: a_size can be calculated from a_mask
as follows: 2<sup>a_size</sup> must equal $countones(a_mask). See spec section
4.6.
<p>
<strong>aKnown</strong>: Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_source
   </td>
   <td><strong>onlyOnePendingReqPerSourceID</strong>: There should be no more
than one pending request per each source ID. See spec section 5.4.
<p>
<strong>aKnown</strong>: Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_address
   </td>
   <td><strong>addressAlignedToSize</strong>: a_address must be aligned to
a_size: a_address & ((1 << a_size) - 1) == 0. See spec section 4.6.
<p>
<strong>aKnown: </strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_mask
   </td>
   <td><strong>maskMustBeContiguous</strong>: a_mask must be contiguous for Get
and PutFullData (but not for PutPartialData). See spec sections 4.6 and 6.2.
<p>
<strong>sizeMatchesMask</strong>: See a_size above.
<p>
<strong>aKnown: </strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_data
   </td>
   <td><strong>aDataKnown</strong>: a_data should not be X for opcodes
PutFullData and PutPartialData (it can be X for Get). Bytes of a_data, whose
corresponding a_mask bits are 0, can be X. See spec section 4.6.
   </td>
  </tr>
  <tr>
   <td>a_user
   </td>
   <td><strong>aKnown: </strong>Make sure it's not X when a_valid is high.
   </td>
  </tr>
  <tr>
   <td>a_valid
   </td>
   <td><strong>aKnown</strong>: Make sure it's not X (except during reset).
   </td>
  </tr>
  <tr>
   <td>a_ready
   </td>
   <td><strong>aReadyKnown</strong>: Make sure it's not X (except during
reset).
   </td>
  </tr>
</table>

## **Response Channel (Channel D)**

Below table lists all channel D signals and their checks.

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
   <td><strong>checkResponseOpcode</strong>: If the original request was Get,
then the corresponding response must be AccessAckData. Otherwise, the response
must be AccessAck. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_param
   </td>
   <td><strong>legalDParam</strong>: This field is reserved, it must be 0. See
spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_size
   </td>
   <td><strong>responseSizeMustEqualReqSize</strong>: The response must have
the same size as the original request. See spec section 6.2.
   </td>
  </tr>
  <tr>
   <td>d_source
   </td>
   <td><strong>responseMustHaveReq</strong>: For each response, there must have
been a corresponding request with the same source ID value. See spec section
5.4.
<p>
<strong>noOutstandingReqsAtEndOfSim</strong>: Make sure that there are no
outstanding requests at the end of the simulation.
<p>
<strong>dKnown</strong>: Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_sink
   </td>
   <td><strong>dKnown</strong>: Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_data
   </td>
   <td><strong>dDataKnown</strong>: d_data should not be X for AccessAckData.
Bytes of d_data, whose corresponding mask bits of the original request are 0,
can be X. See spec section 4.6.
   </td>
  </tr>
  <tr>
   <td>d_error
   </td>
   <td><strong>dKnown: </strong>Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_user
   </td>
   <td><strong>dKnown: </strong>Make sure it's not X when d_valid is high.
   </td>
  </tr>
  <tr>
   <td>d_valid
   </td>
   <td><strong>dKnown</strong>: Make sure it's not X (except during reset).
   </td>
  </tr>
  <tr>
   <td>d_ready
   </td>
   <td><strong>dReadyKnown: </strong>Make sure it's not X (except during
reset).
   </td>
  </tr>
</table>
