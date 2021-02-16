// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// DCD Module
package dcd_pkg;

typedef struct {
 logic [1:0] chnsel;
 logic       powerdown;
} adc_req_t;

typedef struct {
 logic [9:0] data;
 logic       valid;
} adc_rsp_t;

localparam adc_req_t ADC_REQ_DEFAULT = '{default:'0};
localparam adc_rsp_t ADC_RSP_DEFAULT = '{default:'0};

endpackage
