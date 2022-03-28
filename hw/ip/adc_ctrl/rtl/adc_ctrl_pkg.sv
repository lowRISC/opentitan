// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// adc_ctrl package module

package adc_ctrl_pkg;

  // FSM flow
  // 1. PWRDN->PWRUP->ONEST_0->ONEST_021->ONEST_1->ONEST_DONE->PWRDN
  // 2. PWRDN->PWRUP->LP_0->LP_021->LP_1->LP_EVAL->LP_SLP->LP_PWRUP->LP0->
  //    LP_021->LP_1->LP_EVAL->NP_0->NP_021->NP_1->NP_EVAL->NP_0...repeat
  // 3. PWRDN->PWRUP->NP_0->NP_021->NP_1->NP_EVAL->NP_0/NP_DONE....repeat
  typedef enum logic [4:0] {
    PWRDN,      // in the power down state
    PWRUP,      // being powered up
    ONEST_0,    // in oneshot mode; sample channel0 value
    ONEST_021,  // in oneshot mode; transition from chn0 to chn1
    ONEST_1,    // in oneshot mode; sample channel1 value
    ONEST_DONE, // one shot done
    LP_0,       // in low-power mode, sample channel0 value
    LP_021,     // in low-power mode, transition from chn0 to chn1
    LP_1,       // in low-power mode, sample channel1 value
    LP_EVAL,    // in low-power mode, evaluate if there is a match
    LP_SLP,     // in low-power mode, go to sleep
    LP_PWRUP,   // in low-power mode, being powered up
    NP_0,       // in normal-power mode, sample channel0 value
    NP_021,     // in normal-power mode, transition from chn0 to chn1
    NP_1,       // in normal-power mode, sample channel1 value
    NP_EVAL,    // in normal-power mode, detection is done
    NP_DONE     // normal-power detection done
  } fsm_state_e;


endpackage : adc_ctrl_pkg
