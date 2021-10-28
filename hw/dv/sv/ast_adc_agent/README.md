---
title: "AST ADC UVM Agent"
---
# AST ADC UVM Agent
The AST_ADC UVM agent is intended to generate and capture transactions on the AST ADC interface.
It is is extended from DV library agent classes.

## ast_adc_agent
This class implements the agent container which may be passive or active.
In passive mode only the monitor is created.
In active mode the driver and sequencer are also included.

## ast_adc_agent_cfg
This class contains configuration knobs as well as the virtual interface used by the agent.
### Random variables
* resp_dly_min - minimum random reponse delay in clock cycles
* resp_dly_max - maximum random reponse delay in clock cycles

## ast_adc_item
This class implements the transaction for the agent
### Random variables
* channel - Channel number as unsigned integer
* data - ADC data as sized logic vector

## ast_adc_monitor
This class implements the monitor for the agent.
It samples the interface and creates ast_adc_item transactions and writes them to it's analysis port.

## ast_adc_driver
This class implements the driver for the agent.
It accepts ast_adc_item transactions and drives the interface to send data to the DUT.
Transactions are accepted immediately and internally queued so sequences need to wait
for the corresponding response to indicate completion.

## ast_adc_sequencer
This class is the agent sequencer class. It is a typedef in ast_adc_agent_pkg.

# Sequence library

## ast_adc_base_seq
Base sequence for the agent

## ast_adc_all_random_seq
Send randomized data for to all the ADC channels and wait for all the transactions to complete.
### Random variables
* data - random array one entry per channel, used to constrain the values sent to the ADC.
### Non-random variables
* responses - array of response transactions from the driver, one entry per channel
* transaction_ids - array of transaction ids one per channel

## ast_adc_random_ramp_seq - send a ramping set of data to the ADC. The ramp steps are random.
### Random variables
* ramp_min - minimum value of the ramp
* ramp_max - maximum value of the ramp;
* ramp_rising - direction 1=rising 0=falling;
* ramp_step_min - minimum ramp step
* ramp_step_max - maximum ramp step
### Non-random variables
* current_values - current values for the channels
