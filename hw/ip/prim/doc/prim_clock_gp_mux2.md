---
title: "Primitive Component: Two input clock Mux with glitch protection"
---

# Overview
`prim_clock_gp_mux2` is a two input clock mux that protects a glitch. When a current clock source is switched to the next clock source where two clocks are totally unrelated, a glitch can be generated as follows.

### Glitch
{{< wavejson >}}
{signal: [
  {name: 'clk0_i',           wave: 'L.H....L....H....L....H....'},
  {name: 'clk1_i',           wave: 'L.H.L.H.L.H.L.H.L.H.L.H.L.H'},
  {name: 'sel_i',            wave: '0............1.............'},
  {name: 'clk_o',            wave: 'L.H....L....HLH.L.H.L.H.L.H'},
 ]}
{{< /wavejson >}}

This glitch free clock mux can avoid glitch by placing two parallel synchronizers connected to each other. 1st flop and 2nd flop are triggered by positive edge and negative edge respectively to protect metastability on the sel_i signal. The following waveform shows the result.

### Glitch Free
{{< wavejson >}}
{signal: [
  {name: 'clk0_i',           wave: 'L.H....L....H....L....H....'},
  {name: 'clk1_i',           wave: 'L.H.L.H.L.H.L.H.L.H.L.H.L.H'},
  {name: 'sel_i',            wave: '0............1.............'},
  {name: 'clk_o',            wave: 'L.H....L....H....LH.L.H.L.H'},
 ]}
{{< /wavejson >}}
