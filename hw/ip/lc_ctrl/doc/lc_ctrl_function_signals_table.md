###
<!-- this is a workaround to get around Hugo Issue #7296 (https://github.com/gohugoio/hugo/issues/7296) -->

<table style="text-align:center;font-size:small">
  <tr>
    <td style="text-align:left"><strong>State \ Function</strong></td>
    <td><strong>DFT_EN</strong></td>
    <td><strong>NVM_DEBUG_EN</strong></td>
    <td><strong>HW_DEBUG_EN</strong></td>
    <td><strong>CPU_EN</strong></td>
    <td><strong>KEYMGR_EN</strong></td>
    <td><strong>CLK_BYP_REQ</strong></td>
    <td><strong>FLASH_RMA_REQ</strong></td>
    <td><strong>CHECK_BYP_EN</strong></td>
    <td><strong>ESCALATE_EN</strong></td>
  </tr>
  <tr>
    <td style="text-align:left">RAW</td>
    <td rowspan = "9" colspan="4" style="text-align:center;vertical-align:middle"> See <a href="../../../../doc/security/specs/device_life_cycle/#manufacturing-states">life cycle definition table</a> </td>
    <td colspan="1" style="background:#dadce0"></td><td>Y*</td><td style="background:#dadce0"></td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
   <td style="text-align:left">TEST_LOCKED</td>
   <td colspan="1" style="background:#dadce0"></td><td>Y*</td><td style="background:#dadce0"></td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">TEST_UNLOCKED</td>
    <td colspan="2" style="background:#dadce0"></td><td>Y*</td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">DEV</td>
    <td>Y</td><td style="background:#dadce0"></td><td>Y*</td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">PROD</td>
    <td>Y</td><td style="background:#dadce0"></td><td>Y*</td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">PROD_END</td>
    <td>Y</td><td colspan="2" style="background:#dadce0"></td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">RMA</td>
    <td>Y</td><td colspan="2" style="background:#dadce0"></td><td>Y*</td><td>Y*</td>
  </tr>
  <tr>
    <td style="text-align:left">SCRAP</td>
    <td colspan="3" style="background:#dadce0"></td><td>Y*</td><td>Y</td>
  </tr>
  <tr>
    <td style="text-align:left;color:red">INVALID</td>
    <td colspan="3" style="background:#dadce0"></td><td>Y*</td><td>Y</td>
  </tr>
  <tr>
    <td style="text-align:left;color:red">POST_TRANSITION</td>
    <td colspan="7" style="background:#dadce0"></td><td>Y*</td><td>Y</td>
  </tr>
  <tr>
    <td style="text-align:left;color:red">ESCALATION</td>
    <td colspan="7" style="background:#dadce0"></td><td>Y*</td><td>Y</td>
  </tr>
</table>
