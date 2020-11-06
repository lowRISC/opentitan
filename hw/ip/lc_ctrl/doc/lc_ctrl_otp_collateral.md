###
<!-- this is a workaround to get around Hugo Issue #7296 (https://github.com/gohugoio/hugo/issues/7296) -->
<table>
<thead>
<tr>
<th>Collateral</th>
<th>Size [Bit]</th>
<th>Consumer</th>
<th>Usage</th>
</tr>
</thead>
<tbody>
<tr>
<td>LC_STATE</td>
<td>192</td>
<td rowspan="5">Life Cycle Controller</td>
<td>Life cycle manufacturing state (refer to details <a href="#life-cycle-manufacturing-state-encodings">here</a>).</td>
</tr>
<tr>
<td>LC_TRANSITION_CNT</td>
<td>256</td>
<td>Number of total life cycle transition attempts.</td>
</tr>
<tr>
<td>TEST_UNLOCK_TOKEN</td>
<td>128</td>
<td>Token to unlock test function.</td>
</tr>
<tr>
<td>TEST_EXIT_TOKEN</td>
<td>128</td>
<td>Token to exit TEST state.</td>
</tr>
<tr>
<td>RMA_UNLOCK_TOKEN</td>
<td>128</td>
<td>Token to unlock RMA.</td>
</tr>
<tr>
<td>CREATOR_ROOT_KEY_SHARE0</td>
<td>256</td>
<td rowspan="2">Key Manager</td>
<td rowspan="2">The root creator secret.</td>
</tr>
<tr>
<td>CREATOR_ROOT_KEY_SHARE1</td>
<td>256</td>
</tr>
<tr>
<td>SECRET0_DIGEST</td>
<td>64</td>
<td rowspan="2">Life Cycle &amp; OTP Controllers</td>
<td>Digest over the SECRET0 partition containing the TEST_*_TOKEN.</td>
</tr>
<tr>
<td>SECRET2_DIGEST</td>
<td>64</td>
<td>Digest over the SECRET2 partition containing the CREATOR_ROOT_KEY* and RMA_UNLOCK_TOKEN.</td>
</tr>
</tbody>
</table>