###
<!-- this is a workaround to get around Hugo Issue #7296 (https://github.com/gohugoio/hugo/issues/7296) -->
<table>
<thead>
<tr>
<th>Collateral</th>
<th>SW Program</th>
<th>SW Read</th>
<th>HW Read</th>
<th>Comments</th>
</tr>
</thead>
<tbody>
<tr>
<td>LC_STATE</td>
<td>no</td>
<td>no</td>
<td>yes</td>
<td rowspan="2">Advanced only by HW. Note that these two items are exposed in decoded form in the life cycle controller CSRs.</td>
</tr>
<tr>
<td>LC_TRANSITION_CNT</td>
<td>no</td>
<td>no</td>
<td>yes</td>
</tr>
<tr>
<td>TEST_UNLOCK_TOKEN</td>
<td rowspan="2" colspan="2" style="text-align:center;vertical-align:middle">SECRET0_DIGEST == 0</td>
<td rowspan="2" style="text-align:center;vertical-align:middle">yes</td>
<td></td>
</tr>
<tr>
<td>TEST_EXIT_TOKEN</td>
<td></td>
</tr>
<tr>
<td>RMA_UNLOCK_TOKEN</td>
<td rowspan="3" colspan="2" style="text-align:center;vertical-align:middle">SECRET0_DIGEST == 0 && CREATOR_SEED_SW_RW_EN == ON</td>
<td rowspan="3" style="text-align:center;vertical-align:middle">SEED_HW_RD_EN == ON</td>
<td></td>
</tr>
<tr>
<td>CREATOR_ROOT_KEY_SHARE0</td>
<td></td>
</tr>
<tr>
<td>CREATOR_ROOT_KEY_SHARE1</td>
<td></td>
</tr>
<tr>
<td>SECRET0_DIGEST</td>
<td>no</td>
<td>yes</td>
<td>yes</td>
<td rowspan="2">Digest calculation and programming is SW triggered, but the actual calculation is performed by HW.</td>
</tr>
<tr>
<td>SECRET2_DIGEST</td>
<td>no</td>
<td>yes</td>
<td>yes</td>
</tr>
</tbody>
</table>
