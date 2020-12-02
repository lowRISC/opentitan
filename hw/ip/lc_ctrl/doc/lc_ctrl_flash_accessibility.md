###
<!-- this is a workaround to get around Hugo Issue #7296 (https://github.com/gohugoio/hugo/issues/7296) -->
<table>
<thead>
<tr>
<th>Collateral</th>
<th>SW Program</th>
<th>SW Erase</th>
<th>SW Read</th>
<th>Comments</th>
</tr>
</thead>
<tbody>
<tr>
<td>CREATOR_DATA</td>
<td colspan="2" style="text-align:center;vertical-align:middle">PROVISION_WR_EN == ON</td>
<td style="text-align:center;vertical-align:middle">PROVISION_RD_EN == ON</td>
<td>Similar control to creator collateral in OTP, with the difference that this item remains readable after personalization.</td>
</tr>
<tr>
<td>OWNER_DATA</td>
<td rowspan="2" colspan="3" style="text-align:center;vertical-align:middle">yes</td>
<td rowspan="2">Follows normal software isolation rules.</td>
</tr>
<tr>
<td>General</td>
</tr>
</tbody>
</table>