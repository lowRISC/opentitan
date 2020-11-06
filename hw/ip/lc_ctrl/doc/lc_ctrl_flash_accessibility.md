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
<td colspan="3" style="text-align:center;vertical-align:middle">PROVISION_EN == ON</td>
<td>Identical control to creator collateral in OTP.</td>
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