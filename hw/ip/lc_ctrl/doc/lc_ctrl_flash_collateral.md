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
<td>CREATOR_DIV_KEY</td>
<td>256</td>
<td rowspan="2">Key Manager</td>
<td>DiversificationKey: diversification secret for creator identity.</td>
</tr>
<tr>
<td>OWNER_ROOT_SECRET</td>
<td>256</td>
<td>OwnerRootSecret: diversification secret for owner identity.</td>
</tr>
<tr>
<td>OWNERSHIP_BLOB</td>
<td><=2048</td>
<td>Software</td>
<td>
Non-secret information such as public keys, software tags diversification constants.
</td>
</tbody>
</table>