# Programmer's Guide

This section discusses how software can interface with CSRNG.

## Module enable and disable

CSRNG may only be enabled if `ENTROPY_SRC` is enabled.
CSRNG may only be disabled if all EDNs are disabled.
Once disabled, CSRNG may only be re-enabled after `ENTROPY_SRC` has been disabled and re-enabled.

## Endianness and Known-Answer Tests

All CSRNG registers are little-endian.

When providing additional data for an <tt>instantiate</tt>, <tt>reseed</tt> or <tt>update</tt> command the data words have to be written to [`CMD_REQ`](registers.md#cmd_req) in the correct order.
Consider a byte string B<sub>1</sub>, B<sub>2</sub>, ..., B<sub>n</sub> as defined in Appendix A of [NIST's SP 800-90A](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf), i.e., where B<sub>1</sub> is the most significant byte and B<sub>n</sub> the least significant byte.
Providing this sequence as additional data to CSRNG requires software to write the following 32-bit words to [`CMD_REQ`](registers.md#cmd_req) in the following order:

<table>
<caption>Byte order when writing to [`CMD_REQ`](data/csrng.hjson#cmd_req)</caption>
<thead>
  <tr>
    <th>Word Index</th>
    <th>Byte Indices of Additional Data</th>
  </tr>
</thead>
<tbody>
  <tr>
    <td>1</td>
    <td>0xB<sub>n-3</sub>B<sub>n-2</sub>B<sub>n-1</sub>B<sub>n</sub></td>
  </tr>
  <tr>
    <td>...</td>
    <td>...</td>
  </tr>
  <tr>
    <td>n/4-1</td>
    <td>0xB<sub>5</sub>B<sub>6</sub>B<sub>8</sub>B<sub>8</sub></td>
  </tr>
  <tr>
    <td>n/4</td>
    <td>0xB<sub>1</sub>B<sub>2</sub>B<sub>3</sub>B<sub>4</sub></td>
  </tr>
</table>

When reading the internal state from [`INT_STATE_VAL`](registers.md#int_state_val), CSRNG returns the bytes of V and Key in the following order:
<table>
<caption>Byte order when reading from [`INT_STATE_VAL`](data/csrng.hjson#int_state_val)</caption>
<thead>
  <tr>
    <th>Word Index</th>
    <th>Byte Indices of V and Key</th>
  </tr>
</thead>
<tbody>
  <tr>
    <td>1</td>
    <td>0xV<sub>13</sub>V<sub>14</sub>V<sub>15</sub>V<sub>16</sub></td>
  </tr>
  <tr>
    <td>...</td>
    <td>...</td>
  </tr>
  <tr>
    <td>4</td>
    <td>0xV<sub>01</sub>V<sub>02</sub>V<sub>03</sub>V<sub>04</sub></td>
  </tr>
  <tr>
    <td>5</td>
    <td>0xKey<sub>29</sub>Key<sub>30</sub>Key<sub>31</sub>Key<sub>32</sub></td>
  </tr>
  <tr>
    <td>...</td>
    <td>...</td>
  </tr>
  <tr>
    <td>11</td>
    <td>0xKey<sub>05</sub>Key<sub>06</sub>Key<sub>07</sub>Key<sub>08</sub></td>
  </tr>
  <tr>
    <td>12</td>
    <td>0xKey<sub>01</sub>Key<sub>02</sub>Key<sub>03</sub>Key<sub>04</sub></td>
  </tr>
</table>

Finally, when reading a byte string of say 64 bytes (16 words) B<sub>1</sub>, B<sub>2</sub>, ..., B<sub>64</sub> from [`GENBITS`](registers.md#genbits) as defined in Appendix A of [NIST's SP 800-90A](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf), the bytes are returned in the following order.
Note that always 4 words return 1 128-bit GENBITS block.
Within each block, the least significant bytes are returned first and the most significant bytes are returned last.
In particular, the most significant byte B<sub>1</sub> of the string is read in Word 4 and the least significant byte B<sub>64</sub> of the string is read in Word 13.

<table>
<caption>Byte order when reading from [`GENBITS`](data/csrng.hjson#genbits)</caption>
<thead>
  <tr>
    <th>Word Index</th>
    <th>Byte Indices of Generated Bits</th>
  </tr>
</thead>
<tbody>
  <tr>
    <td>1</td>
    <td>0xB<sub>13</sub>B<sub>14</sub>B<sub>15</sub>B<sub>16</sub></td>
  </tr>
  <tr>
    <td>2</td>
    <td>0xB<sub>09</sub>B<sub>10</sub>B<sub>11</sub>B<sub>12</sub></td>
  </tr>
  <tr>
    <td>3</td>
    <td>0xB<sub>05</sub>B<sub>06</sub>B<sub>07</sub>B<sub>08</sub></td>
  </tr>
  <tr>
    <td>4</td>
    <td>0xB<sub>01</sub>B<sub>02</sub>B<sub>03</sub>B<sub>04</sub></td>
  </tr>

  <tr>
    <td>5</td>
    <td>0xB<sub>29</sub>B<sub>30</sub>B<sub>31</sub>B<sub>32</sub></td>
  </tr>
  <tr>
    <td>6</td>
    <td>0xB<sub>25</sub>B<sub>26</sub>B<sub>27</sub>B<sub>28</sub></td>
  </tr>
  <tr>
    <td>7</td>
    <td>0xB<sub>21</sub>B<sub>22</sub>B<sub>23</sub>B<sub>24</sub></td>
  </tr>
  <tr>
    <td>8</td>
    <td>0xB<sub>17</sub>B<sub>18</sub>B<sub>19</sub>B<sub>20</sub></td>
  </tr>

  <tr>
    <td>...</td>
    <td>...</td>
  </tr>

  <tr>
    <td>13</td>
    <td>0xB<sub>61</sub>B<sub>62</sub>B<sub>63</sub>B<sub>64</sub></td>
  </tr>
  <tr>
    <td>14</td>
    <td>0xB<sub>57</sub>B<sub>58</sub>B<sub>59</sub>B<sub>60</sub></td>
  </tr>
  <tr>
    <td>15</td>
    <td>0xB<sub>53</sub>B<sub>54</sub>B<sub>55</sub>B<sub>56</sub></td>
  </tr>
  <tr>
    <td>16</td>
    <td>0xB<sub>49</sub>B<sub>50</sub>B<sub>51</sub>B<sub>52</sub></td>
  </tr>
</table>

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_csrng.h)
