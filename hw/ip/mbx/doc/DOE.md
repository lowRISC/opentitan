# OpenTitan-defined DOE objects

Please refer to the following pages for additional details on the DMA controller.
- [OpenTitan DMA Controller specification](../../dma/README.md)

## Simple DMA transfer request

Requester specifies Source address, Destination address, source space ID and Destination space ID as required by the DMA transfer operation.
Integrated OpenTitan Host firmware parses the object, checks the request and configures the OT DMA controller if it deems the transfer to be OK.

Response Object: [Response DOE object expected](#simple-dma-completion-response-object)

Interrupt: Can be configured to generate interrupt to Requester, if enabled, once DMA transfer complete.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x0</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length =  0x8 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Opcode = &lt;SimpleDMA&gt;</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Reserved\[15:10\],

Dest Addr Space ID\[9:8\]

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Reserved\[7:2\],

Source Addr Space ID\[1:0\]

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Total Data size  (in bytes)</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Source Address Low</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Source Address High (Used only if targeting 64 bit
address space; else all zero)

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Destination Address Low</td>
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Destination Address High (Used only if targeting 64
bit address space; else all zero)

</td>
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## Simple DMA completion response object

DMA transfer completion response to the requester.
Response object conveys the status of the operation.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type= 0x0</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length =  0x3 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

DMA Completion Status {Error Code, Error/Success,
Done}; \[exact format TBD\]

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
</table>

## Firmware Update request

Used by System Host software to initiate a firmware update request.
System software places the firmware update blob in the system memory.
Requester specifies Source address pointer to memory. The source address space ID is fixed toSystem).
Destination address shall be ignored by the responder.
Destination address space ID is fixed to 0x03 (FLASH).
Note that the assumption here is that OT RoT firmware is in control and aware of the Flash map.

Integrated OpenTitan Host firmware parses the object, checks the request and configures the OT DMA controller if it deems the transfer to be OK to write the update binary into an appropriate location of the OT flash, cryptographically verifies the update candidate blob , then initiates and completes the final flash update operation upon successful verification.

Response Object:  [Response DOE object expected](#simple-dma-completion-response-object)

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type= 0x1</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length = 0x8 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">

Interrupt to Requester  = &lt;Yes/No&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Opcode = &lt;FirmwareUpdate&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved\[15:08\],</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved\[7:0\],</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Total Data size (in bytes)</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Source Address Low</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Source Address High (Used only if targeting 64 bit
address space; else all zero)

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Reserved</td>
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Reserved</td>
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## Firmware Update  Ready for Reset Notification

Notify Requester, to system HOST that it is ready for system reset to complete the update operation.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x1</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length =  0x3 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Ready for Reset / Error \[exact format TBD\]

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
</table>

## Secure Storage Read Proxy

Used by Requester (System Host or SoC firmware elements) to request the OT RoT to provide proxy access to the flash storage owned by the OT RoT.
Requester initiates a read request via the DOE object.
Responder performs the corresponding flash operation and sends the contents of the flash back to the requester via a DMA operation.

Requester sets the following parameters in the request object:

Source address: Pointer to the flash storage address from where data is read
Source address ID: = 0x3 (FLASH)
Destination address: memory location where NV storage read data shall be placed
Destination address ID: System memory or CTN memory, based on requester requirements
Total Size: size of the data block (in bytes) requested

OT shall initiate the read access if it’s security policy allows the section of flash to be read by the requester

Response Object: [Response DOE object expected](#secure-storage-read-completion-response)

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x2</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length = 0x8 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">

Interrupt Requester  = &lt;Yes/No&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Opcode = &lt;NVStorageRead&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Reserved\[15:08\],

Dest Addr Space ID\[1:0\]

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved\[7:0\],</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Total Data size (in bytes)</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Source Address Low</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Source Address High (Used only if targeting 64 bit
address space; else all zero)

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Destination Address Low</td>
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Destination Address High (Used only if targeting 64
bit address space; else all zero)

</td>
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## Secure Storage Read Completion response

Proxy Read completion response to the requester.
Response object conveys the status of the operation.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x2</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length =  0x3 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Secure Storage Read Completion Status {Error Code,
Error/Success, Done}; \[exact format TBD\]

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
</table>

## Secure Storage Write Proxy

Used by Requester (System Host or SoC firmware elements) to request the OT RoT to provide proxy access to the flash storage owned by the OT RoT.
The contents to be written to the flash are placed by the requester in a SoC memory location & passes the write request along with memory pointers via the DOE object.
Responder performs the security checks, initiates a DMA transfer of the contents to be written to flash and completes the flash write operation.

Requester sets the following parameters in the request object:

Destination address: Pointer to the flash storage address from where data is read
Destination address ID: = 0x3 (FLASH)
Source address: memory location where NV storage read data shall be placed
Source address ID: System memory or CTN memory, based on requester requirements
Total Size: size of the data block to be written

OT shall initiate the write access if it’s policy allows the section of flash to be written

Response Object: [Response DOE object expected](#secure-storage-write-completion-response)

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x3</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length = 0x8 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">

Interrupt Requester  = &lt;Yes/No&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Opcode = &lt;NVStorageWrite&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Reserved\[15:08\],

Dest Addr Space ID\[1:0\]

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved\[7:0\],</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Total Data size</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Source Address Low</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Source Address High (Used only if targeting 64 bit
address space; else all zero)

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Destination Address Low</td>
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Destination Address High (Used only if targeting 64
bit address space; else all zero)

</td>
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## Secure Storage Write Completion response

Proxy Read completion response to the requester.
Response object conveys the status of the operation.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x3</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length =  0x3 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Secure Storage Write Completion Status {Error Code,
Error/Success, Done}; \[exact format TBD\]

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
</table>

## Secure Authenticated Debug Unlock Request

Used by Requester (System Host, SoC firmware agents or JTAG proxy) to initiate debug authentication & unlock request.
OT shall initiate the crypto challenge-response protocol with the authorizing agent; System Host software or an alternate agent (implementation specific) may provide network access to the remote authorizing agent.
OT shall send a signed challenge token to the remote agent.
The remote agent shall send a signed response.
OT verifies the response & sets the corresponding feature unlock command to other SoC components using the [OT debug unlock bus]()

Requester sets the following parameters in the request object:

Destination Address: Pointer to the memory location where signed challenge is placed in response to this Req
Unlock Category:
- Requester sets the desired unlock category
- Provides up to 16 different debug categories; Each category may define its own Debug feature unlock privileges
- Unlocking / enabling specific debug / DFT features in a category is SoC defined

Response Object:
- Signed Challenge Token; DOE response is generated only if DOE Rsp is set to YES
- Debug authentication via JTAG proxy channel may use the DOE response object scheme.
- System Host based authentication may benefit from DMA transfer to system memory.
- If DOE response is set to NO, then signed challenge is placed in the destination point using the OT DMA operation

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x4</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">Length = 0x8 DWORDS</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c139" colspan="4" rowspan="1">

DOE Rsp = &lt;Yes/No&gt;

</td>
<td markdown="1" class="c139" colspan="4" rowspan="1">

Send INT = &lt;Yes/No&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Opcode = &lt;AuthDebugUnlockReq&gt;

</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">

Reserved\[15:08\],

Dest Addr Space ID\[1:0\]

</td>
<td markdown="1" class="c145" colspan="4" rowspan="1">Reserved</td>
<td markdown="1" class="c147" colspan="4" rowspan="1">Unlock Category</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Destination Buffer Size</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Reserved</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Reserved</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">Destination Address Low</td>
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c49" colspan="32" rowspan="1">

Destination Address High (Used only if targeting 64
bit address space; else all zero)

</td>
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## DOE Response - Debug Unlock Challenge

OT sends this DOE response message in response to the [Secure Authenticated Debug Unlock Request](#secure-authenticated-debug-unlock-request) (if DOE Rsp is set to YES) to initiate the crypto challenge-response protocol with the authorizing agent.
Requester (JTAG proxy or system software) shall read the token via DOE outbox and relay to the remote agent.
The remote agent shall send a signed unlock token in response.
OT verifies the response & sets the corresponding feature unlock command to other SoC components using the [OT debug unlock bus]().

Responder (OT RoT) sets the following parameters in the request object:

Nonce: OT generates a NONCE; Size TBD; Embeds within the object.
Unlock Category:
- Sets the desired unlock category based on the original request.
- Provides up to 16 different debug categories; Each category may define its own Debug feature unlock privileges
- Unlocking / enabling specific debug / DFT features in a category is SoC defined
Signature: Size TBD; Algorithm TBD.

OT generates a digital signature using a private key over the header, NONCE & the Requested unlock category.
Embeds the digital signature within the Response object.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x5</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">

Length =  &lt;TBD&gt;  DWORDS

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c93" colspan="32" rowspan="6">

&lt;TBD&gt; &lt;Signed Debug Unlock Challenge Token
format&gt;

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## DOE Request Object - Debug Unlock Response

System Software receives a response to the Debug Unlock Challenge from the remote server.
System software sends this Unlock response to the OT RoT through this “DOE Request Object - Debug Unlock Response”.
The signed response contains the Unlock Category that the RoT is allowed to set (same as the original request of a lower category, as determined by the remote authentication agent).
Upon successful verification of the response token, the RoT sets the corresponding unlock category via the [OT debug unlock bus]().

The Object Contains the following format:

- DOE Header (2 DWORDS)
- Debug Unlock Response Token: Size and Format TBD.

<table markdown="1" class="c149">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x5</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">

Length =  &lt;TBD&gt;  DWORDS

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c93" colspan="32" rowspan="6">

&lt;TBD&gt; &lt;Signed Debug Unlock Response Token
format&gt;

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>

## DOE TPM-like Service objects

Placeholder for defining DOE objects to provide TPM like services.

One or more just object definitions may be needed for TPM interface.

<table markdown="1" class="c80">
<tr markdown="1" class="c5">
<td markdown="1" class="c11" colspan="1" rowspan="1">31</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">30</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">29</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">28</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">27</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">26</td>
<td markdown="1" class="c7" colspan="1" rowspan="1">25</td>
<td markdown="1" class="c122" colspan="1" rowspan="1">24</td>
<td markdown="1" class="c78" colspan="1" rowspan="1">23</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">22</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">21</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">20</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">19</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">18</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">17</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">16</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">15</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">14</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">13</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">12</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">11</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">10</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">09</td>
<td markdown="1" class="c77" colspan="1" rowspan="1">08</td>
<td markdown="1" class="c42" colspan="1" rowspan="1">07</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">06</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">05</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">04</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">03</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">02</td>
<td markdown="1" class="c26" colspan="1" rowspan="1">01</td>
<td markdown="1" class="c35" colspan="1" rowspan="1">00</td>
<td markdown="1" class="c60" colspan="1" rowspan="1">Byte Offset</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c24" colspan="8" rowspan="1">Reserved</td>
<td markdown="1" class="c24" colspan="8" rowspan="1">Object Data Type=0x5</td>
<td markdown="1" class="c84" colspan="16" rowspan="1">Vendor ID=&lt;OT TBD&gt;</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x0</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c85" colspan="14" rowspan="1">Reserved</td>
<td markdown="1" class="c55" colspan="18" rowspan="1">

Length =  &lt;TBD&gt;  DWORDS

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x4</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c93" colspan="32" rowspan="6">

&lt;TBD&gt; &lt;Signed Debug Unlock Challenge Token
format&gt;

</td>
<td markdown="1" class="c22" colspan="1" rowspan="1">0x8</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0xC</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x10</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c22" colspan="1" rowspan="1">0x14</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c38" colspan="1" rowspan="1">0x18</td>
</tr>
<tr markdown="1" class="c21">
<td markdown="1" class="c109" colspan="1" rowspan="1">0x1C</td>
</tr>
</table>
