# Using I2C host for SMBus commands

The I2C host can generate all the SMBus commands listed in the Rev 3.0 SMBus specification.

### Quick Command

The Quick command is a rare case where the Start and Stop properties are both set on the same write to the I2C FIFO, along with an address and single bit of data.

![Quick Command](01-Quick.svg)

### Simple commands

The simple SMBus commands are essentially single byte I2C transactions.
A Start is attached to an address with either the write or read flag.
There follows a single byte transfer in the appropriate direction with the Stop flag attached.

![Send Byte](02-SendByte.svg)
![Receive Byte](03-ReceiveByte.svg)


### Writes

The set of SMBus Writes (Byte, Word, 32-bit and 64-bit) follow the address with a command byte and then the appropriate number of data bytes.

![Write Byte](04-WriteByte.svg)
![Write Word](04-WriteWord.svg)
![Write 32-bit](10-Write32.svg)
![Write 64-bit](12-Write64.svg)

Host Notify is the same as Write Word but uses special addresses (and would come from a device).

![Host Notify](09-HostNotify.svg)

### Reads

The SMBus read commands start by writing a command byte then have a repeated start before the data transfer.
Note that read entry in the I2C fifo includes the data length, so only one entry is needed for all the cases, and it will always include the Stop.
The data received from the device is read from the RDATA FIFO.
The interface will automatically NACK the last byte in the transfer.

![Read Byte](05-ReadByte.svg)
![Read Word](05-ReadWord.svg)
![Read 32-bit](11-Read32.svg)
![Read 64-bit](13-Read64.svg)

### Process Call

The SMBus Process Call consists of a command and two bytes transferred in each direction.
As with the Reads there is a repeated start before the transfer from the device.
Note that in the write direction each byte is written to the fifo, and for the read direction just the single entry with the 2 byte transfer size.

![Process Call](06-ProcessCall.svg)

### Block Write

A Block Write is a potentially longer write that includes the command and an explicit length byte (N) before N bytes of data.
Since this may transfer up to 255 bytes the driver code is likely to need to manage the I2C fifo becoming full.

![Block Write](07-BlockWrite.svg)

### Block Read

A Block Read is a potentially longer read where the length of data being transferred is reported by the device during the transaction.
This requires the transaction to be split into two stages.
The first part of the transaction is similar to a Byte Read, except instead of the Stop flag the RCont flag is set on the one-byte read.
The RCont flag causes the interface to read the byte and generate an ACK to keep the transaction alive.
Since the I2C fifo will be empty at this point the interface will extend the clock low time.
The driver then needs to read the value (N) from the RDATA fifo to know the size of the rest of the transaction and write the I2C fifo with N and the Read and Stop flags set.
The transaction now completes with N bytes read from the device.
If the RDATA fifo fills then the clock will again be stretched until there is space for more data.

![Block Read](07-BlockRead.svg)

### Block Write Read Process Call

The most complex transaction combines a block write and a block read.
(Note that there may be a different number of bytes transferred in each direction despite the same N being shown in the diagrams below and SMBus specification.)
This has the same split character as Block Read.

![Block Write Read Process Call](08-BlockWrRdPCall.svg)

