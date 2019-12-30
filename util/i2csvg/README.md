# i2csvg -- Generate svg pictures of I2C commands from text description

i2csvg is a Python tool to read I2C transactions from a text file and
generate `svg` pictures of them. It also supports SMBus transactions
and the smbus subdirectory contains examples of how to use the tool to
generate all the transactions from section 6.5 of the [SMBus
Specification 3.0](http://smbus.org/specs/SMBus_3_0_20141220.pdf)

Two source representations are supported. The first is a more
readable format and describes transactions in text. The second is a
hex-dump of values written to the I2C FIFO. In either format a line
starting with a `#` is taken as a comment and a line staring with a
`T` will be used to generate a title in the output.

To assist in parsing debug output the tool can be given a prefix. Only
lines with the prefix will be processed (after removal of the prefix).

### Textual Source Format

The textual description includes the flags and value written to the
I2C host interface FIFO to make the transaction. The flags and data
may be separated by whitespace. The flags are letters representing
each of the 5 control bits written to the FIFO:

|Flag | Use |
|-----|-----|
|S | Send a start signal before the data |
|P | Send a stop signal after the data |
|R | Read transaction (data value indicates how many bytes to read) |
|C | With R, allows read to continue by ACK of the last byte read |
|N | NACK OK, do not raise an error on a NACK |
|. | A dot is guarenteed to be ignored in the input, it is included in the text output format to help readability |

The flags may occur in any order (but not be repeated) and additional
characters will be ignored. In general other than dot (`.`) other
characters should be avoided since they may be used by future
versions of the tool!

The value may be an integer (binary, octal, decimal and hex
supported) or one of the special values that change how the output is
drawn:

|Value | Use |
|------|-----|
|A0 | Address with direction bit set to 0 (write) |
|A1 | Address with direction bit set to 1 (read) |
|A2 | Address in SMBus Quick command with direction bit used for data |
|M  | Multi-byte transaction, drawn as D1, D2 ... DN (like SMBus) |
|'tag'| In single quotes: Tag for the value that is drawn in output |

Lines of the input may consist of a single flag+value per line or a
comma separated list of flag+value pairs.

### Hexdump source format

In the hexdump source format tool processes the raw 13-bit data that
is written to the I2C FIFO. This is normally in hex (preceded with
0x) but the tool will accept binary, octal or decimal. Lines of input
may consist of a single hex value, multiple values separated by commas
(and optionally whitespace) or multiple values separated by
whitespace.

### Output file format

The output file generated depends on the options specified.

|Type | Options|
|-----|--------|
|`.svg`  | If multiple output files are generated or debug/text not selected |
|`.html` | If debug/text is selected and svg is generated |
|`.txt`  | If debug/test is selected and no svg is generated (`--nosvg`) |

The example commands assume `$REPO_TOP` is set to the toplevel
directory of the repo.

### Setup

The i2csvg tool does not depend on any other packages.

### Examples using i2csvg.py

The i2csvg/examples directory contains some example I2C files. For
simple examples text can be piped in to the tool using echo.

A simple I2C write consists of a Start with Address and direction bit
of zero, and a single data byte (4 in the example) with a Stop.

The baseline tool will generate an svg file (which can be viewed in a
browser) that includes the diagramatic form of the transaction and a
line with the comma separated structured text form.

```console
$ cd $REPO_TOP/util
$ echo "SA0, P4" | ./i2csvg.py > out.svg
```

The text version (which is just the input with more structured
formatting) can be viewed in the terminal by suppressing the svg
output. This output will always have the five flags in order and five
characters in the flags field (including a `.` if the flag is not
set):

```console
$ cd $REPO_TOP/util
$ echo "SA0, P4" | ./i2csvg.py --text --nosvg
S.... A0
.P... 0x4
```

The debug version is intended for tool development:

```console
$ cd $REPO_TOP/util
$ echo "SA0, P4" | ./i2csvg.py --debug --nosvg
I2cOp(read=False, rcont=False, start=True, stop=False, nackok=False, mvalue=False, adr=True, size=10, fbyte=0, tag=None)
I2cOp(read=False, rcont=False, start=False, stop=True, nackok=False, mvalue=False, adr=False, size=10, fbyte=4, tag=None)
```

If svg generation is not suppressed then the text or debug output and
the svg are generated in an HTML file.

```console
$ cd $REPO_TOP/util
$ echo "SA0, P4" | ./i2csvg.py --text > out.html
```

The smbus directory contains files with each of the commands listed in
section 6.5 of the SMBus 3.0 specification. These can be used to
generate an HTML file with all the transactions expanded.

```console
$ cd $REPO_TOP/util
$ ./i2csvg.py i2csvg/smbus/*.txt > out.html
```

Alternatively, these can all be converted to individual svg files (for
example for inclusion in documents) with the `--multiout` command.
The output filename matches the input filename with the extension
replaced with `.svg`. Note that if the `--text` or `--debug` flags
are given then the output will be HTML and the extension will be
`.html`.

```console
$ cd $REPO_TOP/util
$ ls i2csvg/smbus
01-Quick.txt        04-WriteWord.txt    07-BlockRead.txt       10-Write32.txt
02-SendByte.txt     05-ReadByte.txt     07-BlockWrite.txt      11-Read32.txt
03-ReceiveByte.txt  05-ReadWord.txt     08-BlockWrRdPCall.txt  12-Write64.txt
04-WriteByte.txt    06-ProcessCall.txt  09-HostNotify.txt      13-Read64.txt
$ ./i2csvg.py --multiout i2csvg/smbus/*.txt
$ ls i2csvg/smbus
01-Quick.svg        04-WriteWord.svg    07-BlockRead.svg       10-Write32.svg
01-Quick.txt        04-WriteWord.txt    07-BlockRead.txt       10-Write32.txt
02-SendByte.svg     05-ReadByte.svg     07-BlockWrite.svg      11-Read32.svg
02-SendByte.txt     05-ReadByte.txt     07-BlockWrite.txt      11-Read32.txt
03-ReceiveByte.svg  05-ReadWord.svg     08-BlockWrRdPCall.svg  12-Write64.svg
03-ReceiveByte.txt  05-ReadWord.txt     08-BlockWrRdPCall.txt  12-Write64.txt
04-WriteByte.svg    06-ProcessCall.svg  09-HostNotify.svg      13-Read64.svg
04-WriteByte.txt    06-ProcessCall.txt  09-HostNotify.txt      13-Read64.txt
```

### Example use in Debugging

The examples directory contains example output from a microcontroller
using the I2C interface. Mixed in to the other debug output are lines
produced when writes are done to the I2C FIFO. These lines are
prefixed by `I2CF:` Prior to a transaction a title line starting with
`T` is produced. This output can be processed to give a simple text
representation:

```console
$ cd $REPO_TOP/util
$ ./i2csvg.py --nosvg --text --fifodata --prefix=I2CF: i2csvg/examples/traceout.txt 
T read sensor
S.... 0x40
.PR.. 0x1
T fix value
S.... 0x41
..... 0x22
.P... 0x33
```

Or the output can be converted into pictures for display in a browser:

```console
$ cd $REPO_TOP/util
$ ./i2csvg.py --text --fifodata --prefix=I2CF: i2csvg/examples/traceout.txt > out.html
```

