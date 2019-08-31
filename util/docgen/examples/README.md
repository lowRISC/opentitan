# Examples using docgen

This directory has some examples of using docgen. The example commands
assume $REPO_TOP is set to the toplevel directory of the repo.

### Setup

If packages have not previously been installed you will need to set a
few things up. First use `pip3` to install some required packages:
```
$ pip3 install --user hjson
$ pip3 install --user mistletoe
$ pip3 install --user pygments
```

The examples all use the -c flag to ensure CSS styles are included
inline in the html file generated. If building a site this flag will
likely not be used. If this flag is not given then `md_html.css` from
docgen and `reg_html.css` from reggen should be put in the same
directory as the html file.

### Build example1

Example 1 is the Simple Uart. There are a couple of changes from the
actuall implemmentation: the registers are declared as 64-bit and the
STATECLR register bits have been moved up by 16 bits.

```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -c uart.md > /tmp/uartout.html
```

If you want it to tell more about progress add the verbose flag. Note
that this causes a second validation pass that checks the output of
the first pass, there should be fewer things to do on the second pass.

```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -c -v uart.md > /tmp/uartout.html
```

You can open the output using file:///tmp/uartout.html

### Build example2

Example 2 is a 16550 style Uart. This shows 8-bit registers and
registers at the same address.

Note this example has a deliberate error in the second waveform description.

```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -c uart16550.md > /tmp/uart16550out.html
```

If you want it to tell more about progress add the verbose flag. Note
that this causes a second validation pass that checks the output of
the first pass, there should be fewer things to do on the second pass.

```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -c -v uart16550.md > /tmp/uart16550out.html
```

The waveforms can also be generated using the browser-based wavedom
javascript.

```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -cj uart16550.md > /tmp/uart16550out.html
```


You can open the output using file:///tmp/uart16550out.html

### Build example 3

Example 3 is an example of using the multireg key to generate registers.


```
$ cd $REPO_TOP/util/docgen/examples
$ ../../docgen.py -c gp.md > /tmp/gpout.html
```
