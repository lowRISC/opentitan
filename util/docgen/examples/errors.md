{{% lowrisc-doc-hdr Example with lots of errors }}
{{% regfile errors.hjson }}

Blah

Error in lowRISC tag
{{% bob 3 }}

## Compatibility


## Theory of operation

Check for cross reference to !!DATA_OUT and !!INT_CTRL and !!INT_CTRL2 blah

For testing, this version should report an error:
```wavejson
{signal: [
  {name:'Baud Clock',  wave: 'p...........' },
  {name:'Data 8 bit',        wave: '10========1=',
   data: [ "lsb", "", "", "", "", "", "", "msb", "next" ] )
  {name:'Data 7 bit',        wave: '10=======1=.',
   data: [ "lsb", "", "", "", "", "", "msb", "next" ] },
  {name:'Data 6 bit',        wave: '10======1=..',
   data: [ "lsb", "", "", "", "", "msb", "next" ] },
  {name:'Data 5 bit',        wave: '10=====1=...',
   data: [ "lsb", "", "", "", "msb", "next" ] },
  {name:'8 with Parity', wave: '10=========1',
   data: [ "lsb", "", "", "", "", "", "", "msb", "par" ] },
 ],
 head:{
   text:'Serial Line format (one stop bit)',
   tock:-1,
 }
}
```

## Programmer Guide


### Initialization


### Interrupts



### Debug Features


## Implementation Guide


## Registers
{{% registers x }}
