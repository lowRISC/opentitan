# OpenTitan Big Number Python Model

## Generate documentation

```console
$ python -m otbnsim.doc
++++ Instruction Formats
{'id': 'L',
 'fields': [{'name': 'bodysize',
             'base': 20,
             'size': 12,
             'description': '',
             'static': False,
             'value': None},
            {'name': 'funct3',
             'base': 12,
             'size': 3,
             'description': '',
             'static': True,
             'value': None},

[...]

++++ Instructions
{'format': 'L',
 'description': 'Loop (indirect)\n'
                '\n'
                'Repeat a sequence of code multiple times. The number of '
                'iterations is a GPR\n'
                'value. The length of the loop is given as immediate.\n'
                '\n'
                'Alternative assembly notation: The size of the loop body is '
                'given by the\n'
                'number of instructions in the parentheses.\n'
                '\n'
                'LOOP <grs> (\n'
                '  # loop body\n'
                ')',
 'asm_signature': 'loop <iter>, <bodysize>',
 'code': '        model.state.loop_start(int(reg[rs1]), int(bodysize))'}

[...]
```

## Assembler

Assemble to verify everything works:

```console
$ otbn-asm << EOF
> LOOPI 8 (
>   addi x2, x2, 1
> )
> EOF
loopi 8, 1
addi x2, x2, 1
```

Produce different output format, C structs:

```console
$ otbn-asm -O carray test.S
static const uint32_t code [] = {
    0x0010140b, // loopi 8, 1
    0x00110113, // addi x2, x2, 1
};
```

Finally, generate a binary, write to output file:

```console
$ otbn-asm -O binary test.S test.bin
$ hexdump test.bin
0000000 140b 0010 0113 0011
0000008
```

## Run standalone test

```console
$ python -m otbnsim.standalone test.S
loopi 8, 1                          | [Start LOOP, 8 iterations, bodysize: 1]
addi x2, x2, 1                      | [x2 = 00000001, pc = 00000004, LOOP iteration 1/8]
addi x2, x2, 1                      | [x2 = 00000002, pc = 00000004, LOOP iteration 2/8]
addi x2, x2, 1                      | [x2 = 00000003, pc = 00000004, LOOP iteration 3/8]
addi x2, x2, 1                      | [x2 = 00000004, pc = 00000004, LOOP iteration 4/8]
addi x2, x2, 1                      | [x2 = 00000005, pc = 00000004, LOOP iteration 5/8]
addi x2, x2, 1                      | [x2 = 00000006, pc = 00000004, LOOP iteration 6/8]
addi x2, x2, 1                      | [x2 = 00000007, pc = 00000004, LOOP iteration 7/8]
addi x2, x2, 1                      | [x2 = 00000008, LOOP iteration 8/8]
```

## Run pytest

```console
$ pytest
```

Grab model trace for debugging

```console
$ pytest --model-verbose
```

## Get program from database of test programs

Test programs are available in a python module. Assembly code are stored in this
file and they can be generated as with the assembler.

Examples:

- Produce assembly code

```console
$ python test/programs.py mul_256x256
```

Produce C array


```console
$ python test/programs.py -O carray mul_256x256
```

Produce binary file

```console
$ python test/programs.py -O binary mul_256x256 program.bin
```
