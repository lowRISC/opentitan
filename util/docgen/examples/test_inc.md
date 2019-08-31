{{% lowrisc-doc-hdr Example like first gpio }}
{{% regfile gp.hjson }}

Blah

{{% toc 3 }}

## Compatibility

* Try out [Anchor 1][] defined in outer
* Try out [Anchor 2][] defined in include depth 1
* Try out [Anchor 3][] defined in include depth 2


{{% include include/included.md }}

[Anchor 1]: https://github.com/lowRisc

## this include should fail

{{% include no_such_file.md }}

## exec include

This should work since there is an exec ls in the directory
{{% include !ls -1 errors.md errorsregs.hjson }}```
```

This should fail because command does not exist {{% include !ps au }}

This should fail for trying to escape the repo {{% include !../../../../foo }}

# big include

{{% include !../../regtool.py --doc }}

## Theory of operation

Check for cross reference to !!DATA_OUT and !!INT_CTRL and !!INT_CTRL2 blah

## Programmer Guide


### Initialization


### Interrupts



### Debug Features


## Implementation Guide


## Registers
{{% registers x }}
