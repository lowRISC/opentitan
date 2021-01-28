# RIG Configuration files

This directory contains YAML files that describe configurations for
the Random Instruction Generator (RIG). If not told otherwise, the RIG
will read default.yml.

# Inheritance

Configurations can inherit from one another. There are two uses for
this. Firstly, it allows us to define customised versions of a more
standard configuration. For example, you might have a configuration
that's just like the normal one but with many more loop instructions.

Secondly, we allow a configuration to give a list of possible parent
configurations from which it should inherit. This allows a generic
test to make (weighted) picks from different base configurations.

The details of how to specify a list of parent configurations for are
described with the `inherits` field below. Once these have been
resolved, we resolve each parent configuration, merge those together
and finally merge with any fields defined in the current file.

Since the values stored in the file are essentially just weights
(defining non-normalized probability distributions), we merge
configurations by multiplying the weights together pointwise. We call
the final resulting configuration the *elaborated* configuration.

## Schema

The valid keys for these YAML files are:

- gen-weights:

  A dictionary of weights, keyed by generator name. In the elaborated
  configuration, there must be a weight defined for each generator (in
  practice, this is ensured by listing a weight for each in
  `base.yml`).

  These weights select the generator to try when starting a snippet.
  Note that instruction weights are mostly independent of this choice:
  increasing the instruction weights for `BEQ` and `BNE` won't affect
  the number of branches generated. The only exception to this rule is
  if the weights of all the instructions that the generator can use
  are zero. For example, setting the instruction weights for `BEQ` and
  `BNE` to zero will disable the branch generator.

- insn-weights:

  A dictionary of weights, keyed by instruction mnemonic. These are
  used by generators like StraightLineInsn to pick *which* straight
  line instruction to generate. To disable an instruction completely,
  set its weight to zero.

  These weights are also used by the special purpose generators. For
  example, the branch generator picks whether to use `BEQ` or `BNE`
  with weights from insn-weights.

- inherit:

  The most general form for this field is a list of dictionaries. Each
  dictionary represents a possible choice of parents and one is picked
  at elaboration time.

  Each dictionary must have a field called `cfgs`, which is a string
  giving a list of parent configurations separated by `+` signs. It
  may also have a field called `weight` giving the weight of the entry
  (defaulting to 1).

  As a shorthand, an entry in the list can be a string, in which case
  this string is interpreted as the `cfgs` field, with a weight of 1.

  As an even shorter shorthand, a one-item list whose only item is a
  string can be replaced by just that string.
