# Wavegen -- Waveform generator in Python

Wavegen is a Python tool to read waveform descriptions in Hjson and
generate `svg` pictures of the waveform.

The source is a JSON representation of the waveform using the wavejson
format defined for Wavedrom. This is sort of described at
[here](https://github.com/drom/wavedrom/wiki/WaveJSON)

Note that the same wavejson could be embedded in a webpage and
wavedrom javascript used to render it directly in the browser. An
online editor for wavejson can be found at [https://wavedrom.com/](https://wavedrom.com/)

The example commands assume `$REPO_TOP` is set to the toplevel directory
of the repo.

### Setup

If packages have not previously been installed you will need to set a
few things up. First use `pip3` to install some required packages:
```console
$ pip3 install --user hjson
```

### Examples using standalone wavetool

Normally for documentation the `docgen` tool will automatically use
wavegen when it encounters a code block labeled for wavejson. See the
examples in the `docgen` module README.

The wavetool provides a standalone way to run wavegen.

The basic test mode can be invoked with `-T`. In this case a builtin
wavejson string is used as the source and is instantiated twice (it
should look the same but the second svg will not include the defines
that can be accessed by id from the first).

```console
$ cd $REPO_TOP/util
$ ./wavetool.py -T > /tmp/out.html
```

The examples directory contains the example wavejson from the
[Tutorial](https://wavedrom.com/tutorial.html). These can be formed in
to a webpage to allow comparison with the tutorial output.

```console
$ cd $REPO_TOP/util
$ ./wavetool.py -v wavegen/examples/* > /tmp/out.html
```

## WaveJSON format and extension

The tool includes an extension to the wavejson format. In addition to
data: being used to label fields that are of type '=2345' the
alternative cdata can be used to label all active data cycles
'01=2345ud' (for example this allows the start and stop bits to be
labeled for the uart in the -T test).


### The signal object

The main object in the WaveJSON is the 'signal'. This consists of a
list of signal values or groups.

```hjson
{ "signal" : [
    value1,
    value2,
    ...
]}
```
The value is either:

* A group. This is a list with the group name as a string as the first
  element, and values for the other elements. `[ "Group name", {
  value1 }, { value2 }]` Groups may be nested, the code allows for
  three deep nesting without the name area being made larger.

* A gap. This element with no waveform generates a gap. `{}` There may
  be a `node:` element in a gap to add markers and allow labeling of
  cycles (see examples).

* A real signal! This is a comma separated list of key/value pairs:
  * `name:` the name that the signal will be labeled with
  * `wave:` a string describing the waveform using characters listed below.
  * `data:` an array of comma separated labels (or a string of space
    separated lables). The labels will be added to any of the value
    types (see below) in the waveform, four or five characters is the
    maximum that will fit for `hscale=1`, `period=1`.
  * `cdata:` **Extension to wavedrom** an array of comma separated
    labels (or a string of space separated lables). The labels will be
    added to any of the cycle types (see below) in the waveform, four
    or five characters is the maximum that will fit for hscale=1,
    period=1.
  * `period:` A positive integer that specifies the period for this signal
  * `phase:` A half-integer (integer or integer.5) specifing the phase
    shift of the signal. Positive values cause the start of the wave
    field to be discarded. Typically 0.5 to shift things back a
    half-cycle which causes the first half of the first character in
    wave to be skipped in the drawing.
  * `node:` A string specifying where timing markers should be
    placed. The string mirrors the wave string. If the node string
    contains a `.` then no marker is inserted. If it contains a
    lower-case letter then a marker with that name will be inserted
    and the letter shown on the waveform. If it contains an upper-case
    letter then a marker will be inserted but no letter shown in the
    waveform. The markers are used to add arrows in the edge
    directive.

Other than signal the top-level keys are:

* `config:` A list of key/value pairs the only one used is hscale
  which is an integer that sets the horizontal scale (1= normal,
  2=twice width etc). `config: { hscale: 2 }` **Note: skins in the
  config are not currently implemented.**

* `head:` Details of the header. This contains:
  * `text:` the string to put in the header. May also be a list with
    first element 'tspan' to add attributes/formatiing. The tspan list
    can be a three element list where the second item in `{` to `}` is
    a comma separated list of key:value pairs that will become
    `key="value"` arguments of the svg tspan and the third item is
    another string/tspan. Or the tspan list is a list of string/tspan.
  * `tick:` integer, optional. Add cycle labels and lines on rising
    egdes. The first edge is numbered with the integer given and
    subsequent edges with incrementing integers.
  * `tock:` integer, optional. Add cycle labels and lines on falling
    egdes. The first edge is numbered with the integer given and
    subsequent edges with incrementing integers.

* `tail:` As head but text and labels go below

* `edge:` An array of strings containing details of edge arrows to be
  drawn on the waveforms.


### wave characters

Characters in the wave= element describe the waveform. There are more
in the wavedrom tutorial than in the WaveJSON description. Listing the
supported ones here.

These generate a sharp square wave edge into the new state.

- `p` - (usually first in string) creates a cycle of a positive edged clock
- `n` - (usually first in string) creates a cycle of a negative edged clock
- `P` - same as p but with arrow
- `N` - same as n but with arrow
- `l` - low level
- `h` - high level
- `L` - low level with an arrow
- `H` - high level with an arrow

These generate a soft edge into the state. The data: list can be used
to labal any of the ones marked "value". Extending WaveJSON the cdata:
list can be used to label any of these. Note that a label will be
centered on the cycle and subsequent '.' extensions.

- `0` - low level
- `1` - high level
- `=` - value (default color 2)
- `2` - value with color 2
- `3` - value with color 3
- `4` - value with color 4
- `5` - value with color 5
- `x` - undefined value (crosshatch)
- `z` - high-impedance state
- `u` - pull-up (weak 1)
- `d` - pull-down (weak 0)

These generate extensions of the previous cycle:
- `.` - extends previous cycle
- `|` - extends previous cycle and draw discontinuity gap on top of it

### edge arrows

Each element in the `edge:` array is a single string that describes
an arrow or line and the label that is associated with the arrow/line.

```hjson
{ ...
  "edge"   : ["a->b edge 1", "b-~>c My Second Edge"]
}
```

The string may contain multiple words separated by spaces. The first
word defines the from and to points and the arrow shape. The rest of
the text (after first space gap) will be placed as the label on the
line. The first and last characters in the arrow text select the
markers (defined in a node string) used as the endpoints for a line
(if these are upper case letters then no text is shown for the marker
but the line will be drawn to the corresponding point). The central
characters define the line shape. If the first shape character is a
`<` an arrowhead is inserted pointing to the start marker. If the last
character in the shape is a `>` an arrowhead is inserted pointing to
the end marker. (Note the original wavedrom may not support only
having an arrow to the start marker.) The remaining characters define
the arrow to be used:

* `-` a straight line between the markers, label centered on line
* `~ ` a curved line between the markers, label centered on line
* `-~` a curved line between the markers biased to end, label closer
  to end marker
* `~-` a curved line between the markers biased to start, label closer
  to start marker
* `-|` a straight line horizontally from the start then vertically to
  end, label closer to the end
* `|-` a straight line vertically from the start then horizontally to
  end, label closer to the start
* `-|-` a straight line horizontally from the start to the horizontal
  mid-point, then vertically, then horizontal to the end, label
  centered

See examples for how the different sorts of arrows actually look.
