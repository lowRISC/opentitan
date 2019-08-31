{{% lowrisc-doc-hdr Markdown Usage and Style Guide }}

## Basics

### Summary

Markdown files are used to write most documentation.
The main markdown tool is based on [CommonMark](https://commonmark.org/) (a strongly defined, highly compatible specification of Markdown), parsed by [mistletoe](https://github.com/miyuchina/mistletoe) (a fast, extensible and spec-compliant Markdown parser in pure Python).
Mistletoe adds support for tables using the Github markdown syntax.

The markdown processing is done using the `docgen.py` tool in the `util` directory.
See the [examples README](https://github.com/lowRISC/opentitan/tree/master/util/docgen/examples) for details of running the tool.
`docgen` provides extensions to the markdown syntax to support documenting [Comportable](comportability_specification.md) components.

This guide covers the enhancements provided by the lowRISC markdown extensions that are used in the project along with a recommended style.
As with all style guides the intention is to:

*   promote consistency across projects
*   promote best practices
*   increase code sharing and re-use

{{% toc 3 }}

### Terminology Conventions

Unless otherwise noted, the following terminology conventions apply to this style guide:

*   The word ***must*** indicates a mandatory requirement.
    Similarly, ***do not*** indicates a prohibition.
    Imperative and declarative statements correspond to ***must***.
*   The word ***recommended*** indicates that a certain course of action is preferred or is most suitable.
    Similarly, ***not recommended*** indicates that a course of action is unsuitable, but not prohibited.
    There may be reasons to use other options, but the implications and reasons for doing so must be fully understood.
*   The word ***may*** indicates a course of action is permitted and optional.
*   The word ***can*** indicates a course of action is possible given material, physical, or causal constraints.

### Style Guide Exceptions

***Justify exceptions with a comment.***

No style guide is perfect.
There are times when the best path to a working design, or for working around a tool issue, is to simply cut the Gordian Knot and create code that is at variance with this style guide.
It is always okay to deviate from the style guide by necessity, as long as that necessity is clearly justified by a brief comment.

## lowRISC Markdown extensions

The following extensions have been made for the lowRISC version:

*   `{{% lowrisc-doc-hdr Title Of Doc }}` Insert a standard title header and give the document a title.
    **Note** that this header includes indicating copyright lowRISC contributors.
    Eventually this will be extended to have lowrisc-doc-hdr=type (type could be component, core, guide,...) to allow the tool to validate required sections are in the document.

*   `{{% regfile filename.hjson }}` Pointer to the comportable IP interface and register definition Hjson.
    This is expected to go early in the document.
    After this line the registers and hardware configuration are available as markup items.
    Any path in the filename is relative to the directory containing the markdown file.

*   `{{% toc <depth> }}` Insert the table of contents at this point in the document.
    The `<depth>` must be an integer and indicates depth to generate the contents.
    The table inserted contains pointers to all headings from level 2 to the depth.
    Table of contents entries are generated for all markup headings (lines starting `#` for level 1 to `######` for level 6), from Section1 (equivalent to level 2) and Section2 (equivalent to level 3) directives (see below) and for register definitions in the register table.

*   `{{% registers x }}` Insert the register tables that were generated from the Hjson file imported with the `regfile` directive.
    This directive must occur later in the file than the regfile extension!
    TODO: fix the need for `x`.

*   `{{% hwcfg name }}` Insert the details of the comportable hardware configuration that was generated from the Hjson file imported with the `regfile` directive.
    The `name` is used as the descriptive name in the generated text and would normally match the IP name.
    This directive must occur later in the file than the regfile extension!

*   `{{% Section1 Section Title }}` Similar to `##` but format the title using lowRISC section formatting.
    See [discussion below](#headings-and-sections).
    In the future the section title may be used to check the document contains the expected sections.

*   `{{% Section2 Section Title }}` Similar to `###` but format the title using lowRISC section formatting.
    See [discussion below](#headings-and-sections).
    In the future the section title may be used to check the document contains the expected sections.

*   `{{% include file }}` Insert the file into the markdown document.
    Any other text on the same line as the include directive will be inserted, then a newline and then the included file.
    The file is included before any other processing so the result is a single file processed by the markdown processor (thus all definitions like anchor links are global and not confined to the file they are in).
    Includes may be nested.
    The filename is relative to the directory that the markdown file currently being processed is in (so relative links work from inside included files).
    If the include file is not found then an error is reported and a line indicating the error will be inserted in the markdown.

*   `{{% include !command -options }}` Use the shell to cd to the directory that the markdown file is in and run the command with given options (everything from the `!` to the closing `}}` is used as the shell command).
    Insert the output (stdout) from the command into the markdown document.
    Any other text on the same line as the include directive will be inserted, then a newline and then the command output.
    (As a result, if the triple back-tick to start a code block immediately follows the `}}` then the output from the command will be inserted inside that code block.)
    Error returns from the command will be ignored, and any output on stderr will be reported in the docgen stderr output.
    This can be used to include generated output in a document or to pull in things like example code.


*   `!!Reg` or `!!Reg.Field` Insert Component.Reg or Component.Reg.Field in the output file as a hyperlink to the register table for Reg and tagged for special CSS decoration (currently makes them blue, monospace and a little smaller).
    If Reg is not in the list of registers read from the regfile directive then a warning is printed and the output is not transformed.
    (Note the use of period rather than underline as the separator was to avoid syntax highlighter issues because of markdown's use of underline for italics.)

*   ` ```lang ` Code blocks are highlighted by [pygments](http://pygments.org/) (a generic syntax highlighter in python).
    Background colour can be set using the {.good} and {.bad} tags after the lang.

*   ` ```wavejson ` Code blocks describing waveforms are converted into an svg picture in the output file.
    See more detailed [description below](#waveforms).
    If the docgen tool is invoked with the `-j` or `--wavesvg-usejs` flag then instead of an inline svg this directive will generate the `<script>` output needed by the online WaveDrom javascript parser and include invocation of wavedrom in the output html.

## General Markdown Style

### Line length

There are two acceptable styles for line wrapping in markdown files:

1.  Wrap lines at under 80 characters.
    This ensures that the source is readable without any markdown processing, but re-wrapping a paragraph after an insertion or deletion tends to cause more diffs when the change is reviewed.
    When making changes to a document using this style consider allowing short lines rather than a full re-wrap after minor edits.
    Then occasionally a separate commit can be used that only does re-wrapping of the paragraphs.
    This style is recommended for all README files.

2.  Have a single sentence per line and allow the line to be as long as is required.
    This ensures change reviews highlight only the actual change at the expense of making the source harder to read.

### Headings and sections

The title of the document should be provided using the `lowrisc-doc-hdr` directive.
Therefore there should be no use of level 1 headings (lines starting `#`).

Standard headings should use the `Section1` (a level 2 heading like `##`) or `Section2` (a level 3 heading like `###`) directive and will be decorated in the project style.

Other headings should use standard markdown heading syntax (lines starting `##` though `######` for level 2-6).

Headings and sections are given ID tags to allow cross references.
The ID is the text of the heading, converted to lower case and with spaces converted to `-`.
Thus `### Headings and sections` gets the ID `headings-and-sections` and can be referenced using the markdown hyperlink syntax `[link text](#headings-and-sections)`.

Headings and sections are added to the table of contents.
When it is inserted the maximum depth can be specified.

### Images

Pictures can be included using the standard Markdown syntax (`![Alt Text](url)`).
The preferred format is Scalable Vector Graphics (`.svg`), alternatively Portable Network Graphics (`.png`).

### Waveforms

Waveforms can be included by adding [wavejson](https://github.com/wavedrom/schema/blob/master/WaveJSON.md) code blocks introduced with ` ```wavejson `.
The `docgen` markdown processor will convert these into an inline SVG image when it generates html.

There is a standalone tool for wavejson to svg conversion.
Details of the tool and a full description of the wavejson syntax that is supported can be found in the [README](https://github.com/lowRISC/opentitan/tree/master/util/wavegen) for the `wavegen.py` tool.
Note that there are several incomplete descriptions of wavejson, the syntax supported is derived primarily from the examples in the [WaveDrom Tutorial](https://observablehq.com/@drom/wavedrom).

An online editor for wavejson can be found on the [WaveDrom](https://wavedrom.com/) website.
The processor built in to `docgen` should produce the identical output, but has one extension that `cdata` may be used in place of `data` to allow labeling all bit positions not just the `2345` ones.



### Comments

Comments are rare, but should be used where needed.
Use the html `<!--` and `-->` as the comment delimiters.


### Markdown file extensions

The markdown files should use the `.md` or `.mkd` file extension.


## Markdown file format for IP module descriptions

Typically the markdown file for an IP block follows the same outline.

The header instantiates the standard document header and reads the Hjson description of the module.

```
{{% lowrisc-doc-hdr Name HWIP Technical Specification }}
{{% regfile name_reg.hjson}}

{{% section1 Overview }}

```

This is followed by some boiler-plate comments and the table of contents.

```
This document specifies Name hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](./comportability_specification.md)
See that document for integration overview within the broader top level system.

{{% toc 3 }}
```

The next section summarizes the feature set of the IP block.

```
{{% section2 Features }}

* Bulleted list
* Of main features
```

There then follows a general description of the IP

```
{{% section2 Description }}

Description of the IP.
```
The Compatibility information will allow device driver writers to identify existing code that can be used directly or with minor changes.

_This section is primarily of interest to software engineers._


```
{{% section2 Compatibility }}

Notes on if the IP register interface is compatible with any existing register interface.
Also note any differences.
For example: Matches 16550 UART interface but registers are at 32-bit word offsets.
```

The next major section is a more detailed operational description of the module.

```
{{% section1 Theory of Operations }}

```

Conventionally one of the first sections includes a block diagram and a description.

_Should be useful to hardware designers, verification engineers and software engineers._


```

{{% section2 Block Diagram }}

![Name Block Diagram](block_diagram.svg)

```

There should be a section containing the automatically generated description of the IP including the signals, interrupts and alerts that it uses.

_Primary user is the SoC integrator, but useful for everyone._

Note that the interrupt descriptions are also automatically placed in the interrupt status register bit descriptions, which is the most likely place for software engineers to reference them.


```

{{% section2 Hardware Interfaces }}

{{% hwcfg uart}}

```

The organization of the design details section is done to suit the module.

```

{{% section2 Design Details }}

Details of the design.

### Many third level headings
```
There are probably waveforms embedded here:

````

```wavejson
{
  signal: [
    { name: 'Clock',        wave: 'p............' },
  ]
}
```

````

The final major section is the software user guide and describes using the IP and notes on writing device drivers.
Code fragments are encouraged.

_This section is primarily for software engineers, but it is expected that the code fragments are used by verification engineers._

```

{{% section1 Programmers Guide }}

```

One important thing here is to show the order of initialization that has been tested in the verification environment.
In most cases other orders will work, and may be needed by the software environment, but it can be helpful in tracking down bugs for the validated sequence to be described!

````
{{% section2 Initialization }}

```c
 if (...) {
   a = ...
 }
```

````

Other sections cover different use cases and example code fragments.

```

{{% section2 Use case A (eg Transmission) }}

{{% section2 Use case B (eg Reception) }}

```

It is important to include a discussion of error conditions.

```
{{% section2 Error conditions }}

```

Also comment on anything special about interrupts, potentially including the priority order for servicing interrupts.


```

{{% section2 Interrupt Handling }}

```

The document should end with the automatically generated register tables.

```
{{% section2 Register Table }}

{{% registers x }}

````

To allow cut/paste of the default structure, here is an uncommented version:

````
{{% lowrisc-doc-hdr Name HWIP Technical Specification }}
{{% regfile name_reg.hjson}}

{{% section1 Overview }}

This document specifies Name hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](./comportability_specification.md)
See that document for integration overview within the broader top level system.

{{% toc 3 }}

{{% section2 Features }}

* Bulleted list

{{% section2 Description }}


{{% section2 Compatibility }}


{{% section1 Theory of Operations }}


{{% section2 Block Diagram }}

![Name Block Diagram](block_diagram.svg)

{{% section2 Hardware Interfaces }}

{{% hwcfg Name }}

{{% section2 Design Details }}

### Many third level headings

{{% section1 Programmers Guide }}

{{% section2 Initialization }}

{{% section2 Use case A (eg Transmission) }}

{{% section2 Use case B (eg Reception) }}

{{% section2 Error conditions }}

{{% section2 Interrupt Handling }}

{{% section2 Register Table }}

{{% registers x }}

````
