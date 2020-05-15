---
title: "Markdown Usage and Style Guide"
---

## Basics

### Summary

Markdown files are used to write most documentation.
The main Markdown tool is [Hugo](https://gohugo.io).

The Markdown processing is done using the `build_docs.py` tool in the `util` directory.

As with all style guides the intention is to:

*   promote consistency across projects
*   promote best practices
*   increase code sharing and re-use


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

## General Markdown Style

### Line length

In OpenTitan, most--but not all--Markdown documents will be rendered to HTML before they are presented to the reader.
However, README files are an important exception, and so the recommended line-wrapping style differs for these two types of files.

1. ***Rendered Files***:
Files which are intended to be rendered before viewing should have exactly one sentence per line, with no line breaks in the middle of a sentence.
This way change reviews will highlight only those sentences which are modified.
Though the long line lengths make the files slightly less convenient to read from the command-line, this greatly simplifies the review process.
When reviewing Markdown changes, every altered sentence will be included in its entirety in the file diff.

2. ***README Files***:
README files should wrap lines at under 80 characters.
This ensures that the source is readable without any Markdown processing.
Please note, however, that re-wrapping a paragraph after an insertion or deletion tends to cause longer diffs when the change is reviewed.
When making changes to a document using this style, please consider allowing short lines rather than a full re-wrap after minor edits.
Then occasionally separate commits can be used that only do re-wrapping of the paragraphs.

### Headings and sections

The title of the document should be provided using the `title` field in the frontmatter.

Headings and sections are given ID tags to allow cross references.
The ID is the text of the heading, converted to lower case and with spaces converted to `-`.
Thus `### Headings and sections` gets the ID `headings-and-sections` and can be referenced using the Markdown hyperlink syntax `[link text](#headings-and-sections)`.

Headings and sections are added to the table of contents.

### Images

Pictures can be included using the standard Markdown syntax (`![Alt Text](url)`).
The preferred format is Scalable Vector Graphics (`.svg`), alternatively Portable Network Graphics (`.png`).

### Waveforms

Waveforms can be included by adding [wavejson](https://github.com/wavedrom/schema/blob/master/WaveJSON.md) code surrounded by `{{</* wavejson */>}}` shortcode tags.

### Text Format

Where possible, please restrict Markdown text to the ASCII character set to avoid downstream tool issues.
Unicode may be used when referring to proper names.

### Comments

Comments are rare, but should be used where needed.
Use the HTML `<!--` and `-->` as the comment delimiters.

### Markdown file extensions

The Markdown files should use the `.md` file extension.

## Markdown file format for IP module descriptions

Typically the Markdown file for an IP block follows the same outline.

The header instantiates the standard document header and reads the Hjson description of the module.

```
---
title: "Example IP Block"
---
```

This is followed by some boiler-plate comments.

```
This document specifies Name hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.]({{</* relref "doc/rm/comportability_specification" */>}})
See that document for integration overview within the broader top level system.
```

The next section summarizes the feature set of the IP block.

```
## Features

* Bulleted list
* Of main features
```

There then follows a general description of the IP

```
## Description

Description of the IP.
```
The Compatibility information will allow device driver writers to identify existing code that can be used directly or with minor changes.

_This section is primarily of interest to software engineers._


```
## Compatability

Notes on if the IP register interface is compatible with any existing register interface.
Also note any differences.
For example: Matches 16550 UART interface but registers are at 32-bit word offsets.
```

The next major section is a more detailed operational description of the module.

```
# Theory of Operations

```

Conventionally one of the first sections includes a block diagram and a description.

_Should be useful to hardware designers, verification engineers and software engineers._


```

## Block Diagram

![Name Block Diagram](block_diagram.svg)

```

There should be a section containing the automatically generated description of the IP including the signals, interrupts and alerts that it uses.

_Primary user is the SoC integrator, but useful for everyone._

Note that the interrupt descriptions are also automatically placed in the interrupt status register bit descriptions, which is the most likely place for software engineers to reference them.


```

## Hardware Interfaces


```

The organization of the design details section is done to suit the module.

```

## Design Details

Details of the design.

### Many third level headings
```
There are probably waveforms embedded here:

```

{{</* wavejson */>}}
{
  signal: [
    { name: 'Clock',        wave: 'p............' },
  ]
}
{{</* /wavejson */>}}

```

The final major section is the software user guide and describes using the IP and notes on writing device drivers.
Code fragments are encouraged.

_This section is primarily for software engineers, but it is expected that the code fragments are used by verification engineers._

```

# Programmers Guide

```

One important thing here is to show the order of initialization that has been tested in the verification environment.
In most cases other orders will work, and may be needed by the software environment, but it can be helpful in tracking down bugs for the validated sequence to be described!

```
## Initialization
```
```c

 if (...) {
   a = ...
 }
```

Other sections cover different use cases and example code fragments.

```

## Use case A (eg Transmission)

## Use case B (eg Reception)

```

It is important to include a discussion of error conditions.

```
## Error conditions

```

Also comment on anything special about interrupts, potentially including the priority order for servicing interrupts.


```

## Interrupt Handling

```

The document should end with the automatically generated register tables.

```
## Register Table

{{</* registers "hw/ip/component/data/component.hjson" */>}}

```

To allow cut/paste of the default structure, here is an uncommented version:

```
---
title: Name HWIP Technical Specification
---

# Overview

This document specifies Name hardware IP functionality.
This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})
See that document for integration overview within the broader top level system.

## Features

* Bulleted list

## Description


## Compatibility


# Theory of Operations


## Block Diagram

![Name Block Diagram](block_diagram.svg)

## Hardware Interfaces

{{</* hwcfg "hw/ip/component/data/component.hjson" */>}}

## Design Details

### Many third level headings

# Programmers Guide

## Initialization

## Use case A (eg Transmission)

## Use case B (eg Reception)

## Error conditions

## Interrupt Handling

## Register Table

{{</* registers "hw/ip/component/data/component.hjson" */>}}

```
