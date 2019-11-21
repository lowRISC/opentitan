---
title: "Hjson Usage and Style Guide"
---

## Basics

### Summary

Json files are used to provide input data to many of the tools.
The preference is to use [Hjson](https://hjson.org/), which is a variation of regular JSON that is easier to write.
In particular it allows the quote marks to be left off the key names, it allows a single string to be quoted with triple quote marks and flow over multiple lines (which is often needed in text descriptions) and it allows comments using the # or // style.

This guide covers the enhancements provided by Hjson that are used in the project along with a recommended style.
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


## Hjson file format

Hjson is a variation of regular JSON that is easier to write.
There are parsers in a number of languages and the tools make extensive used of the `hjson` package provided for Python 3.
A full description can be found on the [Hjson website](https://hjson.org/), but the main features that make it convenient are that it keeps files cleaner by allowing the quote marks to be left off the key names, it enables long descriptive text by allowing a single string to flow over multiple lines and it allows comments using the # or // style.

For example:

```hjson
  key1: "value1",
  // Now a key with a long value
  key2: '''
        A long descriptive value2 that can
        span over multiple lines
        '''
```

### Text Format

Where possible, please restrict Hjson text to the ASCII character set to avoid downstream tool issues.
Unicode may be used when referring to proper names.

### File delimiters and header

***Use `{}` to delimit the file***

***Include a header comment with copyright and license information***

The file must start with a `{` and end with a `}` to be well-formed json.
In both cases these should be on a single line and have no indentation.
Anything enclosed should have two space indentation.
(Hjson allows these to be omitted but this is not recommended style.)

In most cases, before the opening `{` the file should start with a comment containing the copyright and license details and the SPDX-License-Identifier.

```hjson {.good}
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // details...
}
```

In cases where the file may need to be parsed by a standard JSON parser the comments must be omitted, but the SPDX license information should be provided as a top-level key/value using pure JSON syntax and ignored by any tool.

```json {.good}

{
  "SPDX-License-Identifier": "Apache-2.0",
  ...
}
```

### Simple key-value entries

***Use unquoted alphanumeric strings for keys***

***Include all values in quote marks***

Single entries are of the form `key: "value"` Keys must be alphanumeric strings and should not be in quotes.
(Hjson allows this.
The quotes may be included as an exception to the style guide if there is an expectation that the file needs to be parsed with a more traditional JSON parser.)
The valid keys for each tool are described in the tool documentation.
The style is for a simple value to be in quotes (even if it is a number) and the tool should manage any type conversions.

In some cases Hjson allows the quotes to be omitted from values, but this is not recommended because the value string will not be terminated by a comma so there is potential for confusion when multiple key-value pairs are put on the same line.
For example:

```hjson {.good}
      // This is recommended usage and will work as expected
      { name: "fred", tag: "2", desc: "fred has tag 2" }
```

But:

```hjson {.bad}
      // This will cause confusion. The value for tag
      // is the rest of the line after the colon
      // so desc is not defined and the close } is lost
      { name: "fred", tag: 2, desc: "fred has tag 2" }
```

### Groups of entries

***Use two character indentation for items in groups***

Groups of entries are made by enclosing a comma separated list of key/value pairs in {}.
For example

```hjson {.good}
    { name:"odd", value:"1", desc:"odd parity"}
```

In most cases a group will be too long for a single line, particularly where it has a good descriptive string.
In that case the entry should contain one key-value pair per line with a 2 character indent from the opening bracket.
The closing bracket should should not have the extra indentation.

```hjson {.good}
    {
      name:"odd",
      value:"1",
      desc:"odd parity"
    }
```

The first entry in a group may be on the same line as the opening bracket, with a single space.

```hjson
    { name:"odd",
      value:"1",
      desc:"odd parity"
    }
```

Unless the group fits on a single line, the closing bracket should not be on the same line as the final item in the group.

```hjson {.bad}
    { name:"odd",
      value:"1",
      desc:"odd parity"}
```


### Lists

***Use two character indentation for items in lists***

A list value is a comma separated list of entries or groups enclosed in [].
For example a list of groups could be presented:
```hjson
  registers: [{name:"reg1", desc:"description 1"},
              {name:"reg2", desc:"description 2"}]
```

Longer lists and any where elements split over multiple lines should use a 2 character indent from the opening bracket.
The closing bracket should not have the extra indentation.


```hjson {.good}
  registers: [
    {
      name:"reg1",
      desc:"description 1"
    },
    {
      name:"reg2",
      desc:"description 2"
    }
  ]
```

Hjson allows commas to be omitted when an item that would be terminated with a comma is terminated by the end of a line, and will tolerate extra "trailing" commas.
There is currently no style-guide rule on this.
In general, use the comma if it is likely items may be combined on a single line and ommit it if it keeps the file cleaner.


### Long strings

Long strings are encouraged for descriptive text that will be presented to users.
They are delimited by three single-quote marks.

The string should be indented to line up under the opening quote marks and the closing quote marks should be on their own line with the same indentation.

```hjson {.good}
       key: '''
            A long descriptive value that can
            span over multiple lines
            '''
```

The first line of the string may be on the same line as the opening quotes.

```hjson
       key: '''A long descriptive value that can
            span over multiple lines
            '''
```
### Comments

Comments should be used where needed.
The use of `//` as the comment delimiter is recommended, but `#` may also be used.
