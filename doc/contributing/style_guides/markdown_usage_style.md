# Markdown Usage and Style Guide

## Summary

Markdown is used to write most documentation, specifically [Commonmark][] with [minimal extensions](#extensions).
The main Markdown tool is [mdBook](https://rust-lang.github.io/mdBook/).
It is normally run as part of the `./util/site/build-docs.sh` script that builds all `mdbook` books as well as run documentation generators such as `doxygen`.
*See [Contributing to Documentation](../doc/README.md) for more information.*

In OpenTitan, most readers will read the documentation once it has been rendered to HTML on the website or GitHub.
However, it is important that files are pleasant to read in plain text because viewing in the plain text can be more convenient when working in the codebase and when contributing to documentation the plain text form is what has to be read and edited.

## About this Style Guide

As with all style guides the intention is to:

* Promote consistency across projects.
* Promote best practices.
* Increase code sharing and re-use.

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


## Filename

The Markdown file names should be in snake case and should use the `.md` file extension.

## Extensions

One must only use [CommonMark][] with the exception of the following extensions:
- [GFM Tables](https://github.github.com/gfm/#tables-extension-)
- [GFM Task Items](https://github.github.com/gfm/#task-list-items-extension-)
- [Inline maths and maths blocks](#maths)

## Line length and Whitespace

Files must have exactly one sentence per line, with no line breaks in the middle of a sentence.
This way change reviews will highlight only those sentences which are modified.
Though the long line lengths make the files slightly less convenient to read from the command-line, this greatly simplifies the review process.
When reviewing Markdown changes, every altered sentence will be included in its entirety in the file diff.

Markdown files must contain no trailing white space.
As a result, two or more spaces must not be used for [hard line breaks][].
Instead, a double new line is recommended.
[Backslash hard breaks][] can also be used.

## HTML

Do not use inline HTML within markdown documents.
Although it offers a lot of flexibility, this flexibility is hard to handle.
- It is possible to break the website
- Markdown renderers often support different subsets of HTML.
- The use of HTML restricts the ease at which documentation could be converted to other forms in the future, such as PDF.

Reaching for HTML may suggest that:
- You need to split the concepts into more smaller parts that can be expressed in markdown syntax.
- The concept would be better explained in an svg diagram.

*The one exception to this is [comments](#comments).*

## Links

The [GFM autolinks extention][] is not used so links should be flanked by `<` and `>` characters.

One must not use [shortcut reference link][]s, but instead use [collapsed reference link][]s.
This is because it can be ambiguious whether [shortcut reference link][] are meant to be links or not.
Consequently, linters and other tool, such as [marksman](https://github.com/artempyanykh/marksman), cannot warn you of referencing errors.
*Note: [link labels are case insensitive](https://spec.commonmark.org/0.30/#example-554).*

Example of reference syntaxes:

````md
Don't use shortcut references like [this].
Instead use collapsed references like [this][].
[These][this] full reference links are fine as well of course.

[this]: https://example.com
````

## Headings and Sections

Only [ATX headings][] must be used.
Do not use [Setext headings][] for the following reasons.
- Their depth isn't as immediately obvious.
- They only go to a maximum depth of 2.
- They take longer to type and maintain in a nice manner.

Headings and sections are given ID tags, by the mdBook and GitHub when rendering, to allow cross references.
The ID is the text of the heading, converted to lower case with spaces converted to `-` and non-alphanumeric characters removed.
Thus `### Headings and sections` gets the ID `headings-and-sections` and can be referenced using the Markdown hyperlink syntax `[link text](#headings-and-sections)`.

## Code Blocks

Only [fenced code blocks][] must be used and not [indented code blocks][].
Fenced blocks allow more context through [info string][]s and are easier to distinguish from the rest of the text than indented blocks, especially when nested in lists.

Shell code blocks should default using `sh` in their [info string][], unless a non posix shell syntax is used.
These blocks must not include `$` at the beginning of lines, and one must make sure to escape new lines when splitting up a command for readability.
It is recommended that arguments a user is likely to change are made variables; this highlights them to the user.

```sh
util/dvsim/dvsim.py \
    hw/ip/uart/dv/uart_sim_cfg.hjson \
    -i uart_smoke \
    --fixed-seed=$SEED
```

When one wants to show the output of an interactive session in the same code block, for example as part of a guide, one may use the `console` [info string][].
In this case, it is recommended to use `$` or `#` at the beginning of command lines, where `$` denotes the command being run as a non-root user and `#` a root user.

```console
$ echo "Hello world"
Hello World
# sudo apt install cowsay
...
```

## Images

Pictures can be included using the standard Commonmark syntax (`![Alt Text](url)`).
The preferred format is Scalable Vector Graphics (`.svg`), alternatively Portable Network Graphics (`.png`).

## Waveforms

Waveforms can be included by describing them in [wavejson](https://github.com/wavedrom/schema/blob/master/WaveJSON.md) within a code block with a `wavejson` [info string][].

## Maths

Maths can be included inline or within blocks using a single or double `$` respectively.
As a result, the `$` symbol has to be escaped when not wishing to write mathematical notation.

````md
$$
\nabla \cdot \boldsymbol{B} = 0
$$

where $\boldsymbol{B}$ is the magnetic field.

That's saved you \$100 on a text book.
````

## Comments

Comments are rare, but should be used where needed.
Use the HTML `<!--` and `-->` as the comment delimiters.


[commonmark]: https://spec.commonmark.org/
[atx headings]: https://spec.commonmark.org/0.30/#atx-headings
[setext headings]: https://spec.commonmark.org/0.30/#setext-heading
[collapsed reference link]: https://spec.commonmark.org/0.30/#collapsed-reference-link
[shortcut reference link]: https://spec.commonmark.org/0.30/#shortcut-reference-link
[indented code blocks]: https://spec.commonmark.org/0.30/#indented-code-block
[fenced code blocks]: https://spec.commonmark.org/0.30/#fenced-code-blocks
[info string]: https://spec.commonmark.org/0.30/#info-string
[hard line breaks]: https://spec.commonmark.org/0.30/#hard-line-breaks
[backslash hard breaks]: https://spec.commonmark.org/0.30/#example-634
[gfm tables]: https://github.github.com/gfm/#tables-extension-
[gfm list items]: https://github.github.com/gfm/#task-list-items-extension-
[gfm autolinks extention]: https://github.github.com/gfm/#autolinks-extension-
