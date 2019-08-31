# Docgen -- lowRISC Document generator

Docgen is a python3 tool to read markdown documentation and generate html.

It works in conjunction with reggen to generate documentation with the
register information inserted. Examples are described in the README.md
in the examples subdirectory.

The lowRISC markdown is based on CommonMark (A strongly defined, highly
compatible specification of Markdown defined at
https://commonmark.org/ ) parsed by mistletoe (a fast, extensible and
spec-compliant Markdown parser in pure Python).

Mistletoe already adds tables using the Github markdown syntax.

The following extensions have been made for the lowRISC version:
* `{{% lowrisc-doc-hdr Title Of Doc }}` Insert a standard title header
  and give
  the document a title. Expected to extend this to have lowrisc-doc-hdr=type
  (type could be component, core, guide,...) to allow the tool to
  validate required sections are in the document.

* `{{% regfile filename.hjson }}` Pointer to the register definition
  json/hjson. This is expected to go early in the document. After this line
  the registers are available as markup items.

* `{{% registers x }}` Insert the register tables at this point in the
  document. Must be after the regfile extension! TODO fix the need for `x`

* `{{% include file }}` Insert the file into the markdown
  document. Any other text on the same line as the include directive
  will be inserted, then a newline and then the included file. The
  file is included before any other processing so the result is a
  single file processed by the markdown processor (thus all
  definitions like anchor links are global and not confined to the
  file they are in). Includes may be nested. The filename is relative
  to the directory that the markdown file currently being processed is
  in (so relative links work from inside included files). If the
  include file is not found then an error is reported and a line
  indicating the error will be inserted in the markdown.

* `{{% include !command -options }}` Use the shell to cd to the
  directory that the markdown file is in and run the command with
  given options (everything from the `!` to the closing `}}` is used
  as the shell command). Insert the output (stdout) from the command
  into the markdown document. Any other text on the same line as the
  include directive will be inserted, then a newline and then the
  command output. (As a result, if the triple back-tick to start a
  code block immediately follows the `}}` then the output from the
  command will be inserted inside that code block.) Error returns from
  the command will be ignored, and any output on stderr will be
  reported in the docgen stderr output.


* `!!Reg` or `!!Reg.Field` Insert Component.Reg or Component.Reg.Field
  in the output file as a link to the register table for Reg and
  tagged for special CSS decoration (currently makes them blue,
  monospace and a little smaller). If Reg is not in the list of
  registers read from the regfile directive then a warning is printed
  and the output is not transformed. (Note the use of period rather
  than underline as the separator was to avoid syntax highlighter
  issuses because of markdown's use of underline for italics.

* ` ```lang ` Code blocks are highlighted by pygments (a generic
  syntax highlighter in python). Background colour can be set using the
  {.good} and {.bad} tags after the lang.

* ` ```wavejson ` Code blocks describing waveforms are converted into
  an svg picture in the output file. The `-j` or `--wavesvg-usejs` flag
  will instead generate the <script> output needed by the WaveDrom
  javascript parser and include invocation of wavedrom in the output
  html.


* Anticipate adding support for ToC generation and insertion (there is
  partial support for this already in mistletoe)
