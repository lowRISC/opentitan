# Contributing to Documentation

## Summary

In the OpenTitan project, documentation is captured in Markdown placed close to what they are documenting in the repository.
It is viewable on the [OpenTitan website](https://opentitan.org/) or in [GitHub](https://github.com/lowrisc/opentitan) web interface, as well as in plain text.
Unlike the GitHub and plain text view, the website supplements the markdown documentation with auto-generated documentation from tools such as [rustdoc][].

The Markdown is rendered into a book for the website using [mdBook][] with the structure being determined by the `SUMMARY.md` in the root of the repository.
The `util/site/build-docs.sh` script is used to build this book as well as the landing page and auto-generated documentation.

*Before contributing to documentation, please read **[the markdown style guide](../style_guides/markdown_usage_style.md)***.

## File Structure

Documentation pertaining to the content of a directory in the repo should be within a `README.md` in that repository.
Any additional documentation that does not belong to a subdirectory should be put in a `doc` sub-directory.
Images and other assets should also be put in this doc directory.
This structure is used from the very root of the project where the `README.md` describes the project as a whole and the `doc` directory holds general information about the project that cannot be wholly contained by another subdirectory.

See [An Example IP Block's Documentation](./example_ip_block.md) to get a better sense of this structure.

## `CMDGEN`

In an effort to make as much content viewable in plain text and GitHub as possible, auto-generated markdown is checked in within documentation files.
This is done with a tool called `CMDGEN`, that lives at `./util/cmdgen.py`.
When invoked this script will search all given files for `<!-- BEGIN CMDGEN * -->` and `<!-- END CMDGEN -->` delimiters.
On each encounter, it will run the command in the 'begin' delimiter and check the commands output (`stdout`) matches the content that is between the delimiters.

Commonly one will run the following, which will go through every markdown file in the repository and, because the `-u` flag is given, update the content between the delimiters.

```sh
./util/cmdgen.py -u '**/*.md'
```

If run, the following snippet will have the register tables of the AES block (output by `util/regtool.py -d ./hw/ip/aes/data/aes.hjson`) inserted into it.

````md
# Registers

<!-- BEGIN CMDGEN #util/regtool.py -d ./hw/ip/aes/data/aes.hjson -->

<!-- END CMDGEN -->
````

*Note, one should remove the `#` before the commands.
This is there so that `CMDGEN` doesn't generate registers in this file.*


[mdBook]: https://rust-lang.github.io/mdBook/
[rustdoc]: https://doc.rust-lang.org/rustdoc/index.html
