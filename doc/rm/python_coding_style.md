---
title: "Python Coding Style Guide"
---

## Basics

### Summary

Python3 is the main language used for simple tools.

Python can be written in vastly different styles, which can lead to code conflicts and code review latency.
This style guide aims to promote Python readability across groups.
To quote the C++ style guide: "Creating common, required idioms and patterns makes code much easier to understand."

This guide defines the lowRISC style for Python version 3.
The goals are to:

*   promote consistency across hardware development projects
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
It is always okay to deviate from the style guide by necessity, as long as that necessity is clearly justified by a brief comment, as well as a lint waiver pragma where appropriate.

A common case where you may wish to disable tool-enforced reformatting is for large manually formatted data literals.
In this case, no explanatory comment is required and yapf can be disabled for that literal [with a single pragma](https://github.com/google/yapf#why-does-yapf-destroy-my-awesome-formatting).

## Python Conventions

### Summary

The lowRISC style matches [PEP8](https://www.python.org/dev/peps/pep-0008/) with the following options:
* Bitwise operators should be placed before a line split
* Logical operators should be placed before a line split

To avoid doubt, the interpretation of PEP8 is done by [yapf](https://github.com/google/yapf) and the style guide is set using a `.style.yapf` file in the top level directory of the repository.
This just sets the base style to pep8 and overrides with the exceptions given above.

In addition to the basic style, imports must be ordered alphabetically within sections:
* Future
* Python Standard Library
* Third Party
* Current Python Project

The import ordering matches that enforced by [isort](https://github.com/timothycrosley/isort).
Currently the `isort` defaults are used.
If this changes a `.isort.cfg` file will be placed in the top level directory of the repository.

### Lint tool

The `lintpy.py` utility in `util` can be used to check Python code.
It checks all Python (`.py`) files that are modified in the local repository and will report problems.
Both `yapf` and `isort` checks are run.

Basic lintpy usage is just to run from the util directory.
If everything is fine the command produces no output, otherwise it will report the problems.
Additional information will be printed if the `--verbose` or `-v` flag is given.

```console
$ cd $REPO_TOP/util
$ ./lintpy.py
$ ./lintpy.py -v
```

Checking can be done on an explicit list of files using the `--file` or `-f` flag.
In this case the tool will not derive the list from git, so any file can be checked even if it has not been modified.

```console
$ cd $REPO_TOP/util
$ ./lintpy.py -f a.py subdir/*.py
```

Errors may be fixed using the same tool to edit the problem file(s) in-place (you may need to refresh the file(s) in your editor after doing this).
This uses the same set of files as are being checked, so unless the`--file` or `-f` flag is used this will only affect files that have already been modifed (or staged for commit if `-c`is used) and will not fix errors in Python files that have not been touched.

```console
$ cd $REPO_TOP/util
$ ./lintpy.py --fix
```

lintpy.py can be installed as a git pre-commit hook which will prevent commits if there are any lint errors.
This will normally be a symlink to the tool in util so changes are automatically used (it also works if `lintpy.py` is copied to `.git/hooks/pre-commit` but in that case the hook must be reinstalled each time the tool changes).
Since git hooks are not automatically installed the symlink hook can be installed if required using the tool:

```console
$ cd $REPO_TOP/util
$ ./lintpy.py --hook
```


Fixing style errors for a single file can also be done with `yapf` directly:
```console
$ yapf -i file.py
```

Fixing import ordering errors for a single file can be done with `isort`:
```console
$ isort file.py
```

Yapf and isort are Python packages and should be installed with pip:

```console
$ pip3 install --user yapt
$ pip3 install --user isort
```

### File Extensions

***Use the `.py` extension for Python files***

### General File Appearance

#### Characters

***Use only UTF-8 characters with UNIX-style line endings(`"\n"`).***

Follows PEP8.

#### POSIX File Endings

***All lines on non-empty files must end with a newline (`"\n"`).***

#### Line Length

***Wrap the code at 79 characters per line.***

The maximum line length follows PEP8.

Exceptions:

-   Any place where line wraps are impossible (for example, an include path might extend past 79 characters).

#### No Tabs

***Do not use tabs anywhere.***

Use spaces to indent or align text.

To convert tabs to spaces on any file, you can use the [UNIX `expand`](http://linux.die.net/man/1/expand) utility.

#### No Trailing Spaces

***Delete trailing whitespace at the end of lines.***

### Indentation

***Indentation is four spaces per level.***

Follows PEP8.
Use spaces for indentation.
Do not use tabs.
You should set your editor to emit spaces when you hit the tab key.

### Executable Python tools

Tools that can be executed should use `env` to avoid making assumptions about the location of the Python interpreter.
Thus they should begin with the line:

```console
#!/usr/bin/env python3
```

This should be followed by a comment with the license information and the doc string describing the command.

#### Argument Parsing

***Use argparse to parse command line arguments.***

In command line tools use the [argparse library](https://docs.python.org/3/library/argparse.html) to parse arguments.
This will provide support for `--help` and `-h` to get usage information.

Every command line program should provide `--version` to provide standard version information.
This lists the git repositary information for the tool and the version numbers of any Python packages that are used.
The `show_and_exit` routine in `reggen/version.py` can be used to do this.
