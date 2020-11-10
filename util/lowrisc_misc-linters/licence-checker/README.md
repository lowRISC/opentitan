# Licence Checker

This script can check most text file formats that we have checked our
repositories, though it has some limitations. It ensures the entire licence
appears on consecutive lines in the first comment in the file, and those lines
contain nothing else.

The primary limitation of the checker is that each file suffix can only match
one comment style, which is used for checking for the licence header. In text
formats which accept multiple comment styles, there is now a canonical one that
the licence must use. Where available, the licence should use a line comment
style.

The other limitation is for files where the canonical style is block comments,
like `/* */`, each line must be wrapped in the comment prefix and suffix, rather
than the whole licence header being wrapped in a single comment prefix and
suffix. This is an artefact of how the checker searches for the licence.

The checker is configured using a hjson file, which contains the exact licence
header, and a list of file patterns to exclude from checking the licence for,
which is used to exclude vendored and other externally sourced files.
Additionally, the licence checker can be configured to use regex matching using
the `match_regex` key set to "true".

# Configuration Example

```
{
  // Licence to check against.
  licence:
    '''
    Copyright lowRISC contributors.
    Licensed under the Apache License, Version 2.0, see LICENSE for details.
    SPDX-License-Identifier: Apache-2.0
    ''',
  // Optionally match the licence using regex (can be left off).
  // The default is not to use regex.
  match_regex: 'false',
  // Don't consider those paths and files when checking
  // for the licence (can contain wildcards such as `*`).
  exclude_paths: [
    '.style.yapf',
  ],
}
```
