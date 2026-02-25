# OpenTitan Coverage JSON Schema

This document describes the specialized JSON format used by the OpenTitan
coverage viewer.

This format is designed to enable several advanced features beyond the standard
LCOV format, such as:

*   Coverage traceability with per-test coverage data.
*   Focused analysis of specific firmware targets through views.

## Top-level Structure

```json
{
  "metadata": {
    "timestamp": "2026-02-25T12:00:00", // ISO-8601 generation time
    "commit": "abc123def..."            // Git commit hash (optional)
  },
  "tests": ["test_a", "test_b"],        // Names of aggregated test runs
  "views": ["view_a", "view_b"],        // Names of aggregated views
  "files": {                            // Map of source paths to coverage
    "path/to/file.c": <FileProfile>,
    ...
  }
}
```

-   **metadata**: Contains information about when and from which commit the
    coverage was collected.
-   **tests**: An array of strings where each entry is a label or name of a test
    run. The index in this array is used to reference the test in line hits
    (`t`).
-   **views**: An array of strings where each entry is a label or name of a
    coverage view. The index in this array is used to reference the view in line
    membership (`v`). A view defines the set of executable lines remaining in a
    final firmware image after linker stripping. By applying views, the viewer
    can isolate coverage relevant to a specific target (such as `ROM_EXT`) while
    omitting extraneous code like test frameworks.
-   **files**: A map where keys are simplified source file paths and values are
    `FileProfile` objects.

## FileProfile Object

Contains line-by-line and function-level coverage metadata for a single file.

```json
{
  "l": [ // Ordered array of line metadata
    {
      "c": "void main() {", // Literal source line content
      "s": true,            // Is the line non-executable (skipped)?
      "t": [0, 2],          // Indices of tests that hit this line
      "v": [0, 1]           // Indices of views that include this line
    },
    ...
  ],
  "f": [ // List of function definitions
    {
      "n": "main", // Function name
      "l": 10,     // 0-based definition line number
      "t": [0, 2], // Indices of tests that hit this function
      "v": [0, 1]  // Indices of views that include this function
    },
    ...
  ]
}
```

### Lines (`l`)

The `l` field is an array of line objects, ordered by line number (0-based).

-   **c** (contents): The literal content of the source line.
-   **s** (skipped): A boolean indicating if the line is considered
    "non-executable" or skipped by the coverage tool.
-   **t** (tests): An array of indices referring to the top-level `tests` array.
    If a test index is present, it means that specific test "hit" this line.
-   **v** (views): An array of indices referring to the top-level `views` array.
    If a view index is present, it means that specific line is part of that
    view.

### Functions (`f`)

The `f` field is an array of function definition objects.

-   **n** (name): The name of the function.
-   **l** (lineno): The 0-based line number where the function is defined.
-   **t** (tests): An array of indices referring to the top-level `tests` array
    that hit this function.
-   **v** (views): An array of indices referring to the top-level `views` array
    that include this function.

## Path Simplification

Paths are normalized to ensure consistency across different build environments:

-   `bazel-out/k8-*/bin/` is replaced with `generated/`.
-   Absolute paths are typically avoided in favor of project-relative paths.
