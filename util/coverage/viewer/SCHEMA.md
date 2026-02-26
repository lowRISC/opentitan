# OpenTitan Coverage JSON Schema

This document describes the specialized JSON format used by the OpenTitan coverage viewer.

This format is designed to enable several advanced features beyond the standard LCOV format, such as:
* Coverage traceability with per-test coverage data.
* Focused analysis of specific firmware targets.

## Top-level Structure

```json
{
  "metadata": {
    "timestamp": "2026-02-25T12:00:00", // ISO-8601 generation time
    "commit": "abc123def..."            // Git commit hash (optional)
  },
  "test": <Collection>,                 // Aggregated test results
  "view": <Collection>                  // Filters for focused analysis
}
```

- **metadata**: Contains information about when and from which commit the coverage was collected.
- **test**: The primary coverage data aggregated from standard test runs.
- **view**: The filtering data for the coverage display.
 It defines the set of executable lines remaining in a final firmware image after linker stripping. By applying views, the viewer can isolate coverage relevant to a specific target (such as `ROM_EXT`) while omitting extraneous code like test frameworks.

## Collection Object

A Collection represents an aggregated set of coverage results from multiple tests.

```json
{
  "tests": ["test_a", "test_b"], // Names of aggregated test runs
  "files": {                     // Map of source paths to coverage
    "path/to/file.c": <FileProfile>,
    ...
  }
}
```

- **tests**: An array of strings where each entry is a label or name of a test run. The index in this array is used to reference the test in line/function hits.
- **files**: A map where keys are simplified source file paths and values are `FileProfile` objects.

## FileProfile Object

Contains line-by-line and function-level coverage metadata for a single file.

```json
{
  "l": [ // Ordered array of line metadata
    {
      "c": "void main() {", // Literal source line content
      "s": true,            // Is the line non-executable (skipped)?
      "t": [0, 2]           // Indices of tests that hit this line
    },
    ...
  ],
  "f": { // Map of function coverage
    "main": {
      "l": 10,  // 0-based definition line number
      "t": [1]  // Indices of tests that hit this function
    },
    ...
  }
}
```

### Lines (`l`)
The `l` field is an array of line objects, ordered by line number (0-based).

- **c** (contents): The literal content of the source line.
- **s** (skipped): A boolean indicating if the line is considered "non-executable" or skipped by the coverage tool.
- **t** (tests): An array of indices referring to the top-level `tests` array. If a test index is present, it means that specific test "hit" this line.

### Functions (`f`)
The `f` field is a map where keys are function names.

- **l** (lineno): The 0-based line number where the function is defined.
- **t** (tests): An array of indices referring to the top-level `tests` array that hit this function.

## Path Simplification

Paths are normalized to ensure consistency across different build environments:
- `bazel-out/k8-*/` is replaced with `generated/`.
- Absolute paths are typically avoided in favor of project-relative paths.
