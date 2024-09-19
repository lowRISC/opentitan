# Adding Python Dependencies to the Project

To comply with software supply chain security requirements of various project partner organizations, we pin our Python packages to specific versions, and provide hashes for each dependency (including transitive dependencies).
We accomplish this with the help of the `uv pip compile` command, which is part of the `uv` package.

If you need to add another Python package to the project, do so by:
1. adding the package and version number to the `pyproject.toml` file, in the form of `<package> ~= <version>` (or `<package> == <version>` in case a specific version is needed), and
1. run the script `util/sh/scripts/gen-python-requirements.sh`, which will auto-generate the updated `python-requirements.txt` file.
