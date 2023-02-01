# `fix_imports`: Enable Absolute and Relative Imports in Scripts

Absolute and relative imports work fine when a file is executed as a module, e.g. `python3 -m util.foo.bar`, but break when the same file is executed as a script, e.g. `python3 util/foo/bar.py`.
In OpenTitan, we would like to structure our python files freely, use relative imports for ease of maintenance, and be able to run them as scripts.
To this end, this package provides the `fix_import()` function that
* Updates `sys.path` to include the root of the repo (or the directory where our python files reside) and
* Returns the value that `__package__` in the outer frame, i.e. the caller's scope, should be set to.
Modules that use absolute or relative imports should call this function if they are imported from a script.


However, just providing `fix_imports()` is not enough to solve this problem since we can't import it easily unless we add a symlink to every folder containing python code in our repo.
To address this chicken and egg problem we use this package as an in-tree dependency so that it can be used from any Python file as follows:
```
from fix_imports import fix_imports
__package__ = fix_imports()
```

See https://peps.python.org/pep-0328/#relative-imports-and-name.
