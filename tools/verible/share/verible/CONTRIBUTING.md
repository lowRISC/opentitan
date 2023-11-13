---
---

# How to Contribute

We'd love to accept your patches and contributions to this project. There are
just a few small guidelines you need to follow.

## Communciation

Communication will help your concept reach consensus before getting to code, and
potentially conserve time and effort.

*   Join the developer's mailing list: verible-dev@googlegroups.com
    ([join](https://groups.google.com/forum/#!forum/verible-dev/join))
*   Use the github issue tracker to discuss and comment on specific issues. We
    use the assignment status to signal who is working on what. Ask to be
    assigned to an issue if you'd like to volunteer, and un-assign yourself if
    you find yourself unavailable.

## Contributor License Agreement

Contributions to this project must be accompanied by a Contributor License
Agreement. You (or your employer) retain the copyright to your contribution;
this simply gives us permission to use and redistribute your contributions as
part of the project. Head over to <https://cla.developers.google.com/> to see
your current agreements on file or to sign a new one.

You generally only need to submit a CLA once, so if you've already submitted one
(even if it was for a different project), you probably don't need to do it
again.

## Code reviews

All submissions, including submissions by project members, require review. We
use GitHub pull requests for this purpose. Consult
[GitHub Help](https://help.github.com/articles/about-pull-requests/) for more
information on using pull requests.

### Style

Our C++ code mostly follows [Google's C++ style guide][google-cpp-style].

On a pull request, the Continuous Integration (CI) will verify this style, so
to make this smooth, run `clang-format` on your modified files before submitting
a pull request:

```
clang-format --style=file -i <your-modified-c++-files>
```

### Testing

Testing is a critical component to any code contribution. Make sure your the
changes you introduce come with test code to protect against future regression.
Prefer unit-tests in most cases, and end-to-end tests in others. We also welcome
contributions that contain _only_ test cases (where no code change is needed)!

We encourage you to start on any open issue by proposing test cases for
discussion before diving into any implementation. Where applicable, also
consider _negative_ tests. Try to keep the majority of tests small and focused.

#### Running Code Coverage

Code coverage is run in each pull request and tracked on [codecov].
Tests for any new feature should exercise all possible branches;
pull requests should strive for 100% differential coverage.

To inspect coverage locally, run

```
MODE=coverage .github/bin/build-and-test.sh
.github/bin/generate-coverage-html.sh
```

The coverage report can then be found in `coverage-html/index.html`

## Community Guidelines

This project follows
[Google's Open Source Community Guidelines](https://opensource.google/conduct/).

<!-- reference links -->

[google-cpp-style]: https://google.github.io/styleguide/cppguide.html
[codecov]: https://app.codecov.io/gh/chipsalliance/verible
