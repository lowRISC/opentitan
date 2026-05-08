# Contributing to OpenTitan

Thank you for your interest in contributing to OpenTitan.
This document provides some guidelines to making those contributions.
Important points before getting started:
* We consider honest feedback crucial to quality.
  We work hard to thoroughly review changes and provide actionable feedback.
  We do this to ensure a high quality open source design.
* Always assume good intent.
  Our feedback may be demanding and may even feel disheartening.
  Again, this is to support a high quality silicon design, and we definitely appreciate all OpenTitan contributions.
* Please be friendly and patient in your communications.
* All OpenTitan interactions are covered by [lowRISC's code of conduct](https://www.lowrisc.org/code-of-conduct/).
* When communicating, remember OpenTitan is a security-focused project.
  Because of this, certain issues may need to be discussed in a small group first.
  See the [Security Issues Process](#security-issues) described below for more details.
* OpenTitan involves both hardware and software.
  We follow a hybrid approach involving both silicon and software design practices.
* OpenTitan is a work in progress.
  We are always looking for ways to improve and welcome feedback on any project matter, technical or not.

**Important**: Please read the next three, short sections on reporting bugs, reporting security issues, and contributing code in preparation for making your first contribution to OpenTitan.
If you would like more details, see the [Detailed Contribution Guide](./detailed_contribution_guide/README.md).

## Security issues

Security is of major importance to the OpenTitan project.
When dealing with security matters, and in keeping with standard industry practice, there are reasons why it makes sense to be cautious and have a non-public discussion within a small group of experts before full disclosure.
For example,
* to ensure responsible disclosure of vulnerabilities,
* or to discuss the security impact of new features or proposed changes to an existing feature.

If you intend to work on potentially security sensitive matters, please first reach out to our experienced security team at security@opentitan.org before starting a public discussion.
That will enable us to engage successfully without creating undue risk to the project or its consumers.

Please refer to [https://opentitan.org/cvd-policy](https://opentitan.org/cvd-policy) for a description of our disclosure process.

## (Non-security) bug reports

Ideally, all designs are bug free.
Realistically, each piece of collateral in our repository is in a different state of maturity with some still under active testing and development.
See the [Hardware Development Stages](../project_governance/development_stages.md) for an example of how hardware progress is tracked.

We are happy to receive bug reports and eager to fix them.
Please make reports by opening a new issue in our [GitHub issue tracker](https://github.com/lowRISC/opentitan/issues).

## Contributing code

The information below aims at helping you get involved in the OpenTitan project by guiding you through our process of preparing your contribution and getting it integrated.

For straight-forward and non-invasive contributions, a high level of coordination is unlikely to be necessary.
In these cases, please open a pull request.

For larger proposed changes we ask contributors to:
* Discuss the matter with the team, either through the [opentitan-dev@opentitan.org](https://groups.google.com/a/opentitan.org/forum/#!forum/opentitan-dev) mailing list or through discussions in issues on GitHub.
  Agree on a course of action and document this in a GitHub issue.
* Implement the contribution, i.e., the solution previously agreed on, and reference the discussion when submitting the contribution.
* Have the implementation reviewed by the team, address any feedback, and finally have it integrated into the project.

### Quick guidelines for code contribution

* Keep a clean commit history. This means no merge commits, and no long series
  of "fixup" patches (rebase or squash as appropriate). Structure work as a
  series of logically ordered, atomic patches. `git rebase -i` is your friend.
* Changes should be made via pull request, with review. A pull request will be
  committed by a "committer" (an account listed in `COMMITTERS`) once it has
  had an explicit positive review.
* When changes are restricted to a specific area, you are recommended to add a
  tag to the beginning of the first line of the commit message in square
  brackets. e.g. "[uart] Fix bug #157".
* Code review is not design review and doesn't remove the need for discussing
  implementation options. If you would like to make a large-scale change or
  discuss multiple implementation options, discuss on the mailing list.
* Create pull requests from a fork rather than making new branches in
  `github.com/lowrisc/opentitan`.
* Do not attempt to commit code with a non-Apache license without discussing
  first.
* If a relevant bug or tracking issue exists, reference it in the pull request
  and commits.

## License agreements
The following information is detailed in the [CONTRIBUTING.md](https://github.com/lowRISC/opentitan/blob/master/CONTRIBUTING.md) file
* Contributor License agreement
* Organisational Agreement
* Use of Copyright messages
