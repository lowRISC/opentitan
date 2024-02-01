# In-depth guide to contributing to OpenTitan

The way we work on OpenTitan is very similar to what is done in other collaborative open-source projects.
For a brief overview see [Contributing to OpenTitan](../README.md).
This document provides a detailed reference on how we collaborate within the OpenTitan project and is organized as follows:
* [Communication](#communication)
* [Working with Issues](#working-with-issues)
* [Overview on Contributing Code](#overview-on-contributing-code)
* [Writing Code](#writing-code)
* [Working with pull requests (PRs)](#working-with-pull-requests)

# Communication

All OpenTitan interactions, on all platforms and face to face, are covered by lowRISC's [code of conduct](https://www.lowrisc.org/code-of-conduct/).
We believe in creating a welcoming and respectful community, so we have a few ground rules we expect contributors to follow:

* be friendly and patient,
* be welcoming,
* be considerate,
* be respectful,
* be careful in the words that you choose and be kind to others, and
* when we disagree, try to understand why.

We list these principles as general guidance to make it easier to communicate and participate in the OpenTitan (and lowRISC) community.

## When to file an issue vs. sending an email vs. creating a document?

GitHub issues and shared Google Docs are generally preferable to email, as these can be more easily tracked, cross-referenced, archived and shared, e.g., with people joining later.

Emails (e.g. to the [opentitan-dev@opentitan.org](https://groups.google.com/a/opentitan.org/forum/#!forum/opentitan-dev) mailing list) are suitable to raise awareness of discussions and to call for participation.
Emails between members of a smaller group are also useful for preliminary evaluations before starting a public issue or document.

When it comes to technical discussions, either shared documents on Google Docs or GitHub issues may be used.
The former are more suitable for initial, broader discussions, for comparing different options and for soliciting comments from a wider audience on a proposal over a longer period of time, whereas the latter are more suitable for cross-referencing in pull requests, and for presenting the final proposal.
The outcome of such discussions should always be summarized in a GitHub issue for later reference.

## Where do we discuss implementation details/proposals before creating PRs?

A shared Google Doc is suitable for initial, broader discussions, for comparing different design options and for a wider audience and agile commenting, but not for revisioning, referencing and storage in the repository.
Therefore, such a shared document should always be linked from a GitHub issue and the outcome of this discussion should be summarized in that issue.
For short proposals, the entire discussion can be had in a GitHub issue, without a linked document.

## How to/why use Google Docs?

Collaborative documents are more useful than GitHub issues for initial, broader discussions, for comparing different design options and for a wider audience commenting on a proposal over a longer period of time, or when interactive editing is required.
We often make use of a Google Doc to start the discussion of an idea or proposal, before later converting it to Markdown and moving to GitHub (e.g. as a PR adding new documentation).

## When to assign issues or request specific reviewers?

We typically rely on contributors self-assigning to an issue when they start working on it, so it is best to leave issues unassigned when creating them.
If you think a particular issue might be relevant for someone, you can bring it to their attention by mentioning the username in a comment.
Team members are regularly scanning through open issues and will also help ensure issues are brought to the attention of the right people.

For PRs, you should always request reviews unless the PR is work-in-progress or just in draft state (in these cases, please explicitly label the PR as a [draft](https://github.blog/2019-02-14-introducing-draft-pull-requests/)).
In many cases, there will be a default review assignment depending on the files modified in the PR.
You are also strongly encouraged to ask for reviews from anyone you know to be working in that area.

# Working with Issues

## Labeling and assigning issues

Issue and PR labels can be useful as they help categorizing, prioritizing and assigning open issues/PRs.
When filing a new issue, you are welcome to assign labels if you feel comfortable about selecting suitable labels.
If no labels are assigned, committers and other team members might do that when browsing through the open issues/PR from time to time.
If possible, you should also add a meaningful tag to the subject line of your issue as outlined in [subject tags](#subject-tags).

In this project, we use the assignee field to indicate people who are actively working on an issue, so it's best to let people assign themselves when they start working on it.
If you'd like to bring an issue to the attention of a particular contributor or ask if they might be able to help solve it, simply mention them in a comment.

## Who should respond to filed issues?

Anyone who feels qualified to help, though if you're working outside your usual area of expertise and making a best-effort guess it's polite to say so.
If you see an issue that might be of relevance for a particular team member, you are welcome to ping this person by commenting on the issue mentioning that person (*e.g.* "@*githubname* what do you think?").

## How to reference issues in commit messages and PRs?

Commits and PRs related to existing issues or PRs should reference those.
References should always be accompanied by a brief summary of the outcome of the referenced discussion and how the current PR/commit/issue relates to that.
References are not only relevant for automatically closing issues but also and especially for documentation.

Both long references such as "lowRISC/opentitan#1" and short references "#1" can be used in commit messages.
However, short references should not be used in the subject line as they might accidentally create links to unrelated issues if commits containing such references end up in other repositories, e.g., when vendoring in external sources.

See also [References and URLs on GitHub](https://help.github.com/en/github/writing-on-github/autolinked-references-and-urls).

# Overview on Contributing Code

Depending on the size and impact of your contribution, it may need to go through the OpenTitan RFC process.
If your contribution is large, cross cutting, or potentially contentious, we will ask you to follow the procedure documented in the [Request for Comments (RFC) Process](../../project_governance/rfc_process.md).

If you believe an RFC is not required, a lighter weight process will suffice.
Note that if a core committer suggests that a contributor follow the RFC process, you will likely need to do so.
The lightweight process is:

![Code contribution process flowchart](contributing_code_flow_chart.svg)

1. Check if an issue or PR addressing the same matter already exists.
   If so, consider contributing to the existing issue/PR instead of opening a new one.
2. Assess whether the matter may be security sensitive.
   If so, follow the [[Security Issues Process](../README.md#security-issues).
3. [Create a GitHub issue](#working-with-issues) to raise awareness, start the discussion, and build consensus that the issue needs to be addressed.
   For more information, refer to [Communication](#communication).
4. Start discussing possible solutions in a smaller group, possibly outside of GitHub, but in a shared document (we typically use Google Docs for convenience) that is linked to the original GitHub issue.
   Find consensus inside the interest group and come up with a proposal.
   For short proposals, the entire discussion can be had in a GitHub issue, without a linked document.
   For more information, refer to [Communication](#communication).
5. Summarize the outcome of the discussion or the proposed solution in the original GitHub issue.
   For bug fixes, proceed to Step 8.
6. Share the proposal with the wider team and collect feedback.
   For more information, refer to [Communication](#communication).
7. If the feedback is negative, go back to Step 4.
   If agreement with the wider team cannot be found even after a second or third iteration, consider starting the [Request for Comments (RFC) Process](../../project_governance/rfc_process.md).
8. Start implementation and prepare a first PR.
   Create the PR from a fork rather than making new branches in `github.com/lowRISC/opentitan`.
   Reference the GitHub issue in your PR description and commit messages (see also [Working with Issues](#working-with-issues), [Writing Code](#writing-code)).
   To simplify and speed up code review, we expect larger contributions like new features and major changes to be broken into multiple, smaller PRs wherever possible.
   For more information refer to [Working with PRs](#working-with-pull-requests).

Further information can be found in [Getting Started with a Design](../hw/design.md) and in [Request for Comments (RFC) Process](../../project_governance/rfc_process.md).

# Writing Code

## Licensing

The main license used by OpenTitan is the Apache License, Version 2.0, marked by the following license header in all source files:

    // Copyright lowRISC contributors (OpenTitan project).
    // Licensed under the Apache License, Version 2.0, see LICENSE for details.
    // SPDX-License-Identifier: Apache-2.0

Do not attempt to commit code with a non-Apache license without discussing first.

## Coding style guides, formatting tools

All source code contributions must adhere to project style guides.
We use separate style guides for different languages:
* [SystemVerilog](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md)
* [C/C++](../style_guides/c_cpp_coding_style.md)
* [Python](../style_guides/python_coding_style.md)
* [Markdown](../style_guides/markdown_usage_style.md)
* [Hjson](../style_guides/hjson_usage_style.md)
* [RISC-V Assembly](../style_guides/asm_coding_style.md)

If unsure about the style, be consistent with the existing code and do your best to match its style.

For C/C++ code, we recommend to run "git-clang-format" on your changes.

## What should commit messages look like?

There are many [useful guides](https://chris.beams.io/posts/git-commit/) available on how to write commit messages and why.

The following list contains a set of simple guidelines that we consider most useful.
* A commit message consists of a subject line followed by an optional body.
* Keep the subject line short. Ideally under 50 characters.
* Capitalize the subject line.
* Use the imperative mood in the subject line.
* Use the present tense ("Add feature" not "Added feature").
* When changes are restricted to a specific area, you should add a tag to the start of the subject line in square brackets, e.g. "\[uart/rtl\] Rework Tx FSM". See also [subject tags](#subject-tags).
* Do not end the subject line with a period.
* Separate subject from body with a blank line.
* Wrap the body at 72 characters.
* Use the body to explain what and why (rather than how).

To indicate acceptance of our Contributor License Agreement (CLA), commits should also include a Signed-off-by line (which can be generated by `git commit -s`).
See [CONTRIBUTING.md](https://github.com/lowRISC/opentitan/blob/master/CONTRIBUTING.md) for more information.

## Subject tags

If code changes, issues or pull requests (PRs) are restricted to a specific area, we recommend adding a tag in square brackets, *e.g.*, "\[uart/rtl\]", to the subject line of your commit message, issue or PR.
Such tags help to identify areas affected by changes.
Tags are particularly helpful when dealing with pull requests (PRs) as they can guide team members for code review and simplify later retrieval of specific PRs through the GitHub web interface.

You can add multiple tags separated by a comma, e.g., "\[top, dv\]" to indicate that multiple separated areas are affected.
In addition, you can add further levels of hierarchy to make the indication more precise such as "\[uart/rtl\]" instead of just "\[uart\]", "\[sw/device\]" instead of "\[sw\]".

## What about TODO comments?

We track non-trivial pieces of work via GitHub issues rather than TODO comments in the code.
We do not use TODO(name) comments as used in some code bases - if it is important enough to assign someone, it is worth tracking via an issue.

If you as a code reviewer come across TODOs, you should encourage the author to create a GitHub issue to track the work item, which can be referenced using a comment such as `// TODO(lowrisc/<project_name>#<issue_number>): <brief description>`.
Code authors are encouraged to use TODO rather than FIXME.

## How are auto-generated files treated?

We leverage a set of utilities to automatically generate parts of the source code based on configuration files and templates.
Examples for auto-generated RTL code include the register interface of the peripheral IP cores (using the register tool reggen), the top level (using topgen) and the main TL-UL crossbar (using tlgen).
Auto-generated source files are typically checked into the OpenTitan repository.
This allows people to build the system without having to invoke the utilities.

To prevent people from editing auto-generated top-level files, these files both contain a header marking them as such and they live in subfolders called `autogen/`.
When implementing changes that affect auto-generated files, the configuration or template file must be edited, the auto-generated files need to be regenerated and everything needs to be committed to the repository.

## Vendored Code

Not all source code included in the OpenTitan repository has been
developed as part of the project.
OpenTitan also leverages code from other repositories (e.g. [Ibex](https://github.com/lowrisc/ibex) or code from third parties released under compatible open-source licenses.
The process of incorporating such code into the OpenTitan repository, which besides creating a copy may also involve the application of patches, is managed through the "vendor" script.

The "vendored" code is usually found in a vendor subdirectory such as `hw/vendor`.
It should never be modified directly in the OpenTitan repository.
Instead, modifications should be discussed and implemented upstream and then be vendored into OpenTitan.
However, when dealing with third-party code, please first raise awareness and discuss inside OpenTitan before creating issues and pull requests upstream.

Further information regarding vendor code can be found in the [Vendor Tool User Guide](../hw/vendor.md)


# Working with Pull Requests

## What should a PR look like (single/multiple commits)

A pull request (PR) should contain all the code changes required to address an issue, or all the code changes leading to the implementation of a new feature or a major change in the design.
At the same time, a PR should be as small as possible to simplify and speed up the review process.
It may thus make sense to break down larger contributions into multiple, self-contained PRs.
This does not hold for bug fixes: A single PR is sufficient to fix a bug.

Independent of how a contribution is structured, each individual commit should be atomic.
The code base should remain usable even with only the first commit of a PR, or the first PR of a series of PRs, merged.

Code changes not strictly related to the target feature, major change or issue should go into a separate PR.

In some cases, preparatory code changes may be required before a change is implemented, or a new feature may require changes in a somewhat unrelated part of the code.
For example, it may be the case that the register interface of an IP must be updated using the latest version of the register tool, before a new register required for the targeted feature can be added.
Such changes, if small, can be in the same PR, but they should be in a separate commit with a reasonable commit message explaining why this change is necessary.

PRs with more, smaller commits instead of a few large commits simplifies debugging in the case of regressions.

For more detailed information on how to submit a pull request, see our [GitHub notes](../github_notes.md).

## What are committers?

Committers are the only people in the project that can definitively approve contributions for inclusion.

See the [Committers](../../project_governance/committers.md) definition and role description for a fuller explanation.

## Labeling and assigning PRs

Labels can be useful as they help categorizing, prioritizing and assigning open issues/PRs.
When creating a PR, you are welcome to assign labels if you feel comfortable about selecting suitable labels.
If no labels are assigned, committers and other team members might do that when browsing through the open PR from time to time.
If possible, you should also add a meaningful tag to the subject line of your PR as outlined in [subject tags](#subject-tags).

For PRs, it does not make sense to assign people.
But when creating a PR, you should request a review from committers and team members.
Some reviewers may be assigned by default depending on the paths of changed files.
To balance the review load, you are welcome to also request a review from other people familiar in the corresponding area.
However, you should not request a review from more than 2 to 5 team members, as this increases the review load to unsustainable levels.

## Who should review PRs?

Contributors should request reviews from:
* people regularly working on the affected parts of the code, and
* people involved in discussing the solution of the problem addressed by the PR.

However, review requests are not obligations to perform a review.
It is understood that reviewers may not be able to review every single PR where a review has been requested by them.

## How to give good code reviews?

Code review is not design review and doesn't remove the need for discussing implementation options.
If you would like to make a large-scale change or discuss multiple implementation options, follow the procedure outlined under [How to Contribute Code](#how-to-contributed-code).

The main purpose of code review is to make sure the code changes appropriately solve the problem the PR intends to address.
It is thus vital to provide meaningful commit messages and PR descriptions with references to issues where problems and the proposed solutions are outlined.

Code review is a core part of OpenTitan's focus on high quality implementation.
It helps ensure that:
* The design follows good practices.
* The code matches the style guides.
* The code is appropriately commented.
* Code changes are reflected in the documentation.
* The changes are reasonably structured.
* Meaningful commit messages are provided.

When doing code review, you should check if these guidelines are followed.
If some of the points are not met, or if you see potential improvements in the modified areas, bring this up in a comment.
The author of the PR will then address or comment on all feedback.
It is generally the responsibility of the reviewer who started the discussion to decide whether the feedback has been addressed appropriately.
If the author and the reviewer cannot find agreement, another committer or team member should be brought into the discussion.

When reviewing code and giving/discussing feedback, keep in mind that:
* Code review is not design review.
  If a PR comes without clear motivation or does not follow a course of action previously agreed on, this should be discussed first and separately from the actual code review.
* This is a collaborative, distributed open-source project bringing lots of people together with different motivations and backgrounds.
  Some people work full-time on this project and might see the same mistakes repeatedly while others can only contribute in their spare time.
  This means that many people will see the same issue from different viewpoints.
  Always be friendly and patient and remember to adhere to our [code of conduct](https://www.lowrisc.org/code-of-conduct/).

See also: [reviewing pull requests on GitHub](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/reviewing-proposed-changes-in-a-pull-request) and the [OpenTitan Commit Escalation Guidelines](../../project_governance/committers.md#commit-escalation-guidelines" >}}).

## How to receive a code review?

Code review may be an intimidating process, especially if you're new to the open source community.
Getting lots of comments on even minor style violations can be disheartening.
Know that your contributions are always appreciated - the reality is that in many cases initial code review is the most scrutiny a given piece of code will get.
Therefore, it is worth pushing to ensure it meets all coding standards rather than hoping it will be fixed in the future.

## Do we rebase and merge or squash multiple commits into a single one?

Feedback addressed during the review process should go into the corresponding commit in the PR instead of having a single commit containing all changes addressing the feedback.
Try to keep a clean, linear history.
This means no merge commits and no long series of "fixup" patches.
Instead, use rebase to restructure your work as a series of logically ordered, atomic patches (`git rebase -i` helps).
PRs should not be squashed when merging to keep the individual commits including commit messages making up the PR.

Also see our [GitHub notes](../github_notes.md).


## When to merge a PR after it has been approved?

To reduce the risk of accidentally introducing bugs or breaking existing functionality, we leverage continuous integration (CI) checks on every PR in addition to nightly regression tests.
Depending on the target area of the PR, these automated CI checks can include checking code format and lint rules, checking commit metadata, building and running simulation environments, generating an FPGA bitstream, compilation and execution of smoke tests on an FPGA emulator.
The results of these CI checks can be viewed through the GitHub web interface (check the conversation pane of the PR of interest).

In case the CI checks do not succeed, it is not okay to self-approve the PR or merge it.
PRs addressing CI failures themselves may be exempted from this rule.
However, such PRs are rare and they must always involve senior project committers.

If the CI checks for a PR succeed and if the PR affects larger parts of the code base, it is best to wait 24 hours before merging.
This allows project contributors spread across their many time zones an opportunity to provide feedback.

## Who should merge the PR once it is approved?

If the author of the PR has commit access, they should merge it once it has been reviewed and approved.
Otherwise, a committer will need to merge it.
Normally a committer involved in the review will do this.
Note that irrespective of who merges the PR, the original authorship of the commit is preserved.

## What to do if a PR gets merged and breaks things?

The `master` branch should always be stable.
If a PR is merged that causes breakage that is likely to prevent others from making progress (e.g. breaking simulation or CI infrastructure), this failing PR should be [reverted](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/reverting-a-pull-request) unless the required fix is obvious and trivial.
We see two primary advantages to a quick-revert policy:
* It brings the master branch back into a stable state.
  This means it immediately unblocks other people affected by the problems introduced with the failing PR and allows them to continue their work.
* It removes time pressure for finding the right fix.
  This allows us to track down and fix the root cause of the failure, including getting proper review.
  It also prevents the creation of dirty hotfixes, which are possibly incomplete and lead to other failures requiring follow-up patches themselves.
