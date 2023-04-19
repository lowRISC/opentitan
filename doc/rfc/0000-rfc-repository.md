# RFC 0000 - RFC repository

- Date proposed: 2023-02-28
- Date approved: under review

## Summary

This RFC proposes storing OpenTitan RFCs as files in a Git repo, and using
an open source development workflow for the RFC process. RFCs would be
stored in the RFC repo as text files. They would be proposed, reviewed, and
accepted/rejected using GitHub pull requests (PRs). The goal is to ensure
project decisions are better documented, and to make the RFC process more
visible and transparent. The workflow proposed here will already be familiar to
open source contributors and should add little overhead.

## Motivation

RFCs in OpenTitan are used for decisions that need consensus from the technical
committee. The RFC workflow before this proposal is roughly:

1. Write up your RFC somewhere.
2. Create an issue labelled `RFC:Proposal` linking to your RFC in the main repo.
3. Receive and address comments from others.
4. Apply the `RFC:TC review` label when the RFC is ready to be voted on.
5. The technical committee will vote on pending RFCs at their next meeting.
5. Approved RFCs have their label changed to `RFC:Approved`.
6. Rejected RFCs have their label removed.

Typically, authors write their RFCs in one of two places:

* Google Docs.
* The GitHub issue's body as Markdown.

The entry-point for finding RFCs stored like this is through the `RFC:Approved`
label in GitHub issues. The OpenTitan repository gets many issues and has many
labels to sort them. Discovering RFCs requires regularly checking the `RFC`
labels or keeping up to date with OpenTitan's fast moving issues.

Allowing authors to choose where they store their RFC content makes it
harder to reference them as documentation. It also means we can't manage them
consistently: we have no public-by-default rule for Google Docs, leading to
many RFCs restricted only to select people. Comments are left in both GitHub
issue comments and Google Docs reviews.

In summary, the motivation of this RFC is to have a single store of RFC
documents, where:

1. RFCs can easily be discovered,
2. RFC content can be enforced to be public,
3. RFC comments are given and addressed in a consistent workflow.

## Explanation

RFCs can be very important documentation artefacts. They show exactly what
decisions have been made and the factors used to come to those decisions. As an
open source project, we're able to make this process and the documentation
artefacts more open. This RFC proposes applying our open source development
model to the RFC process.

We would do this by having RFCs:

* Written as Markdown text documents.
* Stored and tracked in a Git repo.
* Proposed through GitHub PRs.
* Reviewed and accepted/rejected through GitHub reviews.

The workflow for proposing and reviewing would then be the same as contributing
code or documentation to OpenTitan.

### RFC file structure

Having RFCs as files brings them closer to our other kinds of documentation. To
make best use of RFCs as documentation, this RFC also proposes adding some
structure to RFCs:

* RFCs are dated (and authored if necessary).
* RFCs are based on some template file to help the author fully consider all
  aspects of their proposal.
* RFCs are assigned numeric IDs when accepted.
* RFC numbers will start at 0001 and increase monotonically with date
  accepted without gaps.

Having RFCs as plain documentation lets us reference them when, for example:

* Justifying the need for an issue or PR in OpenTitan.
* Explaining why something was designed as it was in documentation.
* Pointing to similar or conflicting RFCs for new proposals or ideas.

### Historic RFCs

Historic RFCs accepted before this proposal should be converted to Markdown and
included in the RFC repository for consistency. This should happen before
further RFCs are added to preserve the ordering by date.

### Tracking RFC implementation progress

When an RFC is accepted, a link to a "tracking issue" should be added to the
front-matter of the RFC document alongside the date it was accepted. This
tracking issue should be a GitHub issue in the OpenTitan repo where the RFC will
need to be implemented.

This RFC proposes no format for these tracking issues, but they should:

* Show the progress of the RFC's implementation.
* Track any issues or updates encountered since the RFC was accepted.
* Track follow-up RFCs that may need to be proposed to continue any unresolved
  or future work from the RFC.

## Drawbacks

* Some RFCs may have private motivations which cannot be submitted to a public
  repo.
* Some RFC comments may need to reference private use-cases which cannot be
  included in a public review.
* RFC comments are still locked into GitHub's system, so those are not portable.

## Rationale and alternatives

This workflow was chosen to reflect how we already contribute code and
documentation to OpenTitan in an open source way. There should be almost no
overhead to existing open source contributors who want to contribute RFCs.

The choice to store RFCs as text files allows them to be used as any other
documentation. Matching the RFC process to how we already contribute code and
documentation makes the process more accessible. Text files can be written to
and read by anybody, including people outside the opentitan.org domain.

Making the existance of private RFCs known in the public repo prevents confusion
from those without access. They are included in a redacted form to provide at
least some context on what they relate to and why they are private. They are
assigned RFC numbers so that they can be included proper if they can be made
public in the future.

### Alternative: Google Docs

We could instead go all-in on Google Docs and keep RFC documents in one
shared folder. They would be discoverable here, but unlike any of our existing
documentation. The RFC content would be stored in the Google Docs format and
would need converting to be moved or read elsewhere.

### Alternative: GitHub issues

We could instead require that all RFC text is stored in the GitHub issues
themselves. GitHub issues can only be read through the GitHub interface, though
the content is in Markdown format and could be copied elsewhere. They would
still only be discoverable through the RFC labels in GitHub issues. Comments on
GitHub issues do not have the same reviewing features that pull request comments
do.

### Alternative: RFCs as documentation files in the monorepo

We could instead store our RFCs as documentation files mixed into the monorepo's
OpenTitan documentation. This would give us the documentation benefits, but RFC
PRs would get lost amongst the faster moving development PRs. We would also lose
a seperation of concerns, though as we use a monorepo already, the boundary of
what should be included together may be large enough to include RFCs.

## Prior Art

* The Rust project has an RFC repo: <https://github.com/rust-lang/rfcs>.

    * They use the template, PR, review, accept/reject workflow.
    * In place of a technical committee, the relevant team will vote in the PR.
    * Accepted RFCs prompt a "tracking issue" to track its implementation.
    * RFC markdown files are rendered into [a book][rfc-book] for easy browsing.

* The Internet has almost 10,000 RFCs as files:

    * These predate Git or modern open source workflows, and are made
      discoverable through HTML indexes.
    * The original [documentation conventions][rfc3] RFC highlights the
      importance of open decision making.

As a meta point, this RFC was written using a modified version of Rust's RFC
template. I found the headings used made for good prompts to ensure more sides
of the proposal were considered.

## Future possibilities

We could present the Markdown RFC documents in a nice book like we do with other
documentation. The [Rust RFC book][rfc-book] makes for a good example.

[rfc-book]: https://rust-lang.github.io/rfcs/
[rfc3]: https://www.rfc-editor.org/rfc/rfc3
