# RFC 0000 - RFC repository

- Date proposed: 2023-02-28
- Date approved: under review

## Summary

This RFC proposes storing OpenTitan RFCs as files in a Git repo, and using
an open source development workflow for the RFC process. RFCs would be
stored in the RFC repo as text files. RFCs would be proposed, reviewed, and
accepted/rejected using GitHub pull requests (PRs). The goal is to ensure
project decisions are better documented, and to make the RFC process more
visible and transparent. The workflow proposed here will already be familiar to
open source contributors and should add little overhead.

## Motivation

RFCs in OpenTitan are used for decisions that need consensus from the technical
committee. A summary of the RFC process as documented [here][rfc-process]:

1. Write up your RFC somewhere.
2. Create an issue in the OpenTitan repo with a link to your RFC.
3. Label the issue with `RFC:Proposal`, then `RFC:TC review` when ready.
4. Pending RFCs will be discussed in the next technical committee meeting.
5. Approved RFCs have their label changed to `RFC:Approved`.
6. Rejected RFCs have their label removed.

Typically, authors write their RFCs in one of two places:

* A Google Doc, accessible only to select people.
* The GitHub issue itself as Markdown.

RFCs stored like this are not discoverable and not portable. In the case
of Google Docs, they are not accessible to everybody, even within the
opentitan.org domain. RFCs are reviewed in private by the technical committee
and project director.

This makes it difficult (or impossible) for contributors to find documentation
of what decisions have been made and why. Adopting more open processes for
project governance will help the OpenTitan project be an exemplary case for
open hardware development.

## Explanation

RFCs can be very important documentation artefacts. They show exactly what
decisions have been made and the factors used to come to those decisions. As an
open source project, we can make this process and the aftefacts more open. This
RFC proposes applying our open source development model to the RFC process.

We would do this by having RFCs:

* Written as Markdown text documents.
* Stored and tracked in a Git repo.
* Proposed through GitHub PRs.
* Reviewed and accepted/rejected through GitHub.

The workflow for proposing and reviewing would then be the same as contributing
any code or documentation to OpenTitan.

### RFC file structure

Having a repo of RFCs like this brings them closer to any other kind of
documentation. To make best use of RFCs as documentation, this RFC also
proposes adding some structure to RFCs:

* RFCs are dated (and authored if necessary).
* RFCs are based on some template file to help the author fully consider all
  aspects of their proposal.
* RFCs are assigned numeric IDs when accepted.
* RFC numbers should start at 0001 and increase monotonically with date
  accepted.
* There should be no gaps in RFC numbers.

Having RFCs as plain documentation lets us reference them when, for example:

* Justifying the need for an issue or PR in OpenTitan.
* Explaining why something was designed as it was in documentation.
* Pointing to similar or conflicting RFCs to new proposals.

### Private RFCs

How and where private RFCs are stored is out of scope for this RFC, except to
say that any redacted form of a private RFC that can be included must be. At the
very least, private RFCs are still assigned the next RFC number when accepted.

## Drawbacks

* Some RFCs have private reasoning which cannot be submitted to a public repo.
* RFC comments are still locked into GitHub's system, so are not portable.

## Rationale and alternatives

This workflow was chosen to reflect how we already contribute code and
documentation to OpenTitan in an open source way. There should be almost no
overhead to existing open source contributors who want to contribute RFCs.

The choice to store RFCs as text files allows them to be used as any other
documentation. Matching the RFC process to how we already contribute code and
documentation makes the process more accessible. Text files can be written to
and read by anybody, including people outside the opentitan.org domain.

Opening up the RFC process makes our project governance more transparent and
brings us closer inline with other open source projects. It shows that we don't
gatekeep the project to corporate contributors or other insiders.

Making the existance of private RFCs known in the public repo prevents confusion
from those without access. They are included in a redacted form to provide at
least some context on what they relate to and why they are private. They are
assigned RFC numbers so that they can be included proper if they can be made
public in the future.

### Alternative: Google Docs

We could instead go all-in on Google Docs and keep RFC documents in one shared
folder. They would be somewhat discoverable, but unlike any of our existing
documentation. This would also keep them locked into a proprietary platform and
inaccessible to contributors outside opentitan.org.

### Alternative: GitHub issues

We could instead require that all RFC text is stored in the GitHub issues
themselves. This would make them accessible to everybody, but less discoverable
and harder to use as documentation. Issues can be commented on, but not reviewed
like pull requests can be.

### Alternative: RFCs as documentation files in the monorepo

We could instead store our RFCs as documentation files mixed into the monorepo's
OpenTitan documentation. This would give us the documentation benefits, but RFC
PRs would get lost amongst the faster moving development PRs. We would also lose
a seperation of concerns, though we've already lost that for regular development
by using a monorepo there.

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
template. I think the headings used here make for good prompts to ensure all
aspects of a decision are considered.

## Unresolved questions

* Should historic RFCs be brought into the repo?
* How do we keep track of the progress of an RFC's implementation?
* Where do we store the full content of private RFCs?
* Can we have a seperate repository, or do we use a directory in the monorepo?

## Future possibilities

We could present the Markdown RFC documents in a nice book like we do with other
documentation. The [Rust RFC book][rfc-book] makes for a good example.

[rfc-process]: https://staging.opentitan.org/book/doc/project_governance/rfc_process.html
[rfc-book]: https://rust-lang.github.io/rfcs/
[rfc3]: https://www.rfc-editor.org/rfc/rfc3
