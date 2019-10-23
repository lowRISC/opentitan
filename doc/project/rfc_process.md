# RFC (Request For Comments) process and committers

## Intro/background

Unlike many other open-source projects, OpenTitan has a very clear top-level roadmap that is motivated by adopter/customer requirements.
The structure must allow that roadmap to be developed and circulated in a more traditional top-down fashion, while also being open to contributions (when appropriate) and proposals to be made in a more bottom-up fashion.
E.g. new RFC proposals from individual contributors or the open source community at large (although part of the evaluation will be whether they are appropriately aligned to OpenTitan goals and roadmap).

The intent here is to describe a general framework that can evolve over time and indeed be flexible to different approaches for different types of proposal.
This is intended to be complimentary with the
[Getting Started with a Design](../ug/getting_started_design.md)
document which aims to give guidance for HW designers looking to get started in the project with a new design.

## Committers

Committers are the first line of defence for the project - ensuring that any code merged is of sufficient quality and has been subject to sufficient discussion and design rationale.
Although being a committer is a trusted position, we shouldn't artificially limit this set.
Empowering active and proven contributors will free the Technical Committee (TC) from micro-managing the community and is also motivating for individual contributors.
As a rule of thumb, anyone contributing full time to the project are likely to be granted committer rights within the first few months (unless open source development and responsibilities are completely new to them).



*   Everyone has the ability to give code reviews on the project and is encouraged to do so.
    However, only committers can definitively approve something for inclusion.
*   When reviewing a pull request, committers have a range of possible options.
    Committers are entrusted to use their judgement along with guidelines set by the TC to recommend the best path:
    *   Approval, good to merge without an RFC or similar.
        Committers should only use this for areas where they have sufficient expertise or where the patch is trivial.
    *   Approval, but please get an additional LGTM from other named reviewers
    *   Request for changes
    *   Request for further design rationale be written up and shared (much more informal than the RFC process)
    *   Request that an RFC be written up and submitted
*   Where Committers disagree on the path forwards for a given PR, and are unable to reach an agreement, it will be discussed further at the TC.
*   Committers are proposed by and voted on by the TC. Committers must:
    *   Be active contributors to the project, with a history of high quality contributions (including code reviews)
    *   Be familiar with the project processes and rules, and apply them fairly
    *   Be responsive to feedback from TC members on their review approach and interpretation of project policy
    *   Work to ensure that interested parties are properly consulted on any code or design changes.
*   The list of Committers will be maintained by the TC and be publicly visible (documented in the repo, alongside documentation of what it means)
*   Every TC member is a committer


### Potential future Committers refinements

*   This proposal doesn't describe realms of responsibility for Committers and relies on Committers making good judgement.
    It has been found to work well in the LLVM project and other open source projects.


## RFC process

Many projects have found it useful to institute a process for proposed changes to be written up, reviewed, and accepted/rejected.
As well as ensuring changes are appropriately reviewed and the impacts considered by key stakeholders, such a process can also help ensure that alternative implementation options are also adequately evaluated.
Examples of such a process can be seen in the Python Enhancement Proposal, RFCs in the LLVM community (which are much more informal than the previous examples), and many others.

Fundamentally, RFCs are the mechanism by which technical proposals can be reviewed and voted upon by the TC.
RFCs can't be used for resource allocation or to "force" other people to do some work.
E.g. "Implement IP block X" is not a useful RFC unless either the proposer is willing to do that work or someone else is interested in pursuing it.

This proposal outlines the basic structure of the RFC process, with the expectation that it will evolve in time based on the experience of active contributors.

The lifetime of an RFC is that:



*   [Optional: Seek feedback on whether an RFC is desired.
    This is recommended for an "out of the blue" proposal, to ensure time isn't wasted writing up a detailed proposal for something that is out of scope or that can't be decided upon at this stage].
*   An author (or set of authors) writes an RFC.
    This might be triggered simply by an idea, by a discussion in a meeting, or by a request from a Committer after submitting a PR.
    The TC will maintain examples of high quality RFCs to refer to in terms of structure and approach.
*   The RFC authors may solicit early feedback while preparing an RFC, possibly before sharing publicly.
    *   If requested, the TC could help nominate a small group to shepherd the RFC.
        This isn't formalized
*   If the RFC may contain certification sensitive material (guidance to be shared), it should be first sent to [cert-sensitive-priv@lowrisc.org](mailto:cert-sensitive-priv@lowrisc.org) for clearance before sharing more widely.
*   The RFC is shared publicly.
    *   Proposal: File GitHub issue, tag with `Type:RFC`
        *   Alternative: mail opentitan-tech@ with RFC
        *   Alternative: create a spec RFC repo
*   Once the author is happy that the RFC is complete, they submit it to the technical committee for review.
    *   Proposal: Marked as ready by applying a certain tag to the issue.
        RFC Status: For-review
*   The TC will consider active RFCs in each meeting (those that have been marked ready for at least a week).
    If an RFC saw large changes in the week it has been "ready" the TC may postpone judgement in order to allow more comment.
    They will decide whether to:
    *   Accept: Happy for this proposal to be implemented.
        May be conditional on certain changes.
    *   Reject: Decided against the proposal at this time
    *   Postpone: Proposal seemed to have the right level of detail and form, but the project won't be making a decision on it at this time (e.g. refers to work that is too far in the future).
    *   Request revision: The TC feel they could make an accept/reject decision if certain changes were made (e.g. fleshing out a description of alternate approaches, considering changes to the approach etc).

RFCs should be created at least for any major new piece of code (e.g. IP block), or cross-cutting changes that need careful consideration.
Although it is a power that is not expected to be deployed regularly, RFCs may be unilaterally approved/rejected by the Project Director.
Even in these cass, they would likely allow the normal review and feedback process.

Things to do to implement this process:

*   Make decision on where RFCs should live and how "submission" to the TC should work
    *   Current proposal is to use issues, and a label on the issue.
*   Modify contribution guidance to give advice on cases where RFCs are likely to be required


### Potential future RFC process refinements

We would explicitly like to keep the process simple to start with, and keep it well aligned to the process we have already been following.
However, there are a range of potential improvements that it may make sense for the TC to explore:


*   We currently have no particular rule on RFC format and structure.
    It may be useful to at least suggest a structure for certain categories of changes (e.g. outline of headings).
*   Rust RFCs and the Kotlin Evolution and Enhancement Process both introduce the idea of a "Shepherd", which we may want to adopt.
*   Current development velocity sees a maximum 1-2 RFC equivalents per week.
    If the volume increased to a point that it was too time consuming for the TC, the TC may delegate some responsibility for pre-filtering.
    E.g. the Chair/Vice-Chair may make a determination on whether an RFC has attracted sufficient support for further discussion.
