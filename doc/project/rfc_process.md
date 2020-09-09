---
title: OpenTitan RFC Process
---

## Introduction

The OpenTitan RFC process is the mechanism by which technical proposals can be reviewed and voted upon by the Technical Committee (TC).
More generally, the RFC process ensures changes are appropriately reviewed, gives the contributor community opportunity to give feedback, and helps ensure alternative implementation options are also evaluated.
Many other open source projects implement such a process with varying degrees of formality, e.g. Python Enhancement Proposals, RFCs in the LLVM community, and more.

RFCs can't be used for resource allocation or to "force" other people to do some work.
E.g. "Implement IP block X" is not a useful RFC unless either the proposer is willing to do that work or someone else is interested in pursuing it.

This document outlines the basic structure of the RFC process, with the expectation that it will evolve over time based on the experience of active contributors.

## RFC lifetime

* [Optional: Seek feedback on whether an RFC is desired.
  This is recommended for a lengthy "out of the blue" proposal, to ensure time isn't wasted writing up a detailed proposal for something that is out of scope or that can't be decided upon at this stage.]
* An author (or set of authors) writes an RFC.
  This might be triggered simply by an idea, by a discussion in a meeting, or by a request from a Committer after submitting a PR.
  The TC will maintain examples of high quality RFCs to refer to in terms of structure and approach.
* The RFC authors may solicit early feedback while preparing an RFC, possibly before sharing publicly.
   * If requested, the TC could help to nominate a small group to shepherd the RFC.
* If the RFC potentially contains information that could be certification-sensitive (guidance to be shared), send a note to security@opentitan.org first for feedback.
* The RFC is shared publicly by filing a GitHub issue and tagging with the `RFC:Proposal` label.
* Once the author is happy that the RFC is complete, they submit it to the Technical Committee by converting the label to `RFC:TC Review`.
* The Technical Committee will consider active RFCs in each meeting (those that have been marked with `RFC:TC Review` for at least a week).
  If an RFC saw large changes in the week it has been "ready" the TC may postpone judgement in order to allow more comment.
  They will decide whether to:
   * **Accept**: Indicate they are happy for this proposal to be implemented.
     May be conditional on certain changes.
     The TC will change the label from `RFC:TC Review` to `RFC:Approved` in this outcome.
   * **Reject**: Decided against the proposal at this time.
     The label `RFC:TC Review` will be removed by the TC.
   * **Postpone**: The proposal seemed to have the right level of detail and form, but the project won't be making a decision on it at this time (e.g. refers to work that is scheduled too far in the future).
     The TC will revert the label from `RFC:TC Review` back to `RFC:Proposal`.
     In the case where the TC has not had sufficient time to complete review during a meeting, the label `RFC:TC Review` will remain in place until the review has completed.
   * **Request revision**: The TC feel they could make an accept/reject decision if certain changes were made (e.g. fleshing out a description of alternate approaches, considering changes to the approach etc).
     The TC will revert the label from `RFC:TC Review` back to `RFC:Proposal` until revisions have been completed.
   * **Abstain with comment**: The TC feel that the issue does not require TC arbitration.
     The TC may leave comment suggesting the next action for the RFC, perhaps indicating where the issue should be resolved, such as in one of the other committees.
     The TC will remove the `RFC:TC Review` label in this case.

RFCs should be created at least for any major new piece of code (e.g. IP block), or cross-cutting changes that need careful consideration.
Generally speaking, an RFC should be created when there is demand for one (especially when that request comes from a Committer).
Although it is a power that is not expected to be deployed regularly, RFCs may be unilaterally approved/rejected by the Project Director.
Even in these cases, they would likely still follow the normal review and feedback process.

## Potential future RFC process refinements

The process has been kept as simple as possible to start with, closely mimicking the informal consensus approach being used in the early stages of the OpenTitan project.
However, there are a range of potential improvements that it may make sense for the Technical Committee and wider contributor community to explore:

* We currently have no particular rule on RFC format and structure.
  It may be useful to at least suggest a structure for certain categories of changes (e.g. outline of headings).
* [Rust RFCs](https://rust-lang.github.io/rfcs/) and the [Kotlin Evolution and Enhancement Process](https://github.com/Kotlin/KEEP) both introduce the idea of a "Shepherd", which we may want to adopt.
* If the volume of RFCs increased to the point it was too time consuming for the Technical Committee to handle each review request, the TC may delegate some responsibility for pre-filtering.
  E.g. the Chair/Vice-Chair may make a determination on whether an RFC has attracted sufficient support for further discussion.
