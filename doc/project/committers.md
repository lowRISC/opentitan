---
title: "Committers"
---

Committers are individuals with repository write access.
While everyone can and is encouraged to contribute by reviewing code, committers are responsible for final approval and merge.
Committers must ensure that any code merged meets a high quality bar, has been properly discussed, and the design rationale adequately explained and documented.
Making a judgement on when these requirements have been met is fundamental to the role.

Committers are proposed by and voted on by the TC.
Committers should:
* Be active contributors to the project, with a history of high quality contributions, including code reviews.
* Be familiar with the project processes and rules, and be able to apply them fairly.
* Be responsive to feedback from TC members on their review approach and interpretation of project policy.
* Work to ensure that stakeholders are properly consulted on any code or design changes.

If you meet the above criteria and are interested in becoming a committer, then approach a TC member to see if they would be willing to propose you.
TC members may also reach out to you to ask if you would be interested in becoming a committer.

Under certain exceptional circumstances, the Steering Committee may vote to revoke a committer's status.
This may happen in cases such as a committer failing to act as a good citizen within the project and the issue cannot be resolved through discussion.
It may also be a natural function of "pruning the tree" as an individual's involvement in the project changes over time.

The list of committers is maintained within the project's Git repository and is available in the [COMMITTERS file](https://github.com/lowRISC/opentitan/blob/master/COMMITTERS) in the repository root.

## Commit Escalation Guidelines

When reviewing a pull request, there are a range of options in giving feedback.
Although committers have the final say on patch approval or requiring changes, the task of reviewing is shared by all contributors, who may make similar requests.
Options for reviewing a pull request include:
* Approval, with no further conditions.
  * This is appropriate when you are confident the changes are correct, sufficiently explained, in line with the project coding styles, and don't need further review by others or a companion [RFC]({{< relref "rfc_process" >}}) to be written.
    You should only use this for cases where you have sufficient expertise in the areas being modified.
  * Note that if the PR came from someone without commit rights, you will need to rebase and merge for them.
* Approval, but with a request to get an additional approval from other named reviewers.
  * This is appropriate when you believe the changes are correct, but would either like a second opinion or to ensure that another contributor is aware of and approves of the changes.
* Request for changes.
  * This is appropriate when problems or potential improvements are spotted that can be addressed by the original submitter updating the pull request.
* Request that further design rationale be written up and shared (but a full [RFC]({{< relref "rfc_process" >}}) isn't necessary).
  * This is appropriate when the rationale for a change is not clear, or a lack of accompanying documentation makes reviewing the code challenging.
    This can commonly occur when further explanation would be valuable for people working in that area but no project-wide consensus is needed.
* Request that an RFC be written up and submitted.
  * This is appropriate when adding a major new piece of code (e.g. an IP block) or when a change is cross-cutting and likely to require input from many stakeholders.
    The expectation is that in many cases, project contributors will recognize when an RFC is needed before getting to the point of submitting a pull request.

In all cases, clarity in your feedback will be valued.
For instance, if you are giving code style feedback but not reviewing higher level design decisions (perhaps because you are expecting another committer/contributor to do so), it is useful to say so.

Where Committers disagree on the path forwards for a given PR and are unable to reach an agreement, the review moves to the TC.
