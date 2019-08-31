# Contributing code to the opentitan repository

## Quick guidelines

* Keep a clean commit history. This means no merge commits, and no long series
  of "fixup" patches (rebase or squash as appropriate). Structure work as a
  series of logically ordered, atomic patches. `git rebase -i` is your friend.
* Changes should be made via pull request, with review. Do not commit until
  you've had an explicit "looks good to me". We don't yet have, but plan to
  create a policy describing code owners and the like. In the meantime use your
  best judgement. If you're submitting a change against something that was 90%
  authored by a single person, you'll want to get their ACK before committing.
* When changes are restricted to a specific area, you are recommended to add a
  tag to the beginning of the first line of the commit message in square
  brackets. e.g. "[UART] Fix bug #157".
* Code review is not design review and doesn't remove the need for discussing
  implementation options. If you would like to make a large-scale change or
  discuss multiple implementation options, discuss on the mailing list.
* Create pull requests from a fork rather than making new branches in 
  `github.com/lowrisc/opentitan`.
* Do not force push.
* Do not attempt to commit code with a non-Apache license without discussing
  first.
* If a relevant bug or tracking issue exists, reference it in the pull request
  and commits.
