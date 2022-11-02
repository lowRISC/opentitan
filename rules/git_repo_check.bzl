# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This should be run at the end of WORKSPACE definition to check that there aren't any git_repository or new_git_repository rules
def git_repo_check():
  for repos in native.existing_rules().values():
    if "git_repository" in repos["kind"]:
      fail(
"""OpenTitan's security model and airgapping strategy requires use of only http_archives.
Rule '{}' contains a '{}'
Details: {}""".format(repos["name"],repos["kind"],repos)
      )
