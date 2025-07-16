#!/bin/bash

set -euo pipefail

FILES_TO_CHECK=(@FILES@)

VERIFY_ARGS=(@VERIFY_ARGS@)

for file in "${FILES_TO_CHECK[@]}"
do
  @OPENTITANTOOL@ image manifest verify ${file} ${VERIFY_ARGS}
done
