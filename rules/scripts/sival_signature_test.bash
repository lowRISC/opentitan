#!/bin/bash

set -euo pipefail

FILES_TO_CHECK=(@FILES@)

for file in "${FILES_TO_CHECK[@]}"
do
  @OPENTITANTOOL@ image manifest verify ${file}
done
