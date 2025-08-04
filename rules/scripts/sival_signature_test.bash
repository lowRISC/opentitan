#!/bin/bash

set -o pipefail

FILES_TO_CHECK=(@FILES@)

VERIFY_ARGS=(@VERIFY_ARGS@)
ECDSA_KEY=@ECDSA_KEY@
SPX_KEY=@SPX_KEY@
RESULT_STATUS=0

for file in "${FILES_TO_CHECK[@]}"
do
   if [[ ! -z "$ECDSA_KEY" ]]; then
      echo "Creating dummy manifest..."
      sw/host/opentitantool/opentitantool image manifest update \
        --ecdsa-key="$ECDSA_KEY" \
        --spx-key="$SPX_KEY" \
        --output=/tmp/foo.$$ \
        ${file}

      cmp ${file} /tmp/foo.$$

      if [[ $? -ne 0 ]]; then
        echo "Manifest compare failed for ${file}."
        RESULT_STATUS=1
        exit $RESULT_STATUS
      fi

    fi

  echo "Verifying signature for ${file}..."
  sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} ${file}

  # Check if the verification was successful
  if [[ $? -ne 0 ]]; then
    echo "Signature verification failed for ${file}."
    RESULT_STATUS=1
  fi

  echo "Signature verification completed with status: $RESULT_STATUS"
  exit $RESULT_STATUS
done
