#!/bin/bash

set -o pipefail

FILES_TO_CHECK=(@FILES@)

IS_NEGATIVE_TEST=@IS_NEGATIVE_TEST@
VERIFY_ARGS=(@VERIFY_ARGS@)
ECDSA_KEY=@ECDSA_KEY@
SPX_KEY=@SPX_KEY@
RESULT_STATUS=0

echo "___Starting signature verification & manifest key verification___"

for file in "${FILES_TO_CHECK[@]}"
do

  # TEST 1: Signature verification
  echo "Checking signature..."
  if [[ "$IS_NEGATIVE_TEST" == "True" ]]; then
    sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} ${file}

    # If negative test, check if successful
    if [[ $? -eq 0 ]]; then
      echo "Negative test failed."
      RESULT_STATUS=1
    else
      echo "Negative test succeeded."
    fi
  else
    # Else, check if the verification was successful
    sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} ${file}
    if [[ $? -ne 0 ]]; then
      echo "Signature verification failed."
      RESULT_STATUS=1
    else
      echo "Signature verification succeeded."
    fi
   fi

  # TEST 2: ECDSA key and/or SPX key integrity and signature verification
   if [[ ! -z "$ECDSA_KEY" ]]; then
      echo "Creating dummy manifest to verify manifest key integrity..."
      # If SPX key is provided, include it in the manifest update
      if [[ ! -z "$SPX_KEY" ]]; then
        sw/host/opentitantool/opentitantool image manifest update \
          --ecdsa-key="$ECDSA_KEY" \
          --spx-key="$SPX_KEY" \
          --output=/tmp/manifest_test_key_verify.$$ \
          ${file}
        echo "Successfully created manifest with ECDSA and SPX keys."
      # Else, create manifest with only ECDSA key
      else
        sw/host/opentitantool/opentitantool image manifest update \
          --ecdsa-key="$ECDSA_KEY" \
          --output=/tmp/manifest_test_key_verify.$$ \
          ${file}
        echo "Successfully created manifest with ECDSA."
      fi
      # Perform manifest comparison
      echo "Comparing dummy manifest with original file..."
      cmp ${file} /tmp/manifest_test_key_verify.$$

    # Check if the comparison was successful
      if [[ $? -ne 0 ]]; then
        echo "Manifest compare failed."
        RESULT_STATUS=1
      else
        echo "Manifest compare succeeded."
      fi

  fi

  sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} ${file}

done

echo "Status: $RESULT_STATUS"

exit $RESULT_STATUS
