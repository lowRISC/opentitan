#!/bin/bash

set -o pipefail

FILES_TO_CHECK=(@FILES@)

VERIFY_ARGS=(@VERIFY_ARGS@)
ECDSA_KEY=@ECDSA_KEY@
SPX_KEY=@SPX_KEY@
RESULT_STATUS=0

echo "___Starting signature verification & manifest key verification___"

for file in "${FILES_TO_CHECK[@]}"
do
   if [[ ! -z "$ECDSA_KEY" ]]; then
      echo "Creating dummy manifest to verify manifest key integrity..."

      if [[ ! -z "$SPX_KEY" ]]; then
        sw/host/opentitantool/opentitantool image manifest update \
          --ecdsa-key="$ECDSA_KEY" \
          --spx-key="$SPX_KEY" \
          --output=/tmp/manifest_test_key_verify.$$ \
          ${file}
      echo "Successfully created manifest with ECDSA and SPX keys."
      else
        sw/host/opentitantool/opentitantool image manifest update \
          --ecdsa-key="$ECDSA_KEY" \
          --output=/tmp/manifest_test_key_verify.$$ \
          ${file}
         echo "Successfully created manifest with ECDSA."
      fi

      echo "Comparing dummy manifest with original file..."
      cmp ${file} /tmp/manifest_test_key_verify.$$

      if [[ $? -ne 0 ]]; then
        echo "Manifest compare failed."
        RESULT_STATUS=1
      else
        echo "Manifest compare succeeded."
      fi

    fi

  echo "Verifying signature for FILE= ${file}..."
  sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} ${file}

  # Check if the verification was successful
  if [[ $? -ne 0 ]]; then
    echo "signature failed."
    RESULT_STATUS=1
  else
    echo "signature succeeded."
  fi

  echo "Running negative test case by modifying the file..."

  xxd ${file} > /tmp/negative_key_verify_$$.hex

  sed -E '1s/^(........: )../\149/' /tmp/negative_key_verify_$$.hex > /tmp/negative_key_verify_$$.modified.hex

  xxd -r /tmp/negative_key_verify_$$.modified.hex > /tmp/negative_key_verify_$$.modified.bin

  sw/host/opentitantool/opentitantool image manifest verify ${VERIFY_ARGS} /tmp/negative_key_verify_$$.modified.bin

  if [[ $? -eq 0 ]]; then
    echo "Negative test failed."
    RESULT_STATUS=1
  else
    echo "Negative test succeeded."
  fi

  echo "Status: $RESULT_STATUS"
done

exit $RESULT_STATUS
