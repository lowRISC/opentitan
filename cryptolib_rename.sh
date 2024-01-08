#! /usr/bin/bash

set -e;

USAGE="$0 <mode> <previous name> <new name>"

if [[ $1 == "" ]] | [[ $2 == "" ]] | [[ $3 == "" ]]
then
  echo $USAGE;
  exit 1;
fi

if [[ $REPO_TOP == "" ]]
then
  echo "\$REPO_TOP is not defined.";
  exit 1;
fi

MODE=$1
OLD_NAME=$2
NEW_NAME=$3
REPO_TOP=$(realpath $REPO_TOP)
SW_DIR="$REPO_TOP/sw"
OLD_NAME_T=$OLD_NAME
OLD_NAME_T+="_t"
NEW_NAME_T=$NEW_NAME
NEW_NAME_T+="_t"

echo "Renaming $OLD_NAME to $NEW_NAME...";

# Replace occurrences of the name in certain forms in certain directories. The
# tricky part here is not mangling similarly named references by e.g. replacing
# a substring within their name, which is why we use whole-word matches only
# and target directories where the cryptolib is in scope.
for DIR in "$REPO_TOP/sw/device/lib/crypto" "$REPO_TOP/sw/device/tests/crypto" "$REPO_TOP/sw/device/silicon_creator/manuf/lib" "$REPO_TOP/sw/device/sca" "$REPO_TOP/doc/security/cryptolib"
do
  # For enums and structs, replace whole-word occurrences of the name suffixed
  # with _t and occurrences of the mode followed by the name and then a space
  # (e.g. "enum foo "). For functions or constants, replace whole-word
  # occurrences of the name.
  case $MODE in
    enum | struct) git ls-files $DIR | xargs sed -i -E "s/(\b)$OLD_NAME_T(\b)/\1$NEW_NAME_T\2/g" && git ls-files $DIR | xargs sed -i -E "s/$MODE $OLD_NAME /$MODE $NEW_NAME/g";; 
    func | constant) git ls-files $DIR | xargs sed -i -E "s/(\b)$OLD_NAME(\b)/\1$NEW_NAME\2/g";;
    *) echo "Invalid mode: $MODE. Must be one of: enum, struct, func, constant";;
  esac 
done

# Print any remaining occurrences from the software directory.
if grep -Ir -e "\b$OLD_NAME\b" -e "\b$OLD_NAME_T\b" $SW_DIR
then
  # grep exited with 0, meaning it found matches.
  echo "WARNING: Some occurrences of $OLD_NAME remain in $SW_DIR.";
fi
