#!/bin/bash

printf "\n\nCompare to reference files ... \n\n";
FAIL=0
RUN=0

for ref in ${SUITEDIR}/references/*.reference_output;
do 
    base=$(basename ${ref})
    stub=${base//".reference_output"/}
    sig=${WORK}/${RISCV_ISA}/${stub}.signature.output

    RUN=$((${RUN} + 1))
    
    #
    # Ensure both files exist
    #
    if [ -f ${ref} ] && [ -f ${sig} ]; then 
        echo -n "Check $(printf %16s ${stub})"
    else
        echo    "Check $(printf %16s ${stub}) ... IGNORE"
        continue
    fi
    diff --ignore-case --strip-trailing-cr ${ref} ${sig} #&> /dev/null
    if [ $? == 0 ]
    then
        echo " ... OK"
    else
        echo " ... FAIL"
        FAIL=$((${FAIL} + 1))
    fi
done

# warn on missing reverse reference
for sig in ${WORK}/${RISCV_ISA}/*.signature.output; 
do
    base=$(basename ${sig})
    stub=${base//".signature.output"/}
    ref=${SUITEDIR}/references/${stub}.reference_output

    if [ -f $sig ] && [ ! -f ${ref} ]; then
        echo "Error: sig ${sig} no corresponding ${ref}"
        FAIL=$((${FAIL} + 1))
    fi
done

declare -i status=0
if [ ${FAIL} == 0 ]
then
    echo "--------------------------------"
    echo "OK: ${RUN}/${RUN}"
    status=0
else
    echo "--------------------------------"
    echo "FAIL: ${FAIL}/${RUN}"
    status=1
fi
exit ${status}
