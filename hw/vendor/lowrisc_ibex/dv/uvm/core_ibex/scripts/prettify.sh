#!/bin/bash
_GET_TRACES=$(find . -type f -iregex '.*trace_core.*\.log')
for trace in $_GET_TRACES; do
    column -t -s $'\t' -o ' ' -R 1,2,3,4,5 "$trace" > "$(dirname "$trace")"/trace_pretty.log
done
