#!/usr/bin/bash
# Remove leading "# " from the transcript file creation
# https://support.sw.siemens.com/en-US/knowledge-base/MG579948?pid=sc%3Asr-open&index=content-external&audience=external
# This provides compatibility for log file error checking with other supported simulators within Opentitan
vsim -do "set PrefMain(LinePrefix) """
rm transcript
