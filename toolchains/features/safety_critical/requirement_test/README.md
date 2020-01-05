# Requirements test
This directory contains a set of targets intended to test the static analyser against the rules defined in the [JSF++](http://www.stroustrup.com/JSF-AV-rules.pdf) standard. Each target should fail compilation for a compliant safety critical toolchain. 

Each target is of the form av_rule_xxx.cc where each file corresponds to a rule in the JSF++ standard.

**NOTE:** This does not infer complete compliance only that there is a good level of likelihood of compliance. Some rules must be enforced for example by code review.