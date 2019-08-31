#!/usr/bin/env bash
echo '' | ./hmac_model.py -v -k DEADBEEF
./hmac_model.py -k DEADBEEF -v message.dat

