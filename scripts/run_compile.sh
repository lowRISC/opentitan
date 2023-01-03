#!bin/bash
rm log.log
rm ../hw/top_titangrey/examples/sw/simple_system/hello_test/hello_test.vmem
make -C ../hw/top_titangrey/examples/sw/simple_system/hello_test/
cd ..
make clean
bender update
make scripts/compile.tcl
cd scripts

