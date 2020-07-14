#!/usr/bin/env python3
import sys, getopt
from junit_xml import *


def main(argv):
    inputfile = ''
    outputfile = ''

    try:
        opts, args = getopt.getopt(argv,"hi:o:",["ifile=","ofile="])
    except getopt.GetoptError:
        print ('openocd-to-junit.py -i <inputfile> -o <outputfile>')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print ('openocd-to-junit.py -i <inputfile> -o <outputfile>')
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-o", "--ofile"):
            outputfile = arg

    test_strings = defaultdict(list)
    test_timestamps = {}
    current_testname = ''

    test_cases = []
    current_test_case = None

    ocd_stdout = ''

    with open(inputfile, 'r') as infile:
        for line in infile:
            if 'Info' in line and 'riscv013_test_compliance()' in line:
                print(line.split(' '))
                current_testname = ' '.join(line.split(' ')[7:])
                test_strings[current_testname].append(line)
                test_timestamps[current_testname] = line.split(' ')[3]

            ocd_stdout += line

    for k,v in test_strings.items():
        current_test_case = TestCase(k, stdout=''.join(v),
                                     timestamp=test_timestamps[k])
        error_msg = ""
        for line in v:
            if 'FAILED' in line:
                error_msg += line;

            if error_msg:
                current_test_case.add_error_info(error_msg)

        test_cases.append(current_test_case)

    ts = TestSuite("openocd-compliance", test_cases, stdout=ocd_stdout)
    # pretty printing is on by default but can be disabled using prettyprint=False
    with open(outputfile, 'w') as outfile:
        TestSuite.to_file(outfile, [ts])

if __name__ == "__main__":
    main(sys.argv[1:])
