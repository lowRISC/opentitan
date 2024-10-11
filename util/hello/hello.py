#!/usr/bin/env python3

from termcolor import colored
from opentitanlib.bazel import version_file

def main():
    print(colored("hello", 'red'))

def bye():
    print("bye")

if __name__ == '__main__':
    main()