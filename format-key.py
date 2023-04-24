#!/usr/bin/env python3

import sys

PUBKEY = """
04:2d:d4:e6:79:e9:0b:3d:77:89:25:37:c0:3f:0a:
d5:6d:84:4c:02:ca:8c:19:95:34:5b:3d:d8:82:d8:
c4:a7:3b:53:30:cf:7b:fc:ec:68:92:8c:b4:d2:15:
c7:f6:d6:34:b5:fb:bf:91:19:70:90:a0:cd:84:18:
74:f6:69:ff:cf
"""


def main(args):
    pubkey_lines = PUBKEY.split("\n")
    pubkey_list = []
    for line in pubkey_lines:
        line = line.lstrip()
        line = line.rstrip()
        line = line.replace(":", "")
        pubkey_list.append(line)
    pubkey = ''.join(pubkey_list)
    pubkey = pubkey[2:]
    print("X:")
    for i in range(0, len(pubkey) // 2, 8):
        print("0x%s, \\" % pubkey[i:i + 8])
    print("Y:")
    for i in range(len(pubkey) // 2, len(pubkey), 8):
        print("0x%s, \\" % pubkey[i:i + 8])


if __name__ == "__main__":
    main(sys.argv[1:])
