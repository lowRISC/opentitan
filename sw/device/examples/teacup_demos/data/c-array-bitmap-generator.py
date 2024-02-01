#!/usr/bin/python
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from PIL import Image

MAX_WIDTH = 96
MAX_HEIGHT = 64


def main(argv):
    parser = argparse.ArgumentParser(
        prog="PNG image to C array bitmap converter.",
        description=
        "This tool converts a .png image to a C array bitmap for driving a screen",
    )
    parser.add_argument("--png", required=True, type=str)
    parser.add_argument("--outfile", required=True, type=str)
    args = parser.parse_args()

    # Open the PNG file.
    try:
        im = Image.open(args.png)
    except IOError:
        print("Failed to open png file ", args.png)
        sys.exit(1)
    im.thumbnail((MAX_WIDTH, MAX_HEIGHT), Image.Resampling.LANCZOS)
    image_width = im.size[0]
    image_height = im.size[1]

    # Open the output file.
    try:
        outfile = open(args.outfile, "w")
    except IOError:
        print("Failed to open the output or bin files.")
        sys.exit(0)

    # Load the PNG image and convert it to a RGB565 bitmap C array.
    print(f"const size_t kBitmapCols = {image_width};", file=outfile)
    print(f"const size_t kBitmapRows = {image_height};", file=outfile)
    print(f"const uint16_t kBitmap[{image_height}][{image_width}] = {{",
          file=outfile)
    pixels = im.load()
    for h in range(image_height):
        print("{", file=outfile, end='')
        for w in range(image_width):
            r = pixels[w, h][0] >> 3
            g = pixels[w, h][1] >> 2
            b = pixels[w, h][2] >> 3
            rgb = (r << 11) | (g << 5) | b
            print("0x%04x," % (rgb), file=outfile, end='')
        print("},", file=outfile)
    print("};", file=outfile)
    outfile.close()
    print("PNG file \"%s\"" % args.png, "converted to \"%s\"" % args.outfile)


if __name__ == "__main__":
    main(sys.argv[1:])
