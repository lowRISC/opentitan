#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import binascii
import sys
import traceback

def extract_hex_between_delimiters(filename):
    """Reads a file, extracts hexadecimal digits between "+++" delimiters."""

    hex_dumps = []
    hex_data = ""
    capture = False
    counter = int(0)
    with open(filename, "r", errors="ignore") as file:
        for line in file:
            if line.strip() == "~~~":
                if capture:  # Second delimiter found, stop capturing
                    print(f'Dump {counter} starts with {hex_data[:16]}')
                    hex_dumps.append(bytes.fromhex(hex_data))
                    hex_data = ""
                    capture = False
                    counter += 1
                else:  # First delimiter found, start capturing
                    capture = True
                    print(f'Loading dump {counter}...')
            elif capture:  # Capture hex digits if in between delimiters
                hex_data += "".join(c for c in line if c in "0123456789ABCDEF")

    return hex_dumps

def extract_bits(value:int, mask:int) -> int:
    """Extracts bits from an integer using a mask.
    Args:
        value: The integer from which to extract bits.
        mask: The mask specifying which bits to extract.
    Returns:
        An integer representing the extracted bits, right-aligned.
    """
    extracted_bits = 0
    shift_count = 0

    # Iterate while the mask has remaining 1-bits
    while mask:
        if mask & 1:
            extracted_bits |= (value & 1) << shift_count
            shift_count += 1
        value >>= 1
        mask >>= 1

    return extracted_bits

def split_samples(dump:bytes, n_input: int, out_mask:int) -> bytes:
    """Converts a hexadecimal string to a bit string (little-endian 32-bit words)."""

    if len(dump) % 4 != 0:
        print("Invalid dump length", len(dump))

    groups = 8 // n_input
    samples = bytearray(len(dump)*groups)
    sample_count = int(0)
    mask = int((1 << n_input) - 1)
    if out_mask == 0:
          out_mask = mask
    out_bits = out_mask.bit_count()
    if out_mask > mask:
        print(f"Invalid out mask ({out_mask}) has {out_bits} bits; input ({n_input})")
    for i in dump:
        for _ in range(0, groups):
            v = i & mask
            i >>= n_input
            samples[sample_count] = extract_bits(v, out_mask)
            sample_count+=1

    return bytes(samples)

# ./bazelisk.sh test   --//signing:token=//signing/tokens:cloud_kms_prodc    --test_output=streamed   --cache_test_results=no //sw/device/tests:entropy_src_fw_observe_retrieve_test_silicon_owner_prodc_rom_ext
# bazel-testlogs/sw/device/tests/entropy_src_fw_observe_retrieve_test_silicon_owner_prodc_rom_ext/test.log
def main():
    if len(sys.argv) != 2:  # Check if exactly one argument (filename) was provided
        print("Usage: python script_name.py <filename>")
        sys.exit(1)

    filename = sys.argv[1]
    try:
      extracted_hex = extract_hex_between_delimiters(filename)
      print(f'Loaded {len(extracted_hex)} dumps')
      # print(binascii.hexlify(extracted_hex[0][0:8]))
      # print(binascii.hexlify(split_samples(extracted_hex[0][0:8], 4, 5)))
      # print(binascii.hexlify(split_samples(extracted_hex[0][0:8], 2, 3)))
      # print(binascii.hexlify(split_samples(extracted_hex[0][0:8], 1, 0)))

      # for i in extracted_hex[0][0:8]:
      #     print(hex(i))
      # exit(0)

      restart_dump = False
      prev_len = 0
      counter = 0
      for dump in extracted_hex:
          if prev_len != len(dump) and restart_dump:
              restart_dump = False
              counter += 1
          bits = 4 if len(dump) == 500000 else 1 if len(dump) == 125000 else None
          print(f"Dump {counter} size {len(dump)}, bits {bits},"
                f"restart {restart_dump}, starts {binascii.hexlify(dump[0:8])}")
          # Restart dump follows continuous one, if length is the same
          suffix="_restart" if restart_dump else ""
          filename=f'test_{counter}{suffix}'
          print(f'Writing to {filename}')
          with open(filename, "wb") as file:
              file.write(split_samples(dump, bits, 0))
          if bits == 4:
              for mask in range(1, 15):
                filename=f'test_{counter}_m{mask}{suffix}'
                print(f'Writing to {filename}')
                with open(filename, "wb") as file:
                    file.write(split_samples(dump, bits, mask))

          restart_dump = not restart_dump
          if not restart_dump:
              counter +=1
          prev_len = len(dump)

    except Exception as e:
            _, _, exc_traceback = sys.exc_info()
            exc_file, exc_line = traceback.extract_tb(exc_traceback)[-1][:2]
            print('\nError in %s:%s: ' % (exc_file, exc_line), {e})
if __name__ == "__main__":
    main()
