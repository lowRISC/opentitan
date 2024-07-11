def bin_to_vmem_and_h(bin_file, vmem_file, h_file):
    with open(bin_file, 'rb') as f:
        data = f.read()

    num_words = len(data) // 4 + (1 if len(data) % 4 != 0 else 0)

    with open(vmem_file, 'w') as vmem, open(h_file, 'w') as h:
        address = 0
        h.write("#ifndef CLUSTER_H_\n")
        h.write("#define CLUSTER_H_\n\n")
        h.write("#include <stdint.h>\n\n")
        h.write(f"static const uint32_t buffer_size = {num_words};\n")
        h.write(f"static const uint32_t CLUSTER[{num_words}] = {{\n")

        words_in_line = 0
        for i in range(0, len(data), 24):  # Process 24 bytes (6 words) per line
            if address != 0:
                vmem.write('\n')
            vmem.write(f'@{address:08X}')
            for j in range(0, 24, 4):
                word = data[i+j:i+j+4]
                if len(word) < 4:
                    word = word.ljust(4, b'\x00')  # pad with zeros if not enough bytes
                word_value = int.from_bytes(word, byteorder='little')
                vmem.write(f' {word_value:08X}')
                
                if words_in_line == 0:
                    h.write(f'    0x{word_value:08X}')
                else:
                    h.write(f', 0x{word_value:08X}')
                
                words_in_line += 1
                if words_in_line == 6:
                    h.write(',\n')
                    words_in_line = 0
                
                address += 1

        if words_in_line != 0:
            h.write('\n')

        h.write("};\n\n")
        h.write("#endif // CLUSTER_H_\n")

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 4:
        print(f"Usage: {sys.argv[0]} <input.bin> <output.vmem> <output.h>")
        sys.exit(1)

    bin_file = sys.argv[1]
    vmem_file = sys.argv[2]
    h_file = sys.argv[3]
    bin_to_vmem_and_h(bin_file, vmem_file, h_file)
    print(f"Conversion complete: {vmem_file} and {h_file}")
