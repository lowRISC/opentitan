import sys
import os
import struct

# Check if the correct number of command line arguments is provided
if len(sys.argv) != 3:
    print("Usage: python script.py input_file output_path")
    sys.exit(1)

# Get the input file and output path from command line arguments
input_file = sys.argv[1]
output_path = sys.argv[2]

# Extract the file name without the extension
file_name = os.path.splitext(os.path.basename(input_file))[0]

# Open the input file for reading
with open(input_file, 'r') as f:
    # Read the contents of the file into a string
    contents = f.read()

# Split the contents of the file into lines
lines = contents.split('\n')

# Create a list to hold the output lines for the .vmem file (32-bit words)
vmem_output_lines = []

# Create a list to hold the output lines for the .h file (32-bit words)
h_output_lines = []

# Iterate over the lines in the input file
num_elements = 0
for line in lines:
    # Skip any lines that don't start with "@"
    if not line.startswith('@'):
        continue

    # Otherwise, this line represents a new memory address
    address = line.split()[0]
    address_int = int(address[1:], 16) * 2
    address = '@{:0>8X}'.format(address_int)
    data = line.split()[1:]

    # Convert the data from 64-bit words to 32-bit words and append them to the output lines for the .h file
    new_data32 = []
    for word in data:
        upper_bits = word[:8]
        lower_bits = word[8:]
        new_data32.append(upper_bits)
        new_data32.append(lower_bits)

    h_output_lines.append('    ' + ', '.join([f'0x{word}' for word in new_data32]) + ',')
    num_elements += len(new_data32)

    # Append the new line to the output lines for the .vmem file
    new_line = address + ' ' + ' '.join(data)
    vmem_output_lines.append(new_line)

# Join the output lines for the .vmem file into a string
vmem_output_contents = '\n'.join(vmem_output_lines)

# Generate the output string for the .h file
h_output_contents = '''#ifndef {file_name}_H_
#define {file_name}_H_

#include <stdint.h>

static const uint32_t buffer_size = {num_elements};
static const uint32_t {file_name}[{num_elements}] = {{
{h_output_lines}
}};

#endif /* {file_name}_H_ */
'''.format(file_name=file_name.upper(), num_elements=num_elements, h_output_lines='\n'.join(h_output_lines))

# Construct the output file paths
vmem_output_file = os.path.join(output_path, f'{file_name}.vmem')
h_output_file = os.path.join(output_path, f'{file_name}.h')

# Write the output string for the .vmem file to a file
with open(vmem_output_file, 'w') as f:
    f.write(vmem_output_contents)

# Write the output string for the .h file to a file
with open(h_output_file, 'w') as f:
    f.write(h_output_contents)
