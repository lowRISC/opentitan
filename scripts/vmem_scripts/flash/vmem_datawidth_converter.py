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

# Create a list to hold the output lines for the .vmem file (8-bit words)
vmem8_output_lines = []

# Iterate over the lines in the input file
num_elements = 0
for line in lines:
    # Skip any lines that don't start with "@"
    if not line.startswith('@'):
        continue
    
    # Otherwise, this line represents a new memory address
    address = line.split()[0]
    address_int = int(address[1:], 16) * 3
    address = '@{:0>8X}'.format(address_int)
    data = line.split()[1:]
    
    # Convert the data from 76-bit words to 32-bit words
    new_data32 = []
    for word in data:
        # Extract the upper 64 bits of the word
        upper_bits1 = word[0:8]
        upper_bits2 = word[8:16]
        
        # Extract the lower 12 bits of the word
        lower_bits = word[16:]
        
        # Pad the lower 12 bits with zeros
        lower_bits = lower_bits.ljust(8, '0')
        
        # Append the new 32-bit words to the list
        new_data32.append(upper_bits1)
        new_data32.append(upper_bits2)
        new_data32.append(lower_bits)
    
    # Append the new 32-bit words to the output lines for the .vmem file (32-bit words)
    new_line32 = address
    for word in new_data32:
        new_line32 += ' ' + word
    vmem_output_lines.append(new_line32)
    
    # Convert the new 32-bit words to uint32_t values and append them to the output lines for the .h file (32-bit words)
    h_output_lines.append('    ' + ', '.join([f'0x{word}' for word in new_data32]) + ',')
    num_elements += len(new_data32)
    
    # Convert the data from 76-bit words to 8-bit words
    new_data8 = ''
    for word in data:
        # Extract the upper 64 bits of the word
        upper_bits1 = word[0:8]
        upper_bits2 = word[8:16]
        
        # Extract the lower 12 bits of the word
        lower_bits = word[16:]
        
        # Pad the lower 12 bits with zeros
        lower_bits = lower_bits.ljust(4, '0')
        
        # Convert the 76-bit word to 8-bit words
        new_data8 += ' ' + ' '.join([upper_bits1[i:i+2] for i in range(0, len(upper_bits1), 2)])
        new_data8 += ' ' + ' '.join([upper_bits2[i:i+2] for i in range(0, len(upper_bits2), 2)])
        new_data8 += ' ' + ' '.join([lower_bits[i:i+2] for i in range(0, len(lower_bits), 2)])
    
    # Construct the new line of output for the .vmem file (8-bit words)
    new_line8 = address + new_data8
    
    # Add the new line to the output list for the .vmem file (8-bit words)
    vmem8_output_lines.append(new_line8)

# Join the output lines for the .vmem file (32-bit words) into a string
vmem_output_contents = '\n'.join(vmem_output_lines)

# Generate the output string for the .h file (32-bit words)
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
vmem_output_file32 = os.path.join(output_path, f'{file_name}32.vmem')
h_output_file32 = os.path.join(output_path, f'{file_name}32.h')
vmem_output_file8 = os.path.join(output_path, f'{file_name}8.vmem')

# Write the output string for the .vmem file (32-bit words) to a file
with open(vmem_output_file32, 'w') as f:
    f.write(vmem_output_contents)

# Write the output string for the .h file (32-bit words) to a file
with open(h_output_file32, 'w') as f:
    f.write(h_output_contents)

# Join the output lines for the .vmem file (8-bit words) into a string
vmem8_output_contents = '\n'.join(vmem8_output_lines)

# Write the output string for the .vmem file (8-bit words) to a file
with open(vmem_output_file8, 'w') as f:
    f.write(vmem8_output_contents)
