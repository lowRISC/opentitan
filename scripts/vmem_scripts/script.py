import struct

# Open the input file for reading
with open('hmac_smoketest.vmem', 'r') as f:
    # Read the contents of the file into a string
    contents = f.read()

# Split the contents of the file into lines
lines = contents.split('\n')

# Create a list to hold the output lines for the .vmem file
vmem_output_lines = []

# Create a list to hold the output lines for the .h file
h_output_lines = []

# Iterate over the lines in the input file
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
    new_data = []
    for word in data:
        # Extract the upper 64 bits of the word
        upper_bits1 = word[0:8]
        upper_bits2 = word[8:16]
        
        # Extract the lower 12 bits of the word
        lower_bits = word[16:]
        
        # Pad the lower 12 bits with zeros
        lower_bits = lower_bits.ljust(8, '0')
        
        # Append the new 32-bit words to the list
        new_data.append(upper_bits1)
        new_data.append(upper_bits2)
        new_data.append(lower_bits)
    
    # Append the new 32-bit words to the output lines for the .vmem file
    new_line = address
    for word in new_data:
        new_line += ' ' + word
    vmem_output_lines.append(new_line)
    
    # Convert the new 32-bit words to uint32_t values and append them to the output lines for the .h file
    h_output_lines.append('    ' + ', '.join([f'0x{word}' for word in new_data]) + ',')

# Join the output lines for the .vmem file into a string
vmem_output_contents = '\n'.join(vmem_output_lines)

# Write the output string for the .vmem file to a file
with open('hmac_smoketest32.vmem', 'w') as f:
    f.write(vmem_output_contents)

# Generate the output string for the .h file
h_output_contents = '''#ifndef HMAC_SMOKETEST_H_
#define HMAC_SMOKETEST_H_

#include <stdint.h>

static const uint32_t hmac_smoketest[] = {
''' + '\n'.join(h_output_lines) + '''
};

#endif /* HMAC_SMOKETEST_H_ */
'''

# Write the output string for the .h file to a file
with open('hmac_smoketest.h', 'w') as f:
    f.write(h_output_contents)
