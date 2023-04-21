# Open the input file for reading
with open('hmac_smoketest.vmem', 'r') as f:
    # Read the contents of the file into a string
    contents = f.read()

# Split the contents of the file into lines
lines = contents.split('\n')

# Create a list to hold the output lines
output_lines = []

# Iterate over the lines in the input file
for line in lines:
    # Skip any lines that don't start with "@"
    if not line.startswith('@'):
        output_lines.append(line)
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
        
    # Construct the new line of output
    new_line = address
    for word in new_data:
        new_line += ' ' + word
    
    # Add the new line to the output list
    output_lines.append(new_line)

# Join the output lines into a string
output_contents = '\n'.join(output_lines)

# Open the output file for writing
with open('hmac_smoketest32.vmem', 'w') as f:
    # Write the output string to the file
    f.write(output_contents)
