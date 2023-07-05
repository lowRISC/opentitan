import sys

# Get the input and output file paths from command line arguments
if len(sys.argv) < 3:
    print("Usage: python convert_vmem_to_coe.py <input_file_path> <output_file_path>")
    sys.exit(1)
input_file_path = sys.argv[1]
output_file_path = sys.argv[2]

# Open the input file for reading
with open(input_file_path, 'r') as f:
    # Read the contents of the file into a string
    contents = f.read()

# Split the contents of the file into lines
lines = contents.split('\n')

# Create a list to hold the output lines
output_lines = []

# Add the COE header to the output
output_lines.append('memory_initialization_radix = 16;')
output_lines.append('memory_initialization_vector =')

# Iterate over the lines in the input file
for line in lines:
    # Skip any lines that don't start with "@"
    if not line.startswith('@'):
        continue
    
    # Otherwise, this line represents a new memory address
    data = line.split()[1:]
    
    # Transpose the row to columns
    for i in range(len(data)):
        # Create a new line for each element in the row
        output_line = data[i]
        output_lines.append(output_line + ',')
            
# Join the output lines into a string
output_contents = '\n'.join(output_lines)
output_contents = (output_contents[:-1] + ';')
# Open the output file for writing
with open(output_file_path, 'w') as f:
    # Write the output string to the file
    f.write(output_contents)
