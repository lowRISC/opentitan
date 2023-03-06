# Open the output file for writing
with open('baadcode.vmem', 'w') as f:
    # Iterate over all the memory addresses from 0x00000000 to 0x0000FFFF
    for i in range(65536):
        # Convert the address to hexadecimal format and write it to the output file
        address = hex(i * 4)[2:].rjust(8, '0')
        f.write('@' + address + ' ')

        # Split the 32-bit word into four 8-bit words
        word = 'BAADC0DE'
        bytes = [word[i:i+2] for i in range(0, len(word), 2)]

        # Write the four 8-bit words to the output file
        f.write(bytes[0] + ' ')
        f.write(bytes[1] + ' ')
        f.write(bytes[2] + ' ')
        f.write(bytes[3] + '\n')
