#!/usr/bin/env python3
import sys
import csv
import hjson

# Check if the file to be converted has been defined
if len(sys.argv) > 1:
    # Read the CSV file
    csv_file = sys.argv[1]

    with open(csv_file, mode='r', newline='', encoding='utf-8') as file:
        csv_reader = csv.DictReader(file)
        data = [row for row in csv_reader]

    # Convert data into HJSON
    hjson_data = hjson.dumps(data, indent=2)

    # Write the HJSON file
    with open('vplan_example_converted.hjson', mode='w', encoding='utf-8') as file:
        file.write(hjson_data)

    print("Conversion successfully completed")
else:
    print("Error: please specify the CSV file path to be converted")
    print("       eg.: ./csv2hjson.py dv/files/verif/my_vplan.csv")
    exit
