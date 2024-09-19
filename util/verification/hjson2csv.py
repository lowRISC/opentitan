#!/usr/bin/env python3
import sys
import csv
import hjson

# Check if the file to be converted has been defined
if len(sys.argv) > 1:
    # Load data from the HJSON file
    hjson_file = sys.argv[1]
    with open(hjson_file, 'r', encoding='utf-8') as file:
        data = hjson.load(file)

    # Check that the data is a list of objects
    if isinstance(data, list) and all(isinstance(item, dict) for item in data):
        # Extract column headers from the keys of the first object
        headers = data[0].keys()

        # Create the CSV file
        csv_file = 'vplan_example_converted.csv'
        with open(csv_file, 'w', newline='', encoding='utf-8') as file:
            writer = csv.DictWriter(file, fieldnames=headers)

            # Write headers in the CSV
            writer.writeheader()

            # Write the data rows in the CSV
            writer.writerows(data)

        print("Conversion successfully completed")
    else:
        print("HJSON data is not in the expected format")
else:
    print("Error: please specify the HJSON file path to be converted")
    print("       eg.: ./hjson2csv.py dv/files/verif/my_vplan.hjson")
    exit
