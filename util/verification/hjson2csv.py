#!/usr/bin/env python3
import sys
import csv
import hjson
import argparse

# Main function to handle HJSON file parsing and CSV file creation
def convert_hjson(hjson_file):
    with open(hjson_file, 'r', encoding='utf-8') as file:
        data = hjson.load(file)

    # Check that the data is a list of objects
    if isinstance(data, list) and all(isinstance(item, dict) for item in data):
        # Extract column headers from the keys of the first object
        headers = data[0].keys()

        # Extract HJSON file name and create a CSV file with the same name
        csv_file = hjson_file.replace('.hjson', '.csv')

        with open(csv_file, 'w', newline='', encoding='utf-8') as file:
            writer = csv.DictWriter(file, fieldnames=headers)

            # Write headers in the CSV
            writer.writeheader()

            # Write the data rows in the CSV
            writer.writerows(data)

        print("Conversion successfully completed")
    else:
        print("HJSON data is not in the expected format")

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(
        description="Convert HJSON verification plan file format into a CSV file")
    parser.add_argument(
        'hjson_file',
        type=str,
        help='Specify the HJSON file path to be converted. '
             '    eg.: dv/files/verif/my_vplan.hjson'
    )

    # Parse arguments
    args = parser.parse_args()

    # Call the compare function with the provided directory, HJSON file, and block name
    convert_hjson(args.hjson_file)

if __name__ == '__main__':
    main()
