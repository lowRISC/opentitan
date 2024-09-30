#!/usr/bin/env python3
import sys
import csv
import hjson
import argparse

# Main function to handle CSV file parsing and HJSON file creation
def convert_csv(csv_file):
    with open(csv_file, mode='r', newline='', encoding='utf-8') as file:
        csv_reader = csv.DictReader(file)
        data = [row for row in csv_reader]

    # Convert data into HJSON
    hjson_data = hjson.dumps(data, indent=2)

    # Extract CSV file name and create a HJSON file with the same name
    hjson_file = csv_file.replace('.csv', '.hjson')

    # Write the HJSON file
    with open(hjson_file, mode='w', encoding='utf-8') as file:
        file.write(hjson_data)

    print("Conversion successfully completed")

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(
        description="Convert CSV verification plan file format into an HJSON file")
    parser.add_argument(
        'csv_file',
        type=str,
        help='Specify the CSV file path to be converted. '
             '    eg.: dv/files/verif/my_vplan.csv'
    )

    # Parse arguments
    args = parser.parse_args()

    # Call the compare function with the provided directory, HJSON file, and block name
    convert_csv(args.csv_file)

if __name__ == '__main__':
    main()
