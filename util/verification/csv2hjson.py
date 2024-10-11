#!/usr/bin/env python3
import sys
import csv
import hjson
import argparse

# Main function to handle CSV file parsing and HJSON file creation
def convert_csv(csv_file):
    # Open the CSV file and read its contents
    with open(csv_file, mode='r', newline='', encoding='utf-8') as file:
        csv_reader = csv.DictReader(file)
        data = [row for row in csv_reader]

    hjson_lines = ["["]  # Start the HJSON list with an opening bracket
    for i, row in enumerate(data, start=2):  # Start index at 2 to match the CSV rows
        # Add a comment with the CSV row number before each group
        hjson_lines.append(f"  # CSV row {i}")
        hjson_lines.append("  " + hjson.dumps(row, indent=2).replace("\n", "\n  "))  # Indent each item

    hjson_lines.append("]")  # End the HJSON list with a closing bracket

    # Extract CSV file name and create an HJSON file with the same name
    hjson_file = csv_file.replace('.csv', '.hjson')

    # Write the HJSON file with comments and valid HJSON formatting
    with open(hjson_file, mode='w', encoding='utf-8') as file:
        file.write("\n".join(hjson_lines))  # Join all HJSON lines into a single string

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

    # Call the convert_csv function with the provided CSV file path
    convert_csv(args.csv_file)

if __name__ == '__main__':
    main()
