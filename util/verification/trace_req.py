#!/usr/bin/env python3
import sys
import os
import hjson
import argparse
import re

def find_markdown_files(directory):
    """Recursively find all Markdown files in a directory, except in 'dv' directories."""
    markdown_files = []

    # Walk through directory and subdirectories
    for root, dirs, files in os.walk(directory):
        # Exclude 'dv' directories
        dirs[:] = [d for d in dirs if d != 'dv']

        # Find all .md files
        for file in files:
            if file.endswith('.md'):
                markdown_files.append(os.path.join(root, file))

    return markdown_files

def extract_tags_from_markdown(markdown_file, block_name):
    """Extract tags from the Markdown file using a regex pattern based on block_name."""
    try:
        with open(markdown_file, 'r') as md_file:
            content = md_file.read()
    except FileNotFoundError:
        print(f"Error: The Markdown file '{markdown_file}' was not found.")
        return set()

    # Regex pattern to find tags in the form of 'req_<block_name>_xxxx' where xxxx is 4 hexadecimal digits
    pattern = fr"req_{block_name}_[0-9a-fA-F]{{4}}"
    tags = re.findall(pattern, content)
    return set(tags)  # Return unique tags as a set

def extract_tags_from_hjson(hjson_file, block_name):
    """Extract tags from the HJSON file using a regex pattern based on block_name."""
    try:
        with open(hjson_file, 'r') as hjson_file:
            hjson_content = hjson.load(hjson_file)
    except FileNotFoundError:
        print(f"Error: The HJSON file '{hjson_file}' was not found.")
        sys.exit(1)

    # Convert the HJSON file to string and search for tags
    content = str(hjson_content)

    # Regex pattern to find tags in the form of 'req_<block_name>_xxxx' where xxxx is 4 hexadecimal digits
    pattern = fr"req_{block_name}_[0-9a-fA-F]{{4}}"
    tags = re.findall(pattern, content)
    return set(tags)  # Return unique tags as a set

def compare_tags(directory, hjson_file, block_name):
    """Compare tags from Markdown files in a directory with those in the HJSON file."""

    # Find all .md files in the directory (except 'dv')
    markdown_files = find_markdown_files(directory)

    if not markdown_files:
        print(f"No Markdown files found in directory '{directory}'")
        return

    # Display found Markdown files
    print("The following Markdown files have been found and will be analyzed:")
    for md_file in markdown_files:
        print(f"  {md_file}")

    print()  # Blank line before continuing

    # Collect tags from all Markdown files, and map tags to files
    markdown_tags = set()
    tags_in_files = {}  # To store which tags are in which files

    for md_file in markdown_files:
        file_tags = extract_tags_from_markdown(md_file, block_name)
        markdown_tags.update(file_tags)

        # Map tags to the file they were found in
        for tag in file_tags:
            if tag not in tags_in_files:
                tags_in_files[tag] = []
            tags_in_files[tag].append(md_file)

    # Extract tags from the HJSON file
    hjson_tags = extract_tags_from_hjson(hjson_file, block_name)

    # Count number of tags
    num_md_tags = len(markdown_tags)
    num_matching_tags = len(markdown_tags.intersection(hjson_tags))

    # Find tags that are missing in the HJSON file
    missing_in_hjson = markdown_tags - hjson_tags

    # Find tags that are in HJSON but not in Markdown
    missing_in_markdown = hjson_tags - markdown_tags

    # Print summary
    print(f"Total number of tags found in Markdown files:       {num_md_tags}")
    print(f"Number of tags found in both Markdown and HJSON:    {num_matching_tags}")

    if missing_in_hjson:
        print("\nTags found in Markdown but missing in HJSON:")
        for tag in missing_in_hjson:
            print(f"  {tag} (found in {', '.join(tags_in_files[tag])})")
    else:
        print("All tags in the Markdown files are present in the HJSON file.")

    print(f"\n")
    print(f"Total number of tags found in HJSON file:               {len(hjson_tags)}")
    print(f"Number of tags found in HJSON but missing in Markdown:  {len(missing_in_markdown)}")

    if missing_in_markdown:
        print("Tags found in HJSON but missing in Markdown:")
        for tag in missing_in_markdown:
            print(f"  {tag}")

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(
        description="Compare 'req_<block_name>_xxxx' tags between Markdown specifications and the HJSON verification plan.")
    parser.add_argument(
        'block_name',
        type=str,
        help='The block name to look for in the tag format "req_<block_name>_xxxx".'
    )
    parser.add_argument(
        'directory',
        type=str,
        help='The path to the root directory of the block/IP. '
             'The sub-directories will be automatically explored except the "dv" folder.'
             'Eg.: hw/ip/block_name'
    )
    parser.add_argument(
        'hjson_file',
        type=str,
        help='The path to the HJSON file.'
    )

    # Parse arguments
    args = parser.parse_args()

    # Call the compare function with the provided directory, HJSON file, and block name
    compare_tags(args.directory, args.hjson_file, args.block_name)

if __name__ == '__main__':
    main()
