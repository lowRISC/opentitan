#!/usr/bin/env python3
import re
import hjson
import argparse
import os
import sys

class TagMismatchError(Exception):
    """Custom exception raised when there is a mismatch between Markdown and HJSON tags."""
    def __init__(self, message):
        super().__init__(message)

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
    """Extract requirement and feature tags from the Markdown file using a regex pattern based on block_name."""
    try:
        with open(markdown_file, 'r') as md_file:
            content = md_file.read()
    except FileNotFoundError:
        print(f"Error: The Markdown file '{markdown_file}' was not found.")
        return set(), set()

    # Regex patterns to find requirement and feature blocks
    req_pattern = fr"<!--\s*req_{block_name}_[0-9a-fA-F]{{4}}\s*begin\s*-->.*?<!--\s*req_{block_name}_[0-9a-fA-F]{{4}}\s*end\s*-->"
    ftr_pattern = fr"<!--\s*ftr_{block_name}_[0-9a-fA-F]{{4}}\s*begin\s*-->.*?<!--\s*ftr_{block_name}_[0-9a-fA-F]{{4}}\s*end\s*-->"

    # Find all matching tags for requirements and features
    req_matches = re.findall(req_pattern, content, re.DOTALL)
    ftr_matches = re.findall(ftr_pattern, content, re.DOTALL)

    # Extract the tags themselves (without the comment wrappers)
    req_tags = {re.search(fr"req_{block_name}_[0-9a-fA-F]{{4}}", match).group(0) for match in req_matches}
    ftr_tags = {re.search(fr"ftr_{block_name}_[0-9a-fA-F]{{4}}", match).group(0) for match in ftr_matches}

    return req_tags, ftr_tags

def extract_tags_from_hjson(hjson_file, block_name):
    """Extract both req and ftr tags from the HJSON file using regex patterns."""
    try:
        with open(hjson_file, 'r') as hjson_file:
            hjson_content = hjson.load(hjson_file)
    except FileNotFoundError:
        print(f"Error: The HJSON file '{hjson_file}' was not found.")
        sys.exit(1)

    # Convert the HJSON file to string and search for both req and ftr tags
    content = str(hjson_content)

    # Regex patterns to find req and ftr tags
    req_pattern = fr"req_{block_name}_[0-9a-fA-F]{{4}}"
    ftr_pattern = fr"ftr_{block_name}_[0-9a-fA-F]{{4}}"

    req_tags = set(re.findall(req_pattern, content))
    ftr_tags = set(re.findall(ftr_pattern, content))

    return req_tags, ftr_tags

def extract_block_name_from_hjson(hjson_file):
    """Extract the block_name from the HJSON file where Depth is 0."""
    try:
        with open(hjson_file, 'r') as file:
            hjson_content = hjson.load(file)
    except FileNotFoundError:
        print(f"Error: The HJSON file '{hjson_file}' was not found.")
        sys.exit(1)

    # Traverse the HJSON content to find the block where Depth is 0
    for block in hjson_content:
        if block.get("Depth") == "0":
            return block.get("Name")

    # If no block with Depth 0 is found, raise an error
    print("Error: No block with Depth 0 found in the HJSON file.")
    sys.exit(1)

def compare_tags(directory, hjson_file, demote_error):
    """Compare req and ftr tags from Markdown files in a directory with those in the HJSON file."""

    # Extract the block name from the HJSON file
    block_name = extract_block_name_from_hjson(hjson_file)
    print(f"Extracted block name: {block_name}\n")

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
    req_tags_in_files = {}  # To store which req tags are in which files
    ftr_tags_in_files = {}  # To store which ftr tags are in which files
    all_req_tags = set()
    all_ftr_tags = set()

    for md_file in markdown_files:
        req_tags, ftr_tags = extract_tags_from_markdown(md_file, block_name)
        all_req_tags.update(req_tags)
        all_ftr_tags.update(ftr_tags)

        # Map req tags to the file they were found in
        for tag in req_tags:
            if tag not in req_tags_in_files:
                req_tags_in_files[tag] = []
            req_tags_in_files[tag].append(md_file)

        # Map ftr tags to the file they were found in
        for tag in ftr_tags:
            if tag not in ftr_tags_in_files:
                ftr_tags_in_files[tag] = []
            ftr_tags_in_files[tag].append(md_file)

    # Extract req and ftr tags from the HJSON file
    hjson_req_tags, hjson_ftr_tags = extract_tags_from_hjson(hjson_file, block_name)

    # Compare req tags
    num_req_tags = len(all_req_tags)
    matching_req_tags = all_req_tags.intersection(hjson_req_tags)
    missing_in_hjson_req = all_req_tags - hjson_req_tags
    missing_in_markdown_req = hjson_req_tags - all_req_tags

    # Compare ftr tags
    num_ftr_tags = len(all_ftr_tags)
    matching_ftr_tags = all_ftr_tags.intersection(hjson_ftr_tags)
    missing_in_hjson_ftr = all_ftr_tags - hjson_ftr_tags
    missing_in_markdown_ftr = hjson_ftr_tags - all_ftr_tags

    # Print summary for requirements
    print(f"--- Requirements ---")
    print(f"  Total number of requirement tags found in Markdown files:    {num_req_tags}")
    print(f"  Number of requirement tags found in both Markdown and HJSON: {len(matching_req_tags)}")

    if missing_in_hjson_req:
        print("\n  Warning: Requirement tags found in Markdown but missing in HJSON, along with the Markdown files they were found in:")
        for tag in missing_in_hjson_req:
            if demote_error:
                print(f"    {tag} (found in {', '.join(req_tags_in_files[tag])})")
            else:
                raise TagMismatchError(f"Requirement tag '{tag}' found in Markdown but missing in HJSON.")
    else:
        print("  All requirement tags in the Markdown files are present in the HJSON file.")

    print(f"\n  Total number of requirement tags found in HJSON file:              {len(hjson_req_tags)}")
    print(f"  Number of requirement tags found in HJSON but missing in Markdown: {len(missing_in_markdown_req)}")

    if missing_in_markdown_req:
        print("  Warning: Requirement tags found in HJSON but missing in Markdown:")
        for tag in missing_in_markdown_req:
            if demote_error:
                print(f"    {tag}")
            else:
                raise TagMismatchError(f"Requirement tag '{tag}' found in HJSON but missing in Markdown.")

    # Print summary for features
    print(f"\n--- Features ---")
    print(f"  Total number of feature tags found in Markdown files:    {num_ftr_tags}")
    print(f"  Number of feature tags found in both Markdown and HJSON: {len(matching_ftr_tags)}")

    if missing_in_hjson_ftr:
        print("\n  Warning: Feature tags found in Markdown but missing in HJSON, along with the Markdown files they were found in:")
        for tag in missing_in_hjson_ftr:
            print(f"    {tag} (found in {', '.join(ftr_tags_in_files[tag])})")
    else:
        print("  All feature tags in the Markdown files are present in the HJSON file.")

    print(f"\n  Total number of feature tags found in HJSON file:              {len(hjson_ftr_tags)}")
    print(f"  Number of feature tags found in HJSON but missing in Markdown: {len(missing_in_markdown_ftr)}")

    if missing_in_markdown_ftr:
        print("  Warning: Feature tags found in HJSON but missing in Markdown:")
        for tag in missing_in_markdown_ftr:
            print(f"    {tag}")

def main():
    """Main function to parse arguments and call the comparison function."""
    parser = argparse.ArgumentParser(
                description="Compare 'req/ftr_<block_name>_xxxx' tags between Markdown specifications and the HJSON verification plan.")

    # Required arguments
    parser.add_argument(
        'directory',
        type=str,
        help='The path to the root directory of the block/IP. '
             'The sub-directories will be automatically explored except the "dv" folder. '
             'Eg.: hw/ip/block_name'
    )

    parser.add_argument(
        'hjson_file',
        type=str,
        help='The path to the HJSON Verification Plan file.'
    )

    # Optional argument to demote errors into warnings
    parser.add_argument(
        '--demote_error',
        action='store_true',
        help='Print a warning instead of raising an error for missing requirement tags.'
    )

    # Parse arguments
    args = parser.parse_args()

    # Call the compare function with the provided directory, HJSON file, and demote_error flag
    compare_tags(args.directory, args.hjson_file, args.demote_error)

if __name__ == '__main__':
    main()
