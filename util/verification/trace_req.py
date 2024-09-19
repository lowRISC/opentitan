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

def extract_tags_from_markdown(markdown_file, block_name, demote_error):
    """Extract requirement and implementation tags from the Markdown file using a regex pattern based on block_name.
    Ensure that tags with begin/end words are wrapping each blocks."""
    try:
        with open(markdown_file, 'r') as md_file:
            content = md_file.read()
    except FileNotFoundError:
        print(f"Error: The Markdown file '{markdown_file}' was not found.")
        return set(), set()

    # Regex patterns to find requirement and implementation blocks
    req_begin_pattern = fr"<!--\s*req_{block_name}_[0-9a-fA-F]{{4}}\s*begin\s*-->"
    req_end_pattern = fr"<!--\s*req_{block_name}_[0-9a-fA-F]{{4}}\s*end\s*-->"
    imp_begin_pattern = fr"<!--\s*imp_{block_name}_[0-9a-fA-F]{{4}}\s*begin\s*-->"
    imp_end_pattern = fr"<!--\s*imp_{block_name}_[0-9a-fA-F]{{4}}\s*end\s*-->"

    # Ensure all tags have a matching begin and end
    validate_matching_tags(content, req_begin_pattern, req_end_pattern, markdown_file, demote_error, "req")
    validate_matching_tags(content, imp_begin_pattern, imp_end_pattern, markdown_file, demote_error, "imp")

    # Extract the tags themselves (without the comment wrappers)
    req_tags = set(re.findall(fr"req_{block_name}_[0-9a-fA-F]{{4}}", content))
    imp_tags = set(re.findall(fr"imp_{block_name}_[0-9a-fA-F]{{4}}", content))

    return req_tags, imp_tags

def validate_matching_tags(content, begin_pattern, end_pattern, markdown_file, demote_error, tag_type):
    """Validate that each begin tag has a corresponding end tag and no nested tags exist."""
    # Find all positions of begin and end tags
    begin_tags = [(m.start(), m.group(0)) for m in re.finditer(begin_pattern, content)]
    end_tags = [(m.start(), m.group(0)) for m in re.finditer(end_pattern, content)]

    # Sort tags by their positions (so we process tags in the order they appear)
    tags = sorted(begin_tags + end_tags)

    # Stack to track open tags and ensure correct nesting
    stack = []

    for pos, tag in tags:
        if 'begin' in tag:
            if stack:
                # Nested tag detection: if there's already an open tag, raise an error or warning
                open_tag_pos, open_tag = stack[-1]
                error_message = (
                    f"Nested tag detected in '{markdown_file}': "
                    f"'{open_tag}' at position {open_tag_pos} is still open when '{tag}' begins at position {pos}"
                )
                if demote_error:
                    print(f"Warning: {error_message}")
                else:
                    raise TagMismatchError(error_message)

            stack.append((pos, tag))  # Push the begin tag to the stack
        elif 'end' in tag:
            if not stack:
                error_message = f"Unmatched end tag '{tag}' found in '{markdown_file}'"
                if demote_error:
                    print(f"Warning: {error_message}")
                else:
                    raise TagMismatchError(error_message)
            else:
                begin_pos, begin_tag = stack.pop()  # Pop the corresponding begin tag

                # Clean both tags to compare them properly
                begin_tag_cleaned = re.sub(r'\s+begin\s*-->', '', begin_tag).strip()
                end_tag_cleaned = re.sub(r'\s+end\s*-->', '', tag).strip()

                if begin_tag_cleaned != end_tag_cleaned:  # Ensure the tags match
                    error_message = f"Mismatched tag in '{markdown_file}': '{begin_tag}' does not match '{tag}'"
                    if demote_error:
                        print(f"Warning: {error_message}")
                    else:
                        raise TagMismatchError(error_message)

    # If stack is not empty, it means some begin tags don't have matching end tags
    if stack:
        for begin_pos, unmatched_tag in stack:
            error_message = f"Unmatched begin tag '{unmatched_tag}' found in '{markdown_file}'"
            if demote_error:
                print(f"Warning: {error_message}")
            else:
                raise TagMismatchError(error_message)

def extract_tags_from_hjson(hjson_file, block_name):
    """Extract both req and imp tags from the HJSON file using regex patterns."""
    try:
        with open(hjson_file, 'r') as hjson_file:
            hjson_content = hjson.load(hjson_file)
    except FileNotFoundError:
        print(f"Error: The HJSON file '{hjson_file}' was not found.")
        sys.exit(1)

    # Convert the HJSON file to string and search for both req and imp tags
    content = str(hjson_content)

    # Regex patterns to find req and imp tags
    req_pattern = fr"req_{block_name}_[0-9a-fA-F]{{4}}"
    imp_pattern = fr"imp_{block_name}_[0-9a-fA-F]{{4}}"

    req_tags = set(re.findall(req_pattern, content))
    imp_tags = set(re.findall(imp_pattern, content))

    return req_tags, imp_tags

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
    """Compare req and imp tags from Markdown files in a directory with those in the HJSON file."""

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
    imp_tags_in_files = {}  # To store which imp tags are in which files
    all_req_tags = set()
    all_imp_tags = set()

    for md_file in markdown_files:
        req_tags, imp_tags = extract_tags_from_markdown(md_file, block_name, demote_error)
        all_req_tags.update(req_tags)
        all_imp_tags.update(imp_tags)

        # Map req tags to the file they were found in
        for tag in req_tags:
            if tag not in req_tags_in_files:
                req_tags_in_files[tag] = []
            req_tags_in_files[tag].append(md_file)

        # Map imp tags to the file they were found in
        for tag in imp_tags:
            if tag not in imp_tags_in_files:
                imp_tags_in_files[tag] = []
            imp_tags_in_files[tag].append(md_file)

    # Extract req and imp tags from the HJSON file
    hjson_req_tags, hjson_imp_tags = extract_tags_from_hjson(hjson_file, block_name)

    # Compare req tags
    num_req_tags = len(all_req_tags)
    matching_req_tags = all_req_tags.intersection(hjson_req_tags)
    missing_in_hjson_req = all_req_tags - hjson_req_tags
    missing_in_markdown_req = hjson_req_tags - all_req_tags

    # Compare imp tags
    num_imp_tags = len(all_imp_tags)
    matching_imp_tags = all_imp_tags.intersection(hjson_imp_tags)
    missing_in_hjson_imp = all_imp_tags - hjson_imp_tags
    missing_in_markdown_imp = hjson_imp_tags - all_imp_tags

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

    print(f"\n  Total number of requirement tags found in HJSON file:                            {len(hjson_req_tags)}")
    print(f"  Number of requirement tags found in the vPlan but missing in the Markdown specs: {len(missing_in_markdown_req)}")

    if missing_in_markdown_req:
        print("  Warning: Requirement tags found in the vPlan but missing in the Markdown specs:")
        for tag in missing_in_markdown_req:
            if demote_error:
                print(f"    {tag}")
            else:
                raise TagMismatchError(f"Requirement tag '{tag}' found in the vPlan but missing in the Markdown specs.")

    # Print summary for implementations
    print(f"\n--- Implementations ---")
    print(f"  Total number of implementation tags found in Markdown files:    {num_imp_tags}")
    print(f"  Number of implementation tags found in both Markdown and HJSON: {len(matching_imp_tags)}")

    if missing_in_hjson_imp:
        print("\n  Warning: Implementation tags found in Markdown but missing in HJSON, along with the Markdown files they were found in:")
        for tag in missing_in_hjson_imp:
            print(f"    {tag} (found in {', '.join(imp_tags_in_files[tag])})")
    else:
        print("  All implementation tags in the Markdown files are present in the HJSON file.")

    print(f"\n  Total number of implementation tags found in HJSON file:                            {len(hjson_imp_tags)}")
    print(f"  Number of implementation tags found in the vPlan but missing in the Markdown specs: {len(missing_in_markdown_imp)}")

    if missing_in_markdown_imp:
        print("  Warning: Implementation tags found in the vPlan but missing in the Markdown specs:")
        for tag in missing_in_markdown_imp:
            print(f"    {tag}")

def main():
    """Main function to parse arguments and call the comparison function."""
    parser = argparse.ArgumentParser(
                description="Compare 'req/imp_<block_name>_xxxx' tags between Markdown specifications and the HJSON verification plan.")

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
