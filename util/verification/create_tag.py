#!/usr/bin/env python3
import hjson
import os
import argparse
from collections import defaultdict

# Function to recursively build tags based on "Name" and "Depth"
def generate_tags(data):
    tag_hierarchy = []
    tags = {}

    for index, entry in enumerate(data):
        name = entry.get("Name")
        depth_str = entry.get("Depth", "-1")  # Default to -1 if Depth is missing

        # Handle non-integer Depth values gracefully
        try:
            depth = int(depth_str)
        except ValueError:
            print(f"Skipping entry at index {index} ({entry}): 'Depth' is not a valid integer ('{depth_str}')")
            continue

        if name is None:
            print(f"Skipping entry at index {index} ({entry}): missing 'Name'")
            continue

        # Adjust the hierarchy based on depth
        if depth < len(tag_hierarchy):
            tag_hierarchy = tag_hierarchy[:depth]  # Trim hierarchy to the correct depth

        # Add the current name to the hierarchy
        tag_hierarchy.append(name)

        # Generate the tag
        tag = "/".join(tag_hierarchy)
        entry['Tag'] = tag

        # Check if the tag is unique
        if tag in tags:
            raise ValueError(f"Duplicated tag '{tag}' found at entry index {index} at entry index {tags[tag]}")

        tags[tag] = index

    return data, tags

# Main function to handle file parsing and modification
def process_hjson(file_path):
    # Load the original HJSON file
    with open(file_path, 'r') as f:
        original_data = hjson.load(f)

    # Generate tags and check for uniqueness
    try:
        modified_data, tags = generate_tags(original_data)
    except ValueError as e:
        print(e)
        return

    # Overwrite the original file with the modified data containing 'Tag' fields
    with open(file_path, 'w') as f:
        hjson.dump(modified_data, f)

    print(f"Processing complete. Tags added successfully.")

if __name__ == "__main__":
    # Argument parser setup
    parser = argparse.ArgumentParser(description="Parse HJSON, generate tags, check uniqueness, and modify the file.")
    parser.add_argument("hjson_file", type=str, help="Path to the HJSON file to process.")

    # Parse arguments
    args = parser.parse_args()

    # Call the processing function with the provided HJSON file
    process_hjson(args.hjson_file)
