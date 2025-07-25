#!/usr/bin/env python3
import hjson
import re
import sys

# Function to load HJSON file
def load_hjson(file_path):
    with open(file_path, 'r') as file:
        return hjson.load(file)

# Function to get the parent group of the current one
def get_parent(grp_idx, group, groups):
    depth = int(group["Depth"])
    j = 1
    if depth > 0:
        # Move back, up to the parent group which corresponds to the depth level -1
        while (depth-1 != int(groups[grp_idx-j]["Depth"])):
            j += 1
        else:
            parent_idx = grp_idx-j
            return groups[parent_idx], parent_idx
    return group, 0

# Function to check if a key exists in each group
def check_group_structure(group, mandatory_keys):
    for key in mandatory_keys:
        if key not in group:
            return False, f"Missing key '{key}'"
    return True, ""

# Rule 6: Check Depth is a single positive integer starting from 0
def check_depth_format(depth):
    if re.match(r'^\d+$', depth):
        return True, ""
    return False, "'Depth' should be a positive integer"

# Rule 7, 8: Validate Name
def validate_name(name):
    if name == "":
        return False, "'Name' cannot be empty"
    if not re.match(r'^[a-z0-9_]+$', name):
        return False, "'Name' must be alphanumeric, lowercase, and can include underscores"
    return True, ""

# Rule 10, 11, 12, 13: Validate Reference format
def validate_reference(reference, dut_name):
    if reference == "":
        return True, ""  # Rule 9: Can be empty
    references = [r.strip() for r in reference.split(",")]
    for ref in references:
        if not re.match(r'^(req_|imp_).+_\w{4}$', ref):
            return False, "'Reference' must follow the pattern req_/imp_, followed by the DUT name matching with level 0 and a 4-digit hexadecimal"
        if not ref.startswith(f"req_{dut_name}_") and not ref.startswith(f"imp_{dut_name}_"):
            return False, f"'Reference' should contain the DUT name {dut_name}"
    return True, ""

# Rule 14, 15, 16: Validate Coverage_Result (0-100 with precision)
def validate_coverage_result(result):
    if result == "":
        return True, ""  # Rule 14: Can be empty
    try:
        result_float = float(result)
        if 0 <= result_float <= 100:
            if len(result.split(".")) == 1:
                return True, ""
            if len(result.split(".")) == 2 and len(result.split(".")[1]) <= 2:
                return True, ""
            return False, "'Coverage_Result' must have precision of 2 digits max"
        return False, "'Coverage_Result' should be between 0 and 100"
    except ValueError:
        return False, "Invalid number in 'Coverage_Result'"

# Rule 18, 19, 20, 21, 22: Validate Metric_Type
def validate_metric_type(metric_type, depth, parent_metric_type):
    allowed_types = ["dut_name", "section_title", "vplan", "testcase", "functional", "dut_assert", "tb_assert", "assertion", "formal", "emulation", "code_cov"]
    metric_types = [m.strip() for m in metric_type.split(",")]
    nb_metric_type = len(metric_type.split(","))

    for mtype in metric_types:
        # Cannot be empty if attempting to have multiple values
        if mtype == "" and nb_metric_type > 1:
            return False, "'Metric_Type' cannot be empty as multiple values have been declared with ','"
        # Rule 17 and 18: cannot be empty and should be among one/multiple of the predefined values
        if mtype not in allowed_types:
            return False, f"Invalid 'Metric_Type': {mtype}"
        # Rule 40: section_title cannot be with multiple values, it should always be alone
        if mtype == "section_title" and nb_metric_type != 1:
            return False, "'Metric_Type' section_title cannot be with multiple values, it should always be alone"

    # Rule 20: 'dut_name' must be attached to level 0
    if "dut_name" in metric_types and depth != "0":
        return False, "dut_name can only be attached to depth level 0"
    if "dut_name" not in metric_types and depth == "0":
        return False, "level 0 can only be atatched to dut_name"

    # Rule 21: Other than 'section_title', must have a parent with 'section_title' or 'dut_name'
    if depth != "0" and metric_type != "section_title" and parent_metric_type != "section_title" and parent_metric_type != "dut_name":
        return False, "Non-section_title must have parent defined as 'section_title'"

    return True, ""

# Rule 22, 23, 24, 25: Validate Item
def validate_item(item, metric_type):
    nb_item = len(item.split(","))
    nb_metric_type = len(metric_type.split(","))

    metric_types = [m.strip() for m in metric_type.split(",")]
    items = [i.strip() for i in item.split(",")]

    # Rule 22: Matching quantity of 'Item' and of 'Metric_Type'
    if nb_item != nb_metric_type:
        return False, "The number of 'Item' is not matching with the number 'Metric_Type'"

    idx = 0
    for item_n in items:
        # Check if no items is empty when multiple items are declared with ','
        if item_n == "" and nb_item > 1:
            return False, "'Item' cannot be empty as multiple values have been declared with ','"
        # Rule 25: should be empty only if the Metric_Type is dut_name or section_title
        if item_n != "" and (metric_types[idx] == "dut_name" or metric_types[idx] == "section_title"):
            return False, "'Item' should be empty when the 'Metric_Type' is 'dut_name' or 'section_title'"
        # Rule 25: should not be empty if the Metric_Type is not dut_name nor section_title
        if item_n == "" and metric_types[idx] != "dut_name" and metric_types[idx] != "section_title":
            return False, "'Item' should not be empty when the 'Metric_Type' is not 'dut_name' nor 'section_title'"
        # Rule 23: can only contain alphanumeric characters, no special characters except underscores and slashes
        if item_n != "" and not re.match(r'^[a-zA-Z0-9_/().:]+$', item_n):
            return False, "'Item' must be alphanumeric, upper/lowercase, and can include points, colons, underscores, parenthesis and slashes"
        idx += 1

    return True, ""

# Rule 26, 27, 28: Validate Priority (0 to 4)
def validate_priority(priority, parent_priority):
    # Rule 28
    if parent_priority != "" and priority != "":
        return False, "When the parent section is specifying a priority, the child cannot have a priority"
    if priority == "":
        return True, ""
    if priority.isdigit() and 0 <= int(priority) <= 4:
        return True, ""
    return False, "'Priority' should be a number from 0 to 4"

# Rule 29: Validate Milestone (V0, V1, V2, V3)
def validate_milestone(milestone, parent_milestone):
    allowed_milestones = ["V0", "V1", "V2", "V3"]
    # Rule 30
    if parent_milestone != "" and milestone != "":
        return False, "When the parent section is specifying a milestone, the child cannot have a milestone"
    if milestone == "":
        return True, ""
    if milestone in allowed_milestones:
        return True, ""
    return False, "'Milestone' must be one of: V0, V1, V2, V3"

# Rule 31, 32: Validate Weight (positive int or percentage)
def validate_weight(weight, depth, groups, parent_idx):
    if weight != "" and depth == "0":
        return False, "Any line can have an attached weight, except the depth 0"
    if weight == "":
        return True, ""  # Can be empty
    if weight.isdigit() and int(weight) > 0:
        return True, ""
    if (re.match(r'^\d{1,3}\.\d{1,2}%$', weight) or re.match(r'^\d{1,3}\%$', weight)) and 0.01 <= float(weight[:-1]) <= 100:
        return True, ""
    return False, "'Weight' should be a positive integer or a percentage (up to 2 decimals)"

# Rule 33, 34, 35: Validate section Weights
def validate_section_weights(groups):
    for idx, group in enumerate(groups):
        if group["Metric_Type"] == "dut_name" or group["Metric_Type"] == "section_title":
            j = 1
            sum_pct = 0
            has_non_pct = 0

            # Sum only the weights which are at the same level and under the same parent
            while int(group["Depth"]) < int(groups[idx+j]["Depth"]):
                weight = groups[idx+j]["Weight"]
                if int(groups[idx+j]["Depth"]) == int(group["Depth"])+1:
                    if weight == "":
                        has_non_pct = 1
                    elif weight.isdigit() and int(weight) > 0:
                        has_non_pct = 1
                    elif (re.match(r'^\d{1,3}\.\d{1,2}%$', weight) or re.match(r'^\d{1,3}\%$', weight)):
                        sum_pct = sum_pct+float(weight[:-1])
                if idx+j+1 < len(groups):
                    j += 1
                else:
                    # Reach end of the HJSON file
                    break

            sum_pct = round(sum_pct, 2)

            # Rule 33
            if has_non_pct == 0 and sum_pct != 100.00:
                return idx, False, "Under the same level of depth and under the same parent, if all the childs have an attached percentage, the sum of these percentages should be equal to 100"
            # Rule 35
            if has_non_pct == 1 and not sum_pct < 100.00:
                return idx, False, "Under the same level of depth and under the same parent, if an item is not specified as a percentage the sum of percentages should be strictly less than 100%"
    return idx, True, ""

# Rule 37, 38, 39, 41: Validate Goal (0-100 with precision)
def validate_goal(goal, parent_goal):
    # Rule 39
    if parent_goal != "" and goal != "":
        return False, "When the parent section is specifying a goal, the child cannot have a goal"
    if goal == "":
        return True, ""  # Rule 41: Can be empty
    try:
        goal_float = float(goal)
        if 0 <= goal_float <= 100:
            if len(goal.split(".")) == 1:
                return True, ""
            if len(goal.split(".")) == 2 and len(goal.split(".")[1]) <= 2:
                return True, ""
            return False, "'Goal' must have precision of 2 digits max"
        return False, "'Goal' should be between 0 and 100"
    except ValueError:
        return False, "Invalid number in 'Goal'"

# Check all rules
def check_rules(groups):
    mandatory_keys = ["Depth", "Name", "Reference", "Coverage_Result", "Description", "Metric_Type", "Item", "Owner", "Priority", "Milestone", "Weight", "Goal", "Issue"]
    depth_levels = []
    dut_name = ""
    error_count = 0
    errors = []

    # Rules 33-35: Section weights
    idx, valid, message = validate_section_weights(groups)
    if not valid:
        errors.append(f"  CSV row {idx+2}:\t{message}")
        error_count += 1

    for i, group in enumerate(groups):
        depth = group["Depth"]

        # Rule 4: Check if the group depths are consecutives when going up. As:
        #         depth '= n', so the previous group should be  '= n' or '= n-1'
        # Start to check on the second group only
        if i > 0:
            if int(depth) != int(groups[i-1]["Depth"]) and int(depth)-1 > int(groups[i-1]["Depth"]):
                errors.append(f"  CSV row {i+2}:\tCurrent depth level is not valid")
                error_count += 1

        # Get the parent group
        parent_group, parent_idx = get_parent(i, group, groups)

        # Rule 1: Check if group has all mandatory keys
        valid, message = check_group_structure(group, mandatory_keys)
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 2-6: Depth checks
        valid, message = check_depth_format(depth)
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        if depth == "0":
            # Rule 3: Ensure depth level 0 is declared only once
            if "0" in depth_levels:
                errors.append(f"    CSV row {i+2}:\tDepth level 0 appears more than once")
                error_count += 1
            dut_name = group["Name"]
        # Rule 2: depth level 0 should be in the first row
        if i == 0 and depth != "0":
            errors.append(f"  CSV row {i+2}:\tDepth level 0 should exist in the first row")
            error_count += 1

        # Rule 7, 8: Validate Name
        valid, message = validate_name(group["Name"])
        if not valid:
            errors.append(f"  CSV row {i+2}: {message}")
            error_count += 1

        # Rule 10-13: Validate Reference format
        valid, message = validate_reference(group["Reference"], dut_name)
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 15, 16: Validate Coverage_Result
        valid, message = validate_coverage_result(group["Coverage_Result"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 18-22: Validate Metric_Type
        valid, message = validate_metric_type(group["Metric_Type"], depth, parent_group["Metric_Type"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 23-25: Validate Item
        valid, message = validate_item(group["Item"], group["Metric_Type"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 26-27: Validate Priority
        valid, message = validate_priority(group["Priority"], parent_group["Priority"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 29: Validate Milestone
        valid, message = validate_milestone(group["Milestone"], parent_group["Milestone"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 31: Validate Weight
        valid, message = validate_weight(group["Weight"], depth, groups, parent_idx)
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        # Rule 37: Validate Goal
        valid, message = validate_goal(group["Goal"], parent_group["Goal"])
        if not valid:
            errors.append(f"  CSV row {i+2}:\t{message}")
            error_count += 1

        depth_levels.append(depth)

    return error_count, errors

# Main function to validate HJSON
def validate_hjson(file_path):
    try:
        hjson_data = load_hjson(file_path)
        error_count, errors = check_rules(hjson_data)
        if error_count == 0:
            print("HJSON file is valid.")
        else:
            print(f"{error_count} errors found:")
            for error in errors:
                print(error)
            raise ValueError(f"Validation failed with {error_count} errors.")
            sys.exit(1)
    except Exception as e:
        print(f"Failed to validate HJSON file: {str(e)}")
        sys.exit(1)

# Helper function for script usage
def print_helper():
    print("""
    Usage:
        ./validate_hjson.py <path_to_hjson_file>.hjson

    Description:
        This script validates an HJSON file against a set of predefined rules.
        The list of rules is available here:
          https://docs.google.com/spreadsheets/d/1pexjHdGFCWkTgEb_zDlpAZbOG8n0tp6ZnImTpmojSPA/edit?usp=sharing
        It will check for missing keys, invalid values, and format issues.
        If errors are found, it will print the number of errors and raise an exception.
    """)

# Main entry point
if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Error: Missing HJSON file argument.")
        print_helper()
        sys.exit(1)

    file_path = sys.argv[1]

    if file_path in ['-h', '--help']:
        print_helper()
        sys.exit(0)

    validate_hjson(file_path)
