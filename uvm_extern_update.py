#!/usr/bin/env python3
import os
import re
import sys

# List of standard UVM method names
SV_UVM_METHODS = [
    "new", "create", "build_phase", "connect_phase", "end_of_elaboration_phase",
    "start_of_simulation_phase", "run_phase", "extract_phase", "check_phase",
    "report_phase", "final_phase", "start", "body", "do", "randomize"
]

# Function to determine if a method name is a UVM method
def is_sv_uvm_method(name):
    if name in SV_UVM_METHODS:
        return True
    if any(name.startswith(prefix) for prefix in ["pre", "post", "mid"]):
        return any(name.endswith(method) for method in SV_UVM_METHODS)
    return False

# Function to classify methods
def classify_method(name):
    if name in SV_UVM_METHODS or is_sv_uvm_method(name):
        return "Standard SV/UVM methods"
    return "Class specific methods"

# Function to process each file
def process_file(filepath):
    with open(filepath, 'r') as file:
        lines = file.readlines()

    class_name = ""
    class_body = []
    extern_declarations = {
        "Constraints": [],
        "Standard SV/UVM methods": [],
        "Class specific methods": []
    }
    method_implementations = []
    in_class = False
    in_covergroup = False
    covergroup_name = ""
    method_body = []
    method_open = False

    for i, line in enumerate(lines):
        # Detect class declaration and extract class name
        match_class = re.match(r'\s*class\s+(\w+)', line)
        if match_class:
            in_class = True
            class_name = match_class.group(1)
            class_body.append(line)
            continue

        # Detect end of class
        if in_class and 'endclass' in line:
            in_class = False

            # Add extern declarations
            for category, decl in extern_declarations.items():
                if decl:
                    class_body.append(f"  // {category}\n")
                    class_body.extend(decl)

            # Add label to endclass if missing
            if ':' not in line:
                line = line.rstrip() + f" : {class_name}\n"

            class_body.append(line)  # endclass line
            class_body.append("\n")  # Separate class body from implementations
            class_body.extend(method_implementations)  # Add implementations after endclass

            # Copy over any remaining lines as they are
            class_body.extend(lines[i+1:])  # Remaining lines after endclass
            break

        # Handle covergroup start
        covergroup_match = re.match(r'\s*covergroup\s+(\w+)', line)
        if covergroup_match:
            in_covergroup = True
            covergroup_name = covergroup_match.group(1)  # Store covergroup name
            class_body.append(line)
            continue

        # Handle covergroup end
        if in_covergroup and 'endgroup' in line:
            in_covergroup = False
            if ':' not in line:
                # Add label after endgroup if missing
                line = line.rstrip() + f" : {covergroup_name}\n"
            class_body.append(line)
            continue

        # Detect `uvm_object_new` and replace it with extern declaration
        if in_class and 'uvm_object_new' in line:
            category = "Standard SV/UVM methods"
            extern_declarations[category].append("  extern function new(string name=\"\");\n")
            # Prepare the full new function body to add after the class ends
            new_function_body = f"function {class_name}::new(string name=\"\");\n  super.new(name);\nendfunction : new\n"
            method_implementations.append(new_function_body + "\n")
            continue

        # Detect `uvm_component_new` and replace it with extern declaration
        if in_class and 'uvm_component_new' in line:
            category = "Standard SV/UVM methods"
            extern_declarations[category].append("  extern function new(string name=\"\", uvm_component parent=null);\n")
            # Prepare the full new function body to add after the class ends
            new_function_body = f"function {class_name}::new(string name=\"\", uvm_component parent=null);\n  super.new(name, parent);\nendfunction : new\n"
            method_implementations.append(new_function_body + "\n")
            continue

        # If inside the class but not in a covergroup, handle methods, tasks, constraints
        if in_class and not in_covergroup:
            # Detect any preceding qualifiers for function, task, or constraint
            # Ignore lines already starting with "extern" or comments
            method_match = re.match(r'^(?!\s*(//|\*/|\*/|extern)).*?\b(function|task|constraint)\b\s+(void\s+)?(\w+)\s*(\{.*)?', line)

            if method_match:
                # Extract the method name
                method_name = method_match.group(4)

                is_constraint = re.match(r'^\s*(?!//|/\*)\s*constraint\b', line)

                # Create extern declaration for the constraint or method
                if is_constraint:
                    category = "Constraints"
                    extern_line = f"  extern constraint {method_name};\n"  # Add semicolon for extern constraint

                    # Start collecting the body of the constraint
                    method_body = [f"constraint {class_name}::{method_name} {{\n"]  # Adjust constraint label with class name
                    brace_count = 1  # We have one opening brace with the initial line

                    # Loop to collect the entire constraint body
                    for j in range(i + 1, len(lines)):
                        method_body.append(lines[j][2:] if lines[j].startswith("  ") else lines[j])
                        brace_count += lines[j].count('{')
                        brace_count -= lines[j].count('}')

                        # If brace count returns to zero, the constraint body is complete
                        if brace_count == 0:
                            i = j  # Update the main loop index to skip collected lines
                            break

                    # Append the constraint body to method implementations
                    method_implementations.append("".join(method_body) + "\n")

                    # Clear method_body to prevent duplicates
                    method_body = [extern_line]

                else:
                    category = classify_method(method_name)

                    extern_declaration = line  # Start building the extern declaration

                    # Continue collecting until we find a complete declaration ending with ";"
                    for j in range(i + 1, len(lines)):
                        if ";" in extern_declaration:
                            break
                        extern_declaration += lines[j]
                        if ";" in lines[j]:  # End of the function/task declaration
                            i = j  # Update index to skip these lines in the main loop
                            break

                    # Remove leading "virtual" if present for tasks/functions
                    extern_line = "  extern " + re.sub(r'^\s*virtual\s+', '', extern_declaration.lstrip())

                    # Remove "virtual" at the beginning if it exists
                    line_without_virtual = re.sub(r'^\s*virtual\s+', '', line)

                    # Start collecting the body of the method without "virtual"
                    method_body.append(line_without_virtual)

                    # Clear method_body to prevent duplicates
                    method_body = [line_without_virtual]

                # Add the modified line to extern_declarations
                extern_declarations[category].append(extern_line)
                method_open = True
                continue

            # Handle end of constraint, function, or task
            if method_open:
                is_eof_constraint = False

                # Collect full body, including comments inside
                method_body.append(line)

                # Find if the we are at the end of the constraint
                if (is_constraint and '}' in line):
                    is_eof_constraint = False
                    brace_count = 1  # Start with one closing brace found

                    # Move to the next lines to find the closing brace
                    for j in range(i, 0):   # Parse the file backward up until finding the start of the constraint
                        # Count braces
                        brace_count -= lines[j].count('{')
                        brace_count += lines[j].count('}')

                        # Encounter the start of the constraint
                        if re.search(r'\bconstraint\s+' + re.escape(method_name) + r'\b', lines[j]):
                            # If the brace count is zero, we have reached the end of the constraint
                            if brace_count == 0:
                                is_eof_constraint = True
                            break  # Exit the for loop as we found the end of the constraint

                # End detection for constraint, function, or task
                if is_eof_constraint or ('endfunction' in line or 'endtask' in line):
                    if method_name:
                        # Generate the label for class::method or class::constraint
                        method_label = f"{class_name}::{method_name}"

                        # For constraints, add class_name::constraint_name in the body declaration
                        if is_constraint:
                            formatted_body = "".join(method_body).replace(
                                f"constraint {method_name}", f"constraint {method_label}", 1
                            )
                        else:
                            # For functions/tasks, replace method_name in the body and append label to end
                            formatted_body = "".join(method_body).replace(method_name, method_label, 1)
                            formatted_body = re.sub(
                                r'(endfunction|endtask)\b(?!\s*:\s*\b' + re.escape(method_name) + r'\b)',
                                r'\1 : ' + method_name,
                                formatted_body
                            )
                    else:
                        # If method_name is None, join without replacement
                        formatted_body = "".join(method_body)

                    # Remove two spaces of indentation from each line in formatted_body
                    formatted_body = "\n".join([line[2:] if line.startswith("  ") else line for line in formatted_body.splitlines()])

                    # Append formatted_body with an additional newline for separation
                    method_implementations.append(formatted_body + "\n\n")

                    # Clear buffers and reset method state
                    method_body = []
                    method_open = False
                continue

            # Append remaining lines in class
            class_body.append(line)

        else:
            # Append lines outside of class definition
            class_body.append(line)

    # Write transformed content back to the file
    with open(filepath, 'w') as file:
        file.write("".join(class_body))
    print(f"Processed file: {filepath}")

# Function to process all files in a directory
def process_directory(directory):
    for dirpath, _, filenames in os.walk(directory):
        for filename in filenames:
            if filename.endswith(".sv") or filename.endswith(".sva") or filename.endswith(".svh"):
                filepath = os.path.join(dirpath, filename)
                process_file(filepath)

# Main entry point
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python script.py <directory_path>")
    else:
        directory_path = sys.argv[1]
        if os.path.isdir(directory_path):
            process_directory(directory_path)
        else:
            print("Invalid directory path.")
