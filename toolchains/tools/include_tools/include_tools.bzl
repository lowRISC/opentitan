load("@bazel_skylib//lib:paths.bzl", "paths")

def ShellCommand(cc_compiler_path, command_line_list = []):
    """Shell command that lists the compiler info and include directories

    Returns:
        string: shell command to run
    """
    return [cc_compiler_path, "-E", "-x", "c++"] + command_line_list + ["-", "-v", "/dev/null"]

def ProccessResponse(shell_command_result):
    """ Extracts the include paths from the path response

    Args:
        shell_command_result: The response from the output of the wrapped shell command
    Returns:
        list: strings in the include path
    """
    lines = shell_command_result.split("\n")
    filtered_lines = []
    start_of_includes_found = False
    for line in lines:
        if "#include <...> search starts here:" == line:
            start_of_includes_found = True
        line = line.replace(" ", "")
        if start_of_includes_found and line.startswith("/"):
            normalised_path = paths.normalize(line)
            path = normalised_path.rpartition("external")
            filtered_lines.append(path[1] + path[2])
    return filtered_lines

def CommandLineToTemplateString(command_line):
    """ CommandLineToTemplateString converts a list of command line elements to a single string that can be passed into a bazel repository template 
    """
    wrapped_command_line = [
        "\"" + command + "\""
        for command in command_line
    ]
    str = "[{}]".format(", ".join(wrapped_command_line))
    return str

include_tools = struct(
    ShellCommand = ShellCommand,
    ProccessResponse = ProccessResponse,
    CommandLineToTemplateString = CommandLineToTemplateString,
)
