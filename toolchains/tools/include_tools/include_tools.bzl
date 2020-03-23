load("@bazel_skylib//lib:paths.bzl", "paths")

def ShellCommand(cc_compiler_path):
    """Shell command that lists the compiler info and include directories

    Returns:
        string: shell command to run
    """
    return [cc_compiler_path, "-E", "-x", "c++", "-", "-v", "/dev/null"]

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
            filtered_lines.append(paths.normalize(line))
    result = []
    for path in filtered_lines:
        result.append("-I" + path)
    return result

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
