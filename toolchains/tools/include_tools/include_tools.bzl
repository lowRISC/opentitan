load("@bazel_skylib//lib:paths.bzl", "paths")

def ShellCommand(cc_compiler_path, command_line_list = [], os = "linux"):
    """Shell command that lists the compiler info and include directories

    Returns:
        string: shell command to run
    """
    if os == "linux":
        null_pipe_commands =  ["-", "-v", "/dev/null"]
    if os =="unix":
        null_pipe_commands =  ["-", "-v", "/dev/null"]
    elif os == "windows":
        null_pipe_commands  = ["-v","NUL"]
    return [cc_compiler_path, "-E", "-x", "c++"] + command_line_list + null_pipe_commands

def ProccessResponse(shell_command_result):
    """ Extracts the include paths from the path response

    Args:
        shell_command_result: The response from the output of the wrapped shell command
    Returns:
        list: strings in the include path
    """
    lines = shell_command_result.splitlines()
    filtered_lines = []
    start_of_includes_found = False
    for line in lines:
        if "#include <...> search starts here:" == line:
            start_of_includes_found = True
        line = line.replace(" ", "")
        if start_of_includes_found and (line.startswith("/") or line.startswith("c:\\")):
            line = line.replace("\\","/")
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
