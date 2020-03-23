load("@bazel_skylib//lib:unittest.bzl", "asserts", "unittest")
load(":include_tools.bzl", "CommandLineToTemplateString", "ProccessResponse")

def _proccess_response_test_impl(ctx):
    response = """clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)
Target: x86_64-pc-linux-gnu
Thread model: posix
InstalledDir: /usr/bin
Found candidate GCC installation: /usr/bin/../lib/gcc/i686-linux-gnu/8
Found candidate GCC installation: /usr/bin/../lib/gcc/x86_64-linux-gnu/7
Found candidate GCC installation: /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0
Found candidate GCC installation: /usr/bin/../lib/gcc/x86_64-linux-gnu/8
Found candidate GCC installation: /usr/lib/gcc/i686-linux-gnu/8
Found candidate GCC installation: /usr/lib/gcc/x86_64-linux-gnu/7
Found candidate GCC installation: /usr/lib/gcc/x86_64-linux-gnu/7.4.0
Found candidate GCC installation: /usr/lib/gcc/x86_64-linux-gnu/8
Selected GCC installation: /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0
Candidate multilib: .;@m64
Selected multilib: .;@m64
 "/usr/lib/llvm-6.0/bin/clang" -cc1 -triple x86_64-pc-linux-gnu -E -disable-free -disable-llvm-verifier -discard-value-names -main-file-name - -mrelocation-model static -mthread-model posix -mdisable-fp-elim -fmath-errno -masm-verbose -mconstructor-aliases -munwind-tables -fuse-init-array -target-cpu x86-64 -dwarf-column-info -debugger-tuning=gdb -v -resource-dir /usr/lib/llvm-6.0/lib/clang/6.0.0 -internal-isystem /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/c++/7.4.0 -internal-isystem /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/x86_64-linux-gnu/c++/7.4.0 -internal-isystem /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/x86_64-linux-gnu/c++/7.4.0 -internal-isystem /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/c++/7.4.0/backward -internal-isystem /usr/include/clang/6.0.0/include/ -internal-isystem /usr/local/include -internal-isystem /usr/lib/llvm-6.0/lib/clang/6.0.0/include -internal-externc-isystem /usr/include/x86_64-linux-gnu -internal-externc-isystem /include -internal-externc-isystem /usr/include -fdeprecated-macro -fdebug-compilation-dir /home/nathaniel/Downloads/clang+llvm-9.0.0-x86_64-pc-linux-gnu -ferror-limit 19 -fmessage-length 122 -fobjc-runtime=gcc -fcxx-exceptions -fexceptions -fdiagnostics-show-option -fcolor-diagnostics -o - -x c++ -
clang -cc1 version 6.0.0 based upon LLVM 6.0.0 default target x86_64-pc-linux-gnu
ignoring nonexistent directory "/include"
ignoring duplicate directory "/usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/x86_64-linux-gnu/c++/7.4.0"
ignoring duplicate directory "/usr/include/clang/6.0.0/include"
#include "..." search starts here:
#include <...> search starts here:
 /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/c++/7.4.0
 /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/x86_64-linux-gnu/c++/7.4.0
 /usr/bin/../lib/gcc/x86_64-linux-gnu/7.4.0/../../../../include/c++/7.4.0/backward
 /usr/include/clang/6.0.0/include
 /usr/local/include
 /usr/include/x86_64-linux-gnu
 /usr/include
End of search list.
# 1 "<stdin>"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 389 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "<stdin>" 2
"""
    expect = [
        "-I/usr/include/c++/7.4.0",
        "-I/usr/include/x86_64-linux-gnu/c++/7.4.0",
        "-I/usr/include/c++/7.4.0/backward",
        "-I/usr/include/clang/6.0.0/include",
        "-I/usr/local/include",
        "-I/usr/include/x86_64-linux-gnu",
        "-I/usr/include",
    ]
    env = unittest.begin(ctx)
    asserts.equals(env, expect, ProccessResponse(response))
    return unittest.end(env)

proccess_response_test = unittest.make(_proccess_response_test_impl)

def _convert_command_line_to_string_test_impl(ctx):
    input = ["-Ia", "-Ib"]
    expect = """["-Ia", "-Ib"]"""
    env = unittest.begin(ctx)
    asserts.equals(env, expect, CommandLineToTemplateString(input))
    return unittest.end(env)

convert_command_line_to_string_test = unittest.make(_convert_command_line_to_string_test_impl)

def include_tools_test_suite(name):
    unittest.suite(
        name,
        proccess_response_test,
        convert_command_line_to_string_test,
    )
