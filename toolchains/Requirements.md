# Toolchain requirements
There are several key requirements that the toolchain must meet in order to be considered safe for use in high reliability scenarios. Meeting these requirements should be the default behaviour for the toolchain. Any 'unsafe' behaviour will need to be manually specified. A further set of non-critical requirements will also be included for the purpose of optimality.

*NOTE:* These set of requirements are put in place to meet a stringent set of reliability standards as defined by the [JSF++ standard](http://www.stroustrup.com/JSF-AV-rules.pdf). Feedback in terms of how these requirements should be structured to improve reliability are welcomed. It is unlikely that changes will be accepted that would reduce the overall reliability of the system.

## Critical requirements
These set of requirements are of high priority and should be met by default. Configurable differences are allowable.

### Code size and complexity
*Requirement:*

[comment]: <> (This can be detected at compile time using clang-tools)
1. AV Rule 1 Any one function (or method) will contain no more than 200 logical source lines of code (LSLOCs). 

[comment]: <> (Unsure of what this means)
2. AV Rule 2 There shall be no self modifying code

[comment]: <> (This can be detected at compile time using clang-tools)
3. AV Rule 3 All functions should have a cyclomatic complexity of 20 or less

*Reference:*  [Doc. No. 2RDU00001 Rev C, 3.2, AV Rule 1-3](http://www.stroustrup.com/JSF-AV-rules.pdf) 

### Environment

#### Language
1. AV Rule 8 All code shall conform to ISO/IEC 14882:2014. Note that this differs to the JSF++ standard that requires conformance with ISO/IEC 14882:2002(E).

[comment]: <> (gcc_flags:-std=c++14)
*Reference:*  [Doc. No. 2RDU00001 Rev C, 4.4.1, AV Rule 8](http://www.stroustrup.com/JSF-AV-rules.pdf) 

#### Character sets
*Requirement:* 
1. AV Rule 9 Only characters described in [Doc. No. 2RDU00001 Rev C, 4.42, AV Rule 9](http://www.stroustrup.com/JSF-AV-rules.pdf) of the JSF standard. This essentially equates to only ASCII characters.

[comment]: <> (gcc_flags:-Wnormalized=nfc,-Werror=normalized)
2. AV Rule 10 Values of character types will be restricted to a defined and documented subset of ISO
10646-1.


[comment]: <> (gcc_flags:-Wtrigraphs,-Werror=trigraphs)
3. AV Rule 11 Trigraphs will not be used

[comment]: <> (Error by default in gcc) 
4. AV Rule 13 Multi-byte characters and wide-strings will not be used

[comment]: <> (clang_tidy_check:readability-uppercase-literal-suffix) 
5. AV Rule 14 Literal suffixes shall use uppercase rather than lowercase letters. 

*Reference:*  [Doc. No. 2RDU00001 Rev C, 4.4.2, AV Rule 9-14](http://www.stroustrup.com/JSF-AV-rules.pdf) 

### Libraries

#### Standard Libraries
*Requirement:*

[comment]: <> (This can be implemented using gcc poison) 
1. AV Rule 17 The error indicator errno shall not be used

[comment]: <> (This can be implemented using gcc poison) 
2. AV Rule 18 The macro offsetof, in library <stddef.h>, shall not be used.  

[comment]: <> (This can be implemented using gcc poison) 
3. AV Rule 19 <locale.h> and the setlocale function shall not be used. 

[comment]: <> (This can be implemented using gcc poison) 
4. AV Rule 20 The setjmp macro and the longjmp function shall not be used. 

[comment]: <> (This can be implemented using gcc poison) 
5. AV Rule 21 The signal handling facilities of <signal.h> shall not be used. 

[comment]: <> (This can be implemented using gcc poison) 
6. AV Rule 22 The input/output library <stdio.h> shall not be used

[comment]: <> (This can be implemented using gcc poison) 
7. AV Rule 23 The library functions atof, atoi and atol from library <stdlib.h> shall not be used. 

[comment]: <> (This can be implemented using gcc poison) 
8. AV Rule 24 The library functions abort, exit, getenv and system from library <stdlib.h> shall not be used. 

[comment]: <> (This can be implemented using gcc poison) 
9. AV Rule 25 The time handling functions of library <time.h> shall not be used. 

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.5.1, AV Rule 16-25](http://www.stroustrup.com/JSF-AV-rules.pdf)

### Declarations and Definitions
*Requirement:*

[comment]: <> (gcc_flags:-Wshadow,-Werror=shadow) 
1. AV Rule 135 Identifiers in an inner scope shall not use the same name as an identifier in an outer scope, and therefore hide that identifier. 

### Operators
*Requirement:*

[comment]: <> (gcc_flags:-Wsequence-point,-Werror=sequence-point) 
1. AV Rule 157 The right hand operand of a && or || operator shall not contain side effects. 

[comment]: <> (gcc_flags:-Wsign-compare,-Werror=sign-compare,-Wconversion,-Werror=conversion)
2. AV Rule 162 Signed and unsigned values shall not be mixed in arithmetic or comparison operations. 

### Flow Control Structures

*Requirement:*

[comment]: <> (gcc_flags:-ffunction-sections,-fdata-sections,-Wtype-limits ld_flags:-Wl,--gc-sections)
[comment]: <> (NOTE: 100% code coverage will also prove reachability, flags above strip out unreachable object code)
1. AV Rule 186 (MISRA Rule 52) There shall be no unreachable code. 

[comment]: <> (Not sure yet if this is acheivable at toolchain level)
2. AV Rule 187 (MISRA Rule 53, Revised) All non-null statements shall potentially have a side-effect. 

[comment]: <> (Not sure yet if this is completely acheivable at toolchain level)
[comment]: <> (gcc_flags:-Wunused-label)
3. AV Rule 188 (MISRA Rule 55, Revised) Labels will not be used, except in switch statements. 

[comment]: <> (Doable with clang-tidy)
4. AV Rule 189 (MISRA Rule 56) The goto statement shall not be used. 


[comment]: <> (Use gcc poison)
4. AV Rule 189 (MISRA Rule 56) The goto statement shall not be used. 


[comment]: <> (Doable with clang-tidy)
5. AV Rule 191 (MISRA Rule 58) The break statement shall not be used (except to terminate the cases of a switch statement). 


[comment]: <> (Doable with clang-tidy)
6. AV Rule 192 (MISRA Rule 60, Revised) All if, else if constructs will contain either a final else clause or a comment indicating why a final else clause is not necessary. 

[comment]: <> (gcc_flags:-Wimplicit-fallthrough,-Werror=implicit-fallthrough)
7. AV Rule 193 (MISRA Rule 61) Every non-empty case clause in a switch statement shall be terminated with a break statement. 

[comment]: <> (gcc_flags:-Wswitch,-Werror=switch)
8. AV Rule 194 (MISRA Rule 62, Revised) All switch statements that do not intend to test for every enumeration value shall contain a final default clause. 

[comment]: <> (gcc_flags:-Wswitch,-Werror=switch)
9. AV Rule 195 (MISRA Rule 63) A switch expression will not represent a Boolean value.

[comment]: <> (gcc_flags:-Wswitch-bool,-Werror=switch-bool)
10. AV Rule 196 (MISRA Rule 64, Revised) Every switch statement will have at least two cases and a potential default

[comment]: <> (May be acheivable with clang tidy)
11. AV Rule 197 (MISRA Rule 65) Floating point variables shall not be used as loop counters.  

[comment]: <> (May be acheivable with clang tidy)
12. AV Rule 198 The initialization expression in a for loop will perform no actions other than to initialize the value of a single for loop parameter. 

[comment]: <> (May be acheivable with clang tidy)
13. AV Rule 199 The increment expression in a for loop will perform no action other than to change a single loop parameter to the next value for the loop. 

[comment]: <> (May be acheivable with clang tidy)
14. AV Rule 200 Null initialize or increment expressions in for loops will not be used; a while loop will be used instead. 

[comment]: <> (May be acheivable with clang tidy)
15. AV Rule 201 (MISRA Rule 67, Revised) Numeric variables being used within a for loop for iteration counting shall not be modified in the body of the loop. 


*Reference:* [Doc. No. 2RDU00001 Rev C, 4.24, AV Rule 186-201](http://www.stroustrup.com/JSF-AV-rules.pdf)

### Expressions
*Requirement:*

[comment]: <> (gcc_flags:-Wfloat-equal,-Werror=float-equal)
1. AV Rule 202 (MISRA Rule 50) Floating point variables shall not be tested for exact equality or inequality. 


[comment]: <> (gcc_flags:-Wstrict-overflow=4,-Werror=strict-overflow)
[comment]: <> (NOTE: Some of these checks will need to be runtime checks)
2. AV Rule 203 (MISRA Rule 51, Revised) Evaluation of expressions shall not lead to overflow/underflow (unless required algorithmically and then should be heavily documented). 

[comment]: <> (May be acheivable with clang tidy)
3. AV Rule 204 A single operation with side-effects shall only be used in the following contexts:
   - by itself
   - the right-hand side of an assignment
   - a condition
   - the only argument expression with a side-effect in a function call
   - condition of a loop
   - switch condition
   - single part of a chained operation. 

[comment]: <> (May be acheivable with clang tidy)
4. AV Rule 204.1 (MISRA Rule 46) The value of an expression shall be the same under any order of evaluation that the standard permits. 

[comment]: <> (Needs to be implemented via review)
5. AV Rule 205 The volatile keyword shall not be used unless directly interfacing with hardware. 


*Reference:* [Doc. No. 2RDU00001 Rev C, 4.25, AV Rule 202-205](http://www.stroustrup.com/JSF-AV-rules.pdf)

### Memory Allocation 
*Requirement:*

[comment]: <> (This can be acheived using gcc poison)
The ability to use dynamic memory should be disabled in all cases. This is more stringent than the requirement in the JSF++ standard which allows dynamic memory only during initialisation.

[comment]: <> (This can be acheived using gcc poison, or by review)
1. AV Rule 206 (MISRA Rule 118, Revised) Allocation/deallocation from/to the free store (heap) shall not occur after initialization. Note that the “placement” operator new(), although not technically dynamic memory, may only be used in low-level memory management routines. See AV Rule 70.1 for object lifetime issues associated with placement operator new(). 

[comment]: <> (This can be acheived by review)
2. AV Rule 207 Unencapsulated global data will be avoided. 


*Reference:* [Doc. No. 2RDU00001 Rev C, 4.26, AV Rule 206-207](http://www.stroustrup.com/JSF-AV-rules.pdf)

### Fault Handling
*Requirement*: Exceptions are prohibited for use and will be disabled by default. The exception handler is usually part of the c++ runtime and tooling support in a bare-metal environment is limited. Further typical handling of exceptions is [non-deterministic](http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2019/p1947r0.pdf) and is therefore undesireable in a real-time environment. 

1. AV Rule 208 C++ exceptions shall not be used (i.e. throw, catch and try shall not be used.)

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.27, AV Rule 208](http://www.stroustrup.com/JSF-AV-rules.pdf)

### Portable Code

#### Data Abstraction
[comment]: <> (This may not be a critical requirement)
1. AV Rule 209 (MISRA Rule 13, Revised) The basic types of int, short, long, float and double shall not be used, but specific-length equivalents should be typedef’d accordingly for each compiler, and these type names used in the code. 

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.28.1, AV Rule 209](http://www.stroustrup.com/JSF-AV-rules.pdf)

#### Data Representation

[comment]: <> (Requires review)
1. AV Rule 210 Algorithms shall not make assumptions concerning how data is represented in memory (e.g. big endian vs. little endian, base class subobject ordering in derived classes, nonstatic data member ordering across access specifiers, etc.) 

[comment]: <> (Requires review)
2. AV Rule 210.1 Algorithms shall not make assumptions concerning the order of allocation of nonstatic data members separated by an access specifier. See also AV Rule 210 on data representation. 

[comment]: <> (Requires review)
3. AV Rule 211 Algorithms shall not assume that shorts, ints, longs, floats, doubles or long doubles begin at particular addresses. 

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.28.2, AV Rule 210-211](http://www.stroustrup.com/JSF-AV-rules.pdf)

#### Underflow/Overflow

[comment]: <> (Requires review)
1. AV Rule 212 Underflow or overflow functioning shall not be depended on in any special way. 

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.28.3, AV Rule 212](http://www.stroustrup.com/JSF-AV-rules.pdf)

#### Order of Execution
1. AV Rule 213 (MISRA Rule 47, Revised) No dependence shall be placed on C++’s operator precedence rules, below arithmetic operators, in expressions. 
2. AV Rule 214 Assuming that non-local static objects, in separate translation units, are initialized in a special order shall not be done. 

*Reference:* [Doc. No. 2RDU00001 Rev C, 4.28.4, AV Rule 213-214](http://www.stroustrup.com/JSF-AV-rules.pdf)

#### Pointer Arithmetic
[comment]: <> (gcc_flags:-Wpointer-arith)
[comment]: <> (NOTE: Only partial check)
1. AV Rule 215 (MISRA Rule 101) Pointer arithmetic will not be used

## Non-critical requirements
These set of requirements are in place to align with optimisation goals, and can be relaxed if deemed neccesary. Note that the implementation of these requirements will also be enabled by default. 
