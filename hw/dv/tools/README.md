# DV build and run flow
The Makefile system implemented here is a standardized solution for building and
running DV sims for all ip/block/top level testbenches. This is only a stop
gap solution until a proper build and run tool is developed and implemented. The
way the Makefiles are structured will hopefully make the eventual transition
easier.

## Makefile Organization
```
- hw/ip/<ip>/dv/Makefile OR
  hw/top_earlgrey/dv/Makefile
  - hw/dv/tools/Makefile
    - ral_gen.mk
    - fusesoc.mk
    - modes.mk
    - rules.mk
    - vcs/vcs.mk          # if SIMULATOR=vcs
    - xcelium/xcelium.mk  # if SIMULATOR=xcelium
```

### Test Makefile
The test Makefile that serves as the entry point into the DV build and run
flow is placed in individual 'dv' directories of each testbench. For example:
```hw/ip/uart/dv/Makefile```
This includes the top level Makefile, some mandatory variables that are to be
set and exported and the actual tests.

### Top level Makefile
This includes the top level Makefile which contains generic set of variable
names (most of which can be overridden) to indicate where, what and how to build
and run tests, some option groups and generic set of rules. This is located at
hw/dv/tools/Makefile

### Generic Tool-independent Make variables
The following is a list of Make variables that are used for specifying options
to run simulations in a tool-independent way. Some variables are overridable in
the Test Makefile (or command line) and some are appended to group / add options
together. Please see following table for more details:

Make variable | Description | Overridable (O) or Appendable (A) |
--------------|-------------|-----------------------------------|
DV_DIR | This is the top level DV directory for the IP containing the Test Makefile. | |
DUT_TOP | This is the top level dut module under test. This is used in `{vcs, xcelium}_fsdb.tcl` file. | |
TB_TOP | This is the top level tb module under test. This is used in `{vcs, xcelium}_fsdb.tcl` file. | |
FUSESOC_CORE | This is the testbench fusesoc .core name that contains the simulation target. This .core file is typically placed in the same directory as the test Makefile. | |
COMPILE_KEY | Users need to define COMPILE_KEY sets for building Test Makefile, CL with a unique sets of compile time options. This is to be done in the Test Makefile in this way: <br>`ifeq ($(COMPILE_KEY),foo)`<br> &emsp;`BUILD_OPTS += +define+FOO` <br>`endif`<br> There is a 'default' compile key already added which implies no additional compile time options are required. Within each test specification, the COMPILE_KEY can be overridden to use the specific compile key. <br>`ifeq ($(TEST_NAME),foo_test)`<br> &emsp;`COMPILE_KEY = foo` <br> &emsp;`# other test opts` <br>`endif` | O (Within tests,  & command line) |
UVM_TEST | SV UVM test class to create in the test. This is set to the 'base_test' by default and is overridden in the test specifications if needed. | O (Test Makefile) |
UVM_TEST_SEQ | SV UVM test sequence to create in the test. This is set to the 'base_test' by default and is overridden in the test specifications if needed. | O (Test Makefile) |
TEST_NAME | Name of the test to run. These are specified in the test Makefile. By default, it is set to run the sanity test (simply calling 'make' will run this test). | O (command line only) |
SIMULATOR | What simulator to use. Currently only 'vcs' is supported and is set by default. | O |
BUILD_OPTS | Options to pass for build. | A (Test Makefile :: COMPILE_KEY specifications only) |
CL_BUILD_OPTS | Pass additional build options on the command line. | A (command line only) |
RUN_OPTS | Options to pass for run. | A (Test Makefile :: test specifications only) |
CL_RUN_OPTS | Pass additional run options on the command line. | A (command line only) |
WAVES | Enable wave dumps (fsdb). Set to 0 by default; override with WAVES=1. | O |
SIMPROFILE | Turn on sim profiling (time option by default). Set to 0 by default; override with SIMPROFILE=1. | O |
COV | Turn on coverage collection. Set to 0 by default; override with COV=1. | O |
UVM_VERBOSITY | Verbosity level for UVM. Set to UVM_LOW by default; override with UVM_VERBOSITY=UVM_NONE / UVM_LOW / UVM_HIGH / UVM_DEBUG. | O |
BUILD_LOC | Build directory name in the scratch area. This defaults to the COMPILE_KEY used by the corresponding test. You can override it to use a different directory name. This is helpful when there is a test / regression already running and you made some fixes and want to rerun some failing test from another terminal without affecting the existing running sims. | O |
RUN_LOC | Run directory name in the scratch area. This defaults to a 'timestamp' value. You can override this to a specific name. Everytime a test is run, it creates a new directory with the current timestamp for the name. By overriding this with a specific name and rerunning the same test with the same directory name, you won't have to reopen waves - you can just reload. This is useful during test debug. | O |
SCRATCH_ROOT | This is the path to the root scratch area for bulding and running tests. If SCRATCH_ROOT is not already set, it will create a `scratch` directory in `pwd` which typically is the same as `DV_DIR`. | O (command line only) |
RUN_DIR_LIMIT | When you run tests, The flow creates a new `RUN_LOC` directory with the current timestamp (unless it is overridden). In course of debug, you may run the same test multiple times, which will eventually result in a large number of old timestamp directories in the scratch space. Without periodic cleanup, you may run out of scratch space. By default, this variable is set to 5, which means before running the test, it will prune the test area to contain no more than RUN_DIR_LIMIT number of most recent directories (including the newly created one). On the flipside, if you want to run the same test with a large number of iterations, you will need to override this variable to be set to that many iterations to prevent the flow from deleting actively running simulations. | O (command line only) |
SEED | This is a run time parameter passed to the sim executable. It uses `od` command to generate a 32-bit random number to run the sim with a unique seed. You can override this variable on the command line to run the test with a specific seed for debug. | O (command line only) |
XPROP | This is a compile time parameter to enable / disable X-Propagation. Set to 1 by default. | O (command line only) |

This is not an exhaustive list of Make variables. Please see `./Makefile` and
`./*.mk` for more such variables in use.

### ral_gen.mk
#### RAL generation tool specific mk file
This lists tools and options to generate the ral model by simply running the
command `make ral` from the same directory as the Test Makefile. For generating
the UVM REG based RAL model, we use the same [in-house tool]({{< relref "doc/rm/register_tool" >}}) for autogenerating
RTL with mako template.

### fusesoc.mk
#### RTL/TB filelist generation tool specific mk file
This lists tools and options to generate the flattened filelist to supply to the
simulator during the build step.

### modes.mk
#### Modes or option groups that can be turned on easily
This lists common modes (which are groups of compile time and / or run time options)
passed to the simulator for turning on a specific function. Modes listed in this
file are meant to be common across all environments and simulator tools. Modes added
in this file are `WAVES`, `COV`, `SIMPROFILE` and `UVM_TRACE`. These are truly
global and can be turned on easily on the command line by setting them to 1: `COV=1`
switch on the command line will turn on coverage. These modes may require options
that are specific to the simulator tool, so the make variable `SIMULATOR` can be used
to set tool specific options.

### rules.mk
#### List of Make targets and recipes
This is the only file in the make flow that contains targets and recipes that
are completely agnostic to the tools used. It sequences the build and run set
of targets.

### Simulator mk ({vcs, xcelium}.mk)
#### Simulator tool specific options
The top level Makefile uses `SIMULATOR` variable (which is set to `vcs` by
default) to enable tool specific options. If support for new tools need to be
added, then those tool specific mk files need to be supplied. It sets the
following mandatory variables - `SIMCC` & `SIMX`. It also exports additional
tool specific variables to the sub shell when the recipes are executed. This
file has been placed in the respective tool directory.

### Simulation targets
* **build**: Compile and elaborate the testbench
* **gen_sv_flist**: Generate the full file list which will be used by the
  simulator to build the simulation executable
* **run**: Run the test (the simulation executable needs to be built already)
* **env/\<ip\>_reg_block.sv**: Generate the RAL model only
* **sw_build**: Only compile the C SW test

### Building and running tests
All of the below command examples are to be run from the 'dv' directory
containing the Test Makefile.

##### Run the following command to build and run tests:
```console
$ make TEST_NAME=[test-name] [overrides]
```

##### To only buld the simv:
```console
$ make build TEST_NAME=[test-name] [overrides]
```

##### To run the sim after build is complete:
```console
$ make run TEST_NAME=[test-name] [overrides]
```

##### To build and run the sanity test:
```console
$ make
```
This will work provided user has specified a set a 'default' value to the
`TEST_NAME` Make variable.

##### Below are some examples

###### Build and run a test:
This builds the 'default' compile key and runs the 'uart_sanity' test
```console
$ make TEST_NAME=uart_sanity
```

###### Run with specific seed:
```console
$ make TEST_NAME=<test-name> SEED=123423334
```

###### Dump waves:
```console
$ make TEST_NAME=<test-name> SEED=123423334 WAVES=1
```

###### Run with coverage option enabled:
```console
$ make TEST_NAME=<test-name> COV=1
```

The options.mk file lists several tool options passed to the build and run steps
for enabling coverage collection. One of the options is adding a hier file (with
a `-cm_hier` switch). By default, it looks for a file called `cover.cfg` in the
'dv' directory set using the `CM_HIER` Make variable - if it exists, it adds the
switch automatically when coverage is enabled. If another hier file is desired
 (or with another name), it can be placed anywhere as the user desires and user can
 add the following line to the Test Makefile:

```gnumake
CM_HIER := <path-to-hier-file
```

###### Enable sim profiling:
```console
$ make TEST_NAME=<test-name> SIMPROFILE=1
```

###### Override UVM verbosity:
```console
$ make TEST_NAME=<test-name> WAVES=1 UVM_VERBOSITY=UVM_DEBUG
```

###### Build only (This will build the 'default' compile key):
```console
$ make build
```

###### Build 'foo' compile key instead:
```console
$ make build COMPILE_KEY=foo
```

###### Build with 'FOO' preprocessor flag:
```console
$ make build CL_BUILD_OPTS+=+define+FOO
```

###### Run with 'FOO' runtime plusarg:
```console
$ make TEST_NAME=<test-name> CL_RUN_OPTS+=+FOO
```

###### Run test with Xcelium:
```
$ make TEST_NAME=<test-name> SIMULATOR=xcelium
```

###### Run test with Xcelium and dump WAVES in fsdb:
```console
$ make TEST_NAME=<test-name> SIMULATOR=xcelium WAVES=1
```

###### Run test with Xcelium and dump WAVES in shm:
```console
$ make TEST_NAME=<test-name> SIMULATOR=xcelium WAVES=1 DUMP=shm
```

###### Run only (This assumes the sim executable for the specified compile key is available):

```console
$ make run TEST_NAME=<test-name> SEED=123423334 WAVES=1
```
