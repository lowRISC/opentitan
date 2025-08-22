# OpenTitan top description

Due to the very flexible nature of OpenTitan's tops, it is difficult for the build system to adjust the build graph without some knowledge of the top that it is compiling for.
A simple but common example is the existence of an IP: if a top does not have an IP, it should not generate register headers for it, should not compile drivers for it and so on.
How can the build system determine when this is the case?

To solve this issue, a minimal description of each top is created in Bazel so that the build system can query its properties.

## Creating the top description

The description is created in `.bzl` files using two macros provided by [`//rules/opentitan:hw.bzl`](https://github.com/lowRISC/opentitan/blob/master/rules/opentitan/hw.bzl):
- `opentitan_ip`: create the description of an IP,
- `opentitan_top`: create the description of a top.

A description looks like this:
```py
MATCHA = opentitan_top(
    # The name of the top
    name = "matcha",
    # A list of arbitrary attributes
    hjson = "//hw/top_matcha/data/autogen:top_matcha.gen.hjson",
    # ... more attributes
    # List of IPS:
    ips = [
        opentitan_ip(
            # Name of the IP
            name = "uart",
            # List of arbitrary attributes
            hjson = "//hw/ip/uart/data:uart.hjson",
            # ... more attributes
        ),
        # many more IPs...
    ]
)
```

Since this process can be quite tedious, parts of it are automated by topgen, see the documentation [top creation](./create_top.md).
The list of attributes is explained in more details in the following sections.

## Attributes

Each top and IP can include an arbitrary list of attributes. Some of those attributes have a special meaning because they are used by build system to perform some important tasks.
You are free to create new attributes for your top if you need them (see [example](#A-simple-top-label)).
The following sections will describe the well-known top and IP attributes.

### Top attributes

The following attributes have a well-defined meaning in the codebase.
- `hjson`: label string of the complete Hjson description file of the top created by `topgen`.
- `top_lib`: label string of the top's `cc_library` created by `topgen`. This library contains all the top-specific constants.
- `top_ld`: label string of the top's `ld_library` created by `topgen`. This library contains all the top-specific linker constants.
- `platform`: label of the top's platform. This setting can be used to override the default bazel platform when building device code.
  If unspecified, `//sw/target:opentitan_platform` will be used.

Example for Earlgrey:
```py
EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_ld = "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ips = [...],
)
```

### IP attributes

The following attributes have a well-defined meaning in the codebase:
- `hjson`: label string of the Hjson description file of the IP.
- `ipconfig`: for generated IPs, this is label string of the `<top>_<ip>.ipconfig.hjson` file created by `ipgen`.
- `extension`: for IPs which want to provide an extension plugin to `dtgen`, this is the label-string of the `py_library` of the extension.
- `dt_hdr_deps`: extra dependencies which will be added to the `cc_library` target containing the DT header for this IP.
- `dt_src_deps`: extra dependencies which will be added to the `cc_library` target containing the DT source for this IP.

Example for the `uart` IP:
```py
UART = opentitan_ip(
    name = "uart",
    hjson = "//hw/ip/uart/data:uart.hjson",
)
```
More complex example for the `clkmgr` IP.
```py
CLKMGR = opentitan_ip(
    name = "clkmgr",
    hjson = "//hw/top_earlgrey/ip_autogen/clkmgr:data/clkmgr.hjson",
    ipconfig = "//hw/top_earlgrey/ip_autogen/clkmgr:data/top_earlgrey_clkmgr.ipconfig.hjson",
    extension = "//hw/top_earlgrey/ip_autogen/clkmgr/util:dt",
)
```

## Using the top description

Access to the top's description is available through two APIs:
- A high-level API defined in `//hw/top:defs.bzl` which creates `select()` expressions to access top/IPs attributes and express requirement.
  See section below on `//hw/top:defs.bzl` for more details. This is the recommended API.
- A low-level API defined in `//rules/opentitan:hw.bzl` which directly operates on the `opentitan_top`-created objects.
  This API is used to implement the high-level one and it is not recommended to use it directly unless absolutely necessary.

### High-level API

The recommended way to access attributes is through the macros defined in [`//hw/top:defs.bzl`](https://github.com/lowRISC/opentitan/blob/master/hw/top/defs.bzl).
The following macros are particularly useful. To see examples of use, see the [Example section](#Examples).
For more details, look at the documentation in `//hw/top:defs.bzl`
- The most general macro is `opentitan_select_top_attr(attr_name, required = True, default = None, fn = None)`.
  This macro creates a select expression with one entry per top containing the `attr_name` attribute.
  The value for each top is `fn(<attr value>)` and if `fn` is not provided, it defaults to simply copying the attribute value.
  Furthermore, if `required` is set to `True`, the select expression will not match any top not containing the value (hence giving an error if trying to use it for such a top).
  If `required` is set to `False`, then a default entry will be a added that returns the value `default`.
- Sometimes, one only wants to test the existence of an attribute, in which case `opentitan_if_top_attr(attr_name, obj, default)` is sufficient.
  It creates a select expression that evaluates to `obj` for top with the `attr_name` attribute, and to `default` for the others.
- It is sometimes necessary to mark target as compatible only with top providing a certain attribute. This can be done using `opentitan_require_top_attr(attr_name)`.
- Finally, a very common case is when an attribute is simply a label string and we want to create an alias to this target.
  This can be done using `opentitan_alias_top_attr(name, attr_name, required = True, default = None, fn = None)` which works similarly to `opentitan_select_top_attr` but creates an `alias` target instead.

A similar set of API exists for IP attributes, see `opentitan_select_ip_attr`, `opentitan_if_ip_attr` and `opentitan_require_ip_attr`.

### Examples

#### A simple top label

Consider the case where we want to add a new `ast_init` attribute to the Darjeeling top.
This attribute should be a label string to a `cc_library` that is used to initialize the AST registers in a top-specific manner.
We start by creating a new file in `hw/top_darjeeling/sw`:
```c
// In hw/top_darjeeling/sw/ast_lib.c

void ast_init(void) {
  // Some top-specific code.
}
```
Next, we create a `cc_library` in `hw/top_darjeeling/sw/BUILD`:
```py
# In hw/top_darjeeling/sw/BUILD
cc_library(
    name = "ast_lib",
    srcs = ["ast_lib.c"],
)
```
Now we can add an attribute to the top:
```py
DARJEELING = opentitan_top(
    name = "earlgrey",
    # ...
    # NEW:
    ast_lib = "//hw/top_darjeeling/sw:ast_lib",
)
```
The attribute is now registered but still unused.
Maybe we want to use in the test ROM for example, and default to a stub implementation if the top does not provide a library.
We start by creating a stub implementation in `sw/device/lib/testing/test_rom/`:
```c
// In sw/device/lib/testing/test_rom/ast_lib_stub.c

void ast_init(void) {
  // Stub: does nothing.
}
```
We then add a new stub library in `sw/device/lib/testing/test_rom/BUILD` and use it:
```py
# NEW: load the required macro
load(
    "//hw/top:defs.bzl",
    "opentitan_select_top_attr",
)

# In sw/device/lib/testing/test_rom/BUILD
cc_library(
    name = "ast_lib_stub",
    srcs = ["ast_lib_stub.c"],
)

# ...
cc_library(
    name = "test_rom_lib",
    # ...
    deps = [
        #...
    ] + # NEW: we select either the library if it is available, or the stub otherwise.
        opentitan_select_top_attr("ast_lib", required = False, default = ":ast_lib_stub"),
)
```
Note that in this particular case, since `ast_lib` is just a label-string, we can use the convenience macro `opentitan_alias_top_attr` to create a target:
```py
# Alternative to the above for simple label-string attributes
load(
    "//hw/top:defs.bzl",
    "opentitan_alias_top_attr",
)

# In sw/device/lib/testing/test_rom/BUILD
cc_library(
    name = "ast_lib_stub",
    srcs = ["ast_lib_stub.c"],
)

# Create an alias target to the top ast_lib, or default to the stub if not available.
opentitan_alias_top_attr(
    name = "ast_lib",
    required = False,
    default = ":ast_lib_stub",
)

# ...
cc_library(
    name = "test_rom_lib",
    # ...
    deps = [
        # Here we directly use the target.
        ":ast_lib",
    ]
)
```
