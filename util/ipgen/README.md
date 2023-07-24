# ipgen: Generate IP blocks from IP templates

ipgen is a tool to produce specialized IP blocks from IP templates.

IP templates are highly customizable IP blocks which need to be pre-processed before they can be used in a hardware design.
Templates of source files, written in the [Mako templating language](https://www.makotemplates.org/), are converted into "real" source files by a pre-processing step which is performed by the ipgen tool.
We refer to this step as "rendering", a term which is borrowed from the Mako project and other templating frameworks.
"Rendering" takes a set of argument parameters and uses them to resolve all template parameters defined by the template.
The result of this process is normally written back to disk as a complete IP block, ready to be instantiated in a design.

Creating a completely unique instance of a template is not a trivial task.
This is known as "uniquification", and is a common problem to be overcome in IP management for SoC integrators.
We need to consider challenges such as symbol namespace resolution and compilation unit scoping in downstream tooling.
As an example, a C++ compiler can use name mangling as one way to achieve uniquification.
See the [Limitations](#limitations) section below for details of what cannot currently be achieved with the ipgen tool.

ipgen is a command-line tool and a library.
Users wishing to instantiate an IP template or query it for template parameters will find the command-line interface to ipgen useful.
For use in higher-level scripting flows (e.g. within [topgen](../topgen/README.md)), using ipgen as a Python library is recommended.

## Anatomy of an IP template

An IP template is a directory with a well-defined layout. It is structured as follows:

* The directory name must equal the IP template name (`<templatename>`).
* The directory must contain a [Template description file](#template-description-file-tpldeschjson).\
  This file, located at `data/<templatename>.tpldesc.hjson`, contains all configuration information related to the template.
* The directory may contain [templated files](#source-file-templates-tpl-files) with the extension `.tpl`.\
  These files are [Mako](https://www.makotemplates.org/) templates, which are rendered into source files at the same relative paths in the output directory.

The rendering process recursively copies all files which are not templates directly to the output directory, and applies the template parameters to [templated files](#source-file-templates-tpl-files) to create specialized source files in the same relative locations in the output directory (but with the `.tpl` file extension removed).
Hence, the outputted IP block directory has a very similar structure to the IP template directory.

### Template description file (`.tpldesc.hjson`)

Each IP template comes with a description file, located at `data/<templatename>.tpldesc.hjson` in the template directory.
The file is written in [hjson](https://hjson.github.io/).

The description file is used to define the template parameters used by `.tpl` templated files within the directory.
When rendering a template, values for each of these parameters can be passed to the tool to specialize the generated block.
Each template parameter may also specify a default value to use if no input is given for that parameter.

The '.tpldesc.hjson' file is structured as a single top-level object (*dictionary*), with a single key `template_param_list`.
The value of `template_param_list` is an array (*list*) of template parameters, each of which is an object with the key/values defined in [the following section](#list-of-template-parameters-template_param_list).

#### List of template parameters (`template_param_list`)

Keys within `template_param_list`:

* `name` (string): Name of the template parameter.
* `desc` (string): Human-readable description of the template parameter.
* `type` (string): Data type of the parameter. Valid values: `int`, `str`
* `default` (string|int): The default value of the parameter. The data type should match the `type` argument. As convenience, strings are converted into integers on demand (if possible).

##### Special parameters

If an IP Template defines a special parameter called `module_instance_name`, ipgen can use this value to perform a basic uniquification of the block.
This can be used as a 'Manual Approach' to uniquification by a template author.
(See the [Limitations](#limitations) section for discussion about different approaches to uniquification.)

With this approach, "module_instance_name" can be used as a standard templated variable throughout the template, everywhere a unique name may be required.
The value for "module_instance_name" given to ipgen will then be inserted in the normal rendering process.
In addition, ipgen will perform the following steps:
- Rewrite the filenames of all `.tpl` templated files, replacing `<template_name>` with `<module_instance_name>`.

By using the value of "module_instance_name" when constructing the `IpConfig` object and invoking `IpBlockRenderer.render()`), it is also possible to:
- Use `<module_instance_name>` as the instance name for the block.
- Change the output directory to `ip_autogen/<module_instance_name>`

This approach is currently implemented in the `hw/ip_templates/rv_plic` template, but for the Earl Grey top the default value ("rv_plic") for the `module_instance_name` is used and this effectively becomes a noop.

#### Example file

An example template description file with two parameters `src` and `target` is shown below.

```hjson
// data/<templatename>.tpldesc.hjson
{
  "template_param_list": [
    {
      "name": "src",
      "desc": "Number of Interrupt Sources",
      "type": "int",
      "default": "32"
    },
    {
      "name": "target",
      "desc": "Number of Interrupt Targets",
      "type": "int",
      "default": "32"
    },
  ],
}
```

### Source file templates (`.tpl` files)

Templates are written in the [Mako templating language](https://www.makotemplates.org/).
All template parameters are available in the rendering context.
For example, a template parameter `src` can be used in the template as `{{ src }}`.

Furthermore, the following functions are available:

* `instance_vlnv(vlnv)`: Transform a FuseSoC core name, expressed as VLNV string, into an instance-specific name.
  The `vendor` is set to `lowrisc`, the `library` is set to `opentitan`, and the `name` is prefixed with the instance name.
  The optional version segment is retained.
  Use this function on the `name` of all FuseSoC cores which contain sources generated from templates and which export symbols into the global namespace.

## Templating FuseSoC core files (`.core` files)

FuseSoC core files can be templated just like any other file.

The following rules should be applied when creating IP templates of FuseSoC `.core` files:

* Use instance-specific names for all FuseSoC cores which reference templated source files (e.g. SystemVerilog files).
* Use an instance-specific name for the top-level FuseSoC core at a minimum.
* If a FuseSoC core with an instance-specific name exposes a well-defined public interface (see below), add a `provides: lowrisc:ip_interfaces:<name>` line to the core file to allow other cores to refer to it without knowing the actual core name.

### `instance_vlnv()` template function

The ipgen tool defines a handy helper template function `instance_vlnv()`, which transforms a placeholder VLNV (a string in the form `vendor:library:name:version`) into a instance-specific one.

For example, a `rv_plic.core.tpl` file could use the `instance_vlnv()` function like this:

```yaml
CAPI=2:
name: ${instance_vlnv("lowrisc:ip:rv_plic")}
```

After processing, the `name` in the rendered output file will be set to `lowrisc:opentitan:top_earlgrey_rv_plic`.

### "same name, same interface" principle

FuseSoC core files should be written in a way that upholds the principle "same name, same public interface", i.e. if a FuseSoC core has the same name as another one, it must also provide the same public interface.

Since SystemVerilog does not provide no strong control over which symbols become part of the public API developers must be carefully evaluate their source code.
At least, the public interface is comprised of
- module header(s), e.g. parameter names, ports (names, data types),
- package names, and all identifiers within it, including enum values (but not the values assigned to them),
- defines

If any of those aspects of a source file are templated, the core name referencing the files must be made instance-specific.

## Library usage

ipgen can be used as a Python library by importing from the `ipgen` package.
Refer to the comments within the source code for usage information.

The following example shows how to produce an IP block from an IP template.

```python
from pathlib import Path
from ipgen import IpConfig, IpTemplate, IpBlockRenderer

# Load the template
ip_template = IpTemplate.from_template_path(Path('a/ip/template/directory'))

# Prepare the IP template configuration
params = {}
params['src'] = 17
ip_config = IpConfig("my_instance", params)

# Produce an IP block
renderer = IpBlockRenderer(ip_template, ip_config)
renderer.render(Path("path/to/the/output/directory"))
```

The output produced by ipgen is determined by the chosen renderer.
For most use cases the `IpBlockRenderer` is the right choice, as it produces a full IP block directory.
Refer to the `ipgen.renderer` module for more renderers available with ipgen.

## Command-line usage

The ipgen command-line tool lives in `util/ipgen.py`.
The first argument is typically the action to be executed.

```console
$ cd $REPO_TOP
$ util/ipgen.py --help
usage: ipgen.py [-h] ACTION ...

optional arguments:
  -h, --help  show this help message and exit

actions:
  Use 'ipgen.py ACTION --help' to learn more about the individual actions.

  ACTION
    describe  Show details about an IP template
    generate  Generate an IP block from an IP template
```

### `ipgen generate`

```console
$ cd $REPO_TOP
$ util/ipgen.py generate --help
usage: ipgen.py generate [-h] [--verbose] -C TEMPLATE_DIR -o OUTDIR [--force] [--config-file CONFIG_FILE]

Generate an IP block from an IP template

optional arguments:
  -h, --help            show this help message and exit
  --verbose             More info messages
  -C TEMPLATE_DIR, --template-dir TEMPLATE_DIR
                        IP template directory
  -o OUTDIR, --outdir OUTDIR
                        output directory for the resulting IP block
  --force, -f           overwrite the output directory, if it exists
  --config-file CONFIG_FILE, -c CONFIG_FILE
                        path to a configuration file
```

### `ipgen describe`

```console
$ cd $REPO_TOP
$ util/ipgen.py generate --help
usage: ipgen.py describe [-h] [--verbose] -C TEMPLATE_DIR

Show all information available for the IP template.

optional arguments:
  -h, --help            show this help message and exit
  --verbose             More info messages
  -C TEMPLATE_DIR, --template-dir TEMPLATE_DIR
                        IP template directory
```

## Limitations

### Changing the IP block name is not supported

Every IP block has a name, which is reflected in many places: in the name of the directory containing the block, in the base name of various files (e.g. the Hjson files in the `data` directory), in the `name` key of the IP description file in `data/<ipname>.hjson`, and many more.

To "rename" an IP block, the content of multiple files, and multiple file names, have to be adjusted to reflect the name of the IP block, while keeping cross-references intact.
Doing that is possible but a non-trivial amount of work, which is currently not implemented.
This limitation is of lesser importance, as each template may be used only once in every toplevel design (see below).

What is supported and required for most IP templates is the modification of the FuseSoC core name, which can be achieved by templating relevant `.core` files (see above).

### Each template may be used only once per (top-level) design

Each template may be used to generate only once IP block for each top-level design.
The generated IP block can still be instantiated multiple times from SystemVerilog, including with different SystemVerilog parameters passed to it.
It is not possible, however, to, for example, use one IP block template to produce two different flash controllers with different template parameters.

IP templates generally contain code which exports symbols into the global namespace of the design: names of SystemVerilog modules and packages, defines, names of FuseSoC cores, etc.
Such names need to be unique for each design, i.e. we cannot have multiple SystemVerilog modules with the same name in one design.
To produce multiple IP blocks from the same IP template within a top-level design, exported symbols in generated IP blocks must be made "unique" within the design.
Making symbols unique can be either done manually by the author of the template or automatically.

In the manual approach, the template author writes all global identifiers in templates in a unique way, e.g. `module {prefix}_flash_ctrl` in SystemVerilog code, and with similar approaches wherever the name of the IP block is used (e.g. in cross-references in `top_<toplevelname>.hjson`).
This is easy to implement in ipgen, but harder on the IP template authors, as it is easy to miss identifiers.

In the automated approach, a tool that understands the source code transforms all identifiers.
C++ name mangling uses a similar approach.
The challenge is, however, to create a tool which can reliably do such source code transformations on a complex language like SystemVerilog.

Finally, a third approach could be a combination of less frequently used/supported SystemVerilog language features like libraries, configs, and compilation units.
