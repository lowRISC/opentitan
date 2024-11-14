# Ipgen: Generate IP Blocks From IP Templates

Ipgen is a tool to produce IP blocks from IP templates.

IP templates are highly customizable IP blocks which are pre-processed to render blocks that can be used in a hardware design.
The templates of the source files are written in the Mako templating language, and are rendered by the ipgen tool to become the actual source files.
The templates can be customized through template parameters, which are available within the templates.

Ipgen is a command-line tool and a library.
Users wishing to instantiate an IP template or query it for template parameters will find the command-line application useful.
For use in higher-level scripting, e.g. within [topgen](../topgen/README.md) using ipgen as Python library is recommended.

## Anatomy of an IP template

An IP template is a directory with a well-defined directory layout, which mostly mirrors the standard layout of IP blocks.

An IP template directory has a well-defined structure:

* The IP template name (`<templatename>`) equals the directory name.
* The directory contains a template description file `data/<templatename>.tpldesc.hjson` containing descriptions of the configurable parameters.
  The "default" field of these descriptions are expected to be overriden via the actual configuration parameters.
* The directory also contains some files ending in `.tpl`.
  These files are Mako templates and are rendered into a file in the same relative location without the `.tpl` file extension.

### The template description file

Each IP template comes with a description itself.
This description is contained in the hjson file `data/<templatename>.tpldesc.hjson` in the template directory.

It contains a list of parameter objects.
These objects are dictionaries with the following required keys:

* `name` (string): Name of the template parameter.
* `desc` (string): Human-readable description of the template parameter.
* `type` (string): Data type of the parameter. Valid values: `bool`, `int`, `str`, `object`.
* `default` (bool|string|int|dict): The default value of the parameter.
  The type of this should match the `type` argument.
  For convenience, strings are converted into integers on demand (if possible).

#### Example template description file

An exemplary template description file with two parameters, `src` and `target` is shown below.

```hjson
// data/<templatename>.tpldesc.hjson
{
  template_param_list: [
    {
      name: "src"
      desc: "Number of Interrupt Source"
      type: "int"
      default: "32"
    }
    {
      name: "target"
      desc: "Number of Interrupt Targets"
      type: "int"
      default: "32"
    }
  ]
}
```

### Source file templates (`.tpl` files)

Templates are written in the [Mako templating language](https://www.makotemplates.org/).
All template parameters are available in the rendering context.
For example, a template parameter `src` can be used in the template as `${src}`.

### VLNV support

The `instance_vlnv` function is available to process VLNV strings, which is useful for template core files.
A VLNV string has the form vendor:library:name[:version] where the version is optional.
The `instance_vlnv` function is given a vlnv and outputs a transformed vlnv as follows:

- The vendor string becomes `lowrisc`.
- The library string becomes `opentitan`.
- The name is processed as follows:
  - If the `module_instance_name` parameter exists, the name must start
    with it as a prefix, and that is replaced by the `instance_name`
    renderer value.
  - If the name starts with the template name, it is replaced by the
    `instance_name` value.
  - Otherwise the `instance_name` is pefixed to the name.
- The optional version is preserved.

For example, a `rv_plic.core.tpl` file could look like this:

```yaml
CAPI=2:
name: ${instance_vlnv("lowrisc:ip:rv_plic")}
```

After processing, the VLNV could become `lowrisc:opentitan:top_earlgrey_rv_plic`.

The following rules should be applied when creating IP templates:

* Template and use an instance-specific name for all FuseSoC cores which reference templated source files (e.g. SystemVerilog files).
* Template and use an instance-specific name at least the top-level FuseSoC core.
* If a FuseSoC core with an instance-specific name exposes a well-defined public interface (see below), add a `virtual: lowrisc:ip_interfaces:<name>` line to the core file to allow non-instance-specific cores to refer to it without knowing the actual core name.

#### Templating core files to uphold the "same name, same interface" principle

FuseSoC core files should be written in a way that upholds the principle "same name, same public interface", i.e. if a FuseSoC core has the same name as another one, it must also provide the same public interface.

Since SystemVerilog does not provide strong control over which symbols become part of the public API, developers must carefully evaluate their source code.
At least, the public interface is comprised of
- module header(s), e.g. parameter names, ports (names, data types),
- package names, and all identifiers within it, including enum values (but not the values assigned to them),
- defines

If any of those aspects of a source file are templated, the core name referencing the files must be made instance-specific.

## Library usage

Ipgen can be used as Python library by importing from the `ipgen` package.
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

## `ipgen generate`

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

## `ipgen describe`

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
However, it is not possible to use one IP block template to produce two different flash controllers with different template parameters.

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
