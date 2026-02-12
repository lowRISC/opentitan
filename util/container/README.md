# Docker Container

Docker container based on the Claude Code sandbox image, containing various
hardware and software development tools for OpenTitan, as listed in the
[OpenTitan documentation](../../doc/getting_started/README.md).

The container integrates Claude Code with the full OpenTitan development
toolchain and an open-source FPGA bitstream flow.

## Local Build Instructions

First, you'll need to install Docker either through your package manager or
their [download page](https://www.docker.com/get-started/). You'll also need
to clone the [OpenTitan repository](https://github.com/lowRISC/opentitan) if
you haven't done that yet.

Then, from `$REPO_TOP` (the top-level directory in the repository, called
`opentitan` by default), you can build the container with:

```shell
$ sudo docker build -t opentitan-claude -f util/container/Dockerfile .
```

## Using the Container

### With Claude Code (default)

The default `CMD` starts a tmux session running Claude Code:

```shell
docker run -t -i \
  -v $(pwd):/workspace/opentitan \
  opentitan-claude:latest
```

### Interactive shell

To get a regular shell instead:

```shell
docker run -t -i \
  -v $(pwd):/workspace/opentitan \
  opentitan-claude:latest \
  bash
```

The container runs as the `agent` user (from the Claude Code sandbox base
image). You can use `sudo` within the container to gain root permissions.

## Included Tools

The container bundles:

- **Claude Code**: AI-assisted development (runs as default CMD)
- **OpenTitan toolchain**: RISC-V toolchain, Verilator, Verible, Clang 16, Bazelisk
- **Sandbox extras**: Docker CLI, GitHub CLI, Node.js, Go, Python 3, Git, ripgrep, jq, .NET 8.0

## Open-Source FPGA Toolchain

The container includes open-source tools for building CW310 (Kintex-7 XC7K410T)
bitstreams without Vivado:

| Tool | Purpose | Path |
|------|---------|------|
| [Yosys](https://github.com/YosysHQ/yosys) | RTL synthesis (`synth_xilinx -family xc7`) | `/tools/yosys/bin/yosys` |
| [sv2v](https://github.com/zachjs/sv2v) | SystemVerilog to Verilog conversion | `/tools/sv2v/bin/sv2v` |
| [nextpnr-xilinx](https://github.com/openXC7/nextpnr-xilinx) | Place & route for Xilinx 7-series | `/tools/nextpnr-xilinx/bin/nextpnr-xilinx` |
| [Project X-Ray](https://github.com/f4pga/prjxray) | Bitstream generation for 7-series | `/tools/prjxray/build/tools/` |
| [openFPGALoader](https://github.com/trabucayre/openFPGALoader) | JTAG/SPI FPGA programming | `/tools/openFPGALoader/bin/openFPGALoader` |

### Generating the Chip Database

Before running place & route, you must generate the nextpnr-xilinx chip
database for the CW310's XC7K410T. This is not done during the Docker build
because it requires significant time (~1-2 hours) and memory (~16-32 GB):

```shell
cd /tools/nextpnr-xilinx/share/python
pypy3 bbaexport.py --device xc7k410tffg676-1 \
    --bba /tools/nextpnr-xilinx/share/xc7k410t.bba
bbasm --l /tools/nextpnr-xilinx/share/xc7k410t.bba \
    /tools/nextpnr-xilinx/share/xc7k410t.bin
```

The resulting `.bin` file can be persisted on a host volume to avoid
regenerating it each time.

See `PLAN_opensource_cw310_bitstream.md` in the repository root for the
complete open-source bitstream build flow.
