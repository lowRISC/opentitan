# Docker Container

Docker container based on Ubuntu 22.04 LTS containing various hardware and
software development tools for OpenTitan, as listed in the
[OpenTitan documentation](../../doc/getting_started/README.md).

## Local Build Instructions

For now, no pre-built containers are available; you'll need to build the Docker container locally.
First, you'll need to install Docker either through your package manager or their [download page](https://www.docker.com/get-started/).
You'll also need to clone the [OpenTitan repository](https://github.com/lowRISC/opentitan) if you haven't done that yet.
Then, from `$REPO_TOP` (the top-level directory in the repository, called `opentitan` by default), you can build the container with:

```shell
$ sudo docker build -t opentitan -f util/container/Dockerfile .
```

## Using the Container

Run the container with `docker run`, mapping the current working directory to
`/home/dev/src`. The user `dev` will have the same user ID as the current user
on the host (you!), causing all files created by the `dev` user in the container
to be owned by the current user on the host.

If you'd like to initialize your shell environment in a specific way, you can
pass an environment variable `USER_CONFIG=/path/to/a/script.sh`. Otherwise,
remove the `--env USER_CONFIG` argument from the invocation shown below.

The script passed through this mechanism will be sourced. The path of the script
must be within the container, e.g. in the OpenTitan repository directory.

```
docker run -t -i \
  -v $(pwd):/home/dev/src \
  --env DEV_UID=$(id -u) --env DEV_GID=$(id -g) \
  --env USER_CONFIG=/home/dev/src/docker-user-config.sh \
  opentitan:latest \
  bash
```

You can use `sudo` within the container to gain root permissions.

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
