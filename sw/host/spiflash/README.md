# SPI Flash

`spiflash` is a tool used to update the firmware stored in OpenTitan's flash.
The tool resets OpenTitan and signals the boot ROM to enter bootstrap mode
before sending the update payload.

Currently, the tool only supports Verilator targets.

## Build instructions

`spiflash` is written in C++17.

Required packages:

```shell
$ sudo apt-get install libssl-dev libftdi1-dev
```

Build command:

```shell
$ cd ${REPO_TOP}/util/spiflash
$ make clean && make
```

## Run the tool in Verilator

Build boot_rom:

```shell
$ cd ${REPO_TOP}/sw/boot_rom
$ make clean && make SIM=1
```

Build and run Verilator with boot_rom enabled:

```shell
$ cd ${REPO_TOP}
$ fusesoc --cores-root . sim --build-only lowrisc:systems:top_earlgrey_verilator
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --rominit=sw/boot_rom/boot_rom.vmem
```

Build hello_world program:

```shell
$ cd ${REPO_TOP}/sw/examples/hello_world
$ make clean && make SIM=1
```

Run spiflash. In this example we use SPI device `/dev/pts/3` as an example.
After the transmission is complete, you should be able to see the hello_world
output in the UART console.

```shell
$ cd ${REPO_TOP}/util/spiflash
$ make clean && make
$ ./spiflash --input=../../sw/examples/hello_world/hello_world.bin --verilator=/dev/pts/3
```

## TODOs

- Implement ACK handshake between boot_rom and spiflash.
- Add support for FPGA targets via FTDI interface.
