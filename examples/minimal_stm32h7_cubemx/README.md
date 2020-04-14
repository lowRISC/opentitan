# Minimal stm32hu cubemx project
This is an example project to demonstrate how to use stm32cubemx projects with bazel. 

## Setup
Setting up your project from the cubemx code generator is relatively straight forward. First setup up your project as usual but before you generate your code take the following steps;

### Set up your code generation as if you where using the 'make' build configuration. (Optional)
This step is useful if you would like to automatically generate your linker script. Switch to the 'Project Manager' tab in Cubemx and under 'Project Settings'->'Toolchain/IDE' select Makefile. 

### Set up your code generation to only generate the files that you need for your project
By default cubemx will copy a few hundred megabytes of code into your project. This code is the entire HAL and LL drivers + middleware. At the moment this can be handled by bazel significantly reducing the size of your repository. To do this under the 'Project Manager'->'Code Generator'->'STM32Cube MCU Packages and embedded software packs' check the 'add neccesary library files as references in the toolchain project configuration'. After this you should have a project tree that looks something like this.


```
├── Inc
│   ├── main.h
│   ├── stm32h7xx_hal_conf.h
│   └── stm32h7xx_it.h
├── Makefile
├── minimal-cubemx-test.ioc
├── README.md
├── Src
│   ├── main.c
│   ├── stm32h7xx_hal_msp.c
│   ├── stm32h7xx_it.c
│   └── system_stm32h7xx.c
├── startup_stm32h743xx.s
├── STM32H743XIHx_FLASH.ld
```

### Adding the bazel WORKSPACE and BUILD files