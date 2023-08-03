# Unofficial Setup Guide for Fedora

This is an unofficial guide detailing how to set up a Fedora system for OpenTitan development.
This guide differs from the main guide only in step 2.

## Step 2: Install dependencies using the package manager

Fedora uses a different package manager than the officially supported Ubuntu development environment.
You can install equivalent packages to the `apt-requirements.txt` file with the following command:

```shell
sudo dnf install autoconf bison make automake gcc gcc-c++ kernel-devel \
         clang-tools-extra clang cmake curl \
         doxygen flex g++ git golang lcov elfutils-libelf \
         libftdi libftdi-devel ncurses-compat-libs openssl-devel \
         systemd-devel libusb redhat-lsb-core \
         make ninja-build perl pkgconf python3 python3-pip python3-setuptools \
         python3-urllib3 python3-wheel srecord tree xsltproc zlib-devel xz clang-tools-extra \
         clang11-libs clang-devel elfutils-libelf-devel
```
