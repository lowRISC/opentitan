# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Optional wrapper `dm_obi_top.sv` that wraps `dm_top` providing an OBI compliant interface
- `tb` that runs dm in conjunction with ri5cy and OpenOCD
- `.travis-ci.yml` running `tb` with verilator

### Changed
- Made second scratch register optional (default is two) from [@zarubaf](https://github.com/zarubaf

### Fixed
- Off-by-one error in data and progbuf end address from [@pbing](https://github.com/pbing)
- Haltsum1-3 calculation

## [0.3.0] - 2020-01-23

### Added
- Documentation in `doc/` from [@imphil](https://github.com/imphil)

### Changed
- Various linting issues and cleanups from [@msfschaffner](https://github.com/msfschaffner)

### Fixed
- Corruption on debug exception entry [@tomroberts-lowrisc](https://github.com/tomroberts-lowrisc)
- truncation of `selected_hart`

## [0.2.0] - 2019-08-16

## Added
- Add Bender.yml

### Fixed
- Fix haltsum1, haltsum2 and haltsum3
- Fix minor linter issues

## [0.1.0] - 2019-05-18

### Added
- Parametrize buswidth to support 32-bit and 64-bit cores
- Support arbitrary base addresses in debug ROM
- Add misc helper functions to facilitate code generation
- Add README
- Fork from Ariane

### Changed
- Allow generic number of data registers
- Make JTAG IDCODE parametrizable

### Removed
- Remove ariane specific packages

### Fixed
- Fix resumeack and resumereq behaviour to be cleared and set according to debug
  specification
- Add missing JTAG test logic reset handling
- Fix resume logic in multihart situations
- Fix missing else(s) in system bus access
- Fix bad transitions into program buffer
- Fix error handling when using unsupported abstract commands
- Prevent harts from being in multiple states
- Fix various style issues
