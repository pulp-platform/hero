# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/), and this project adheres to
[Semantic Versioning](http://semver.org).

## v1.3.0 - 2018-10-17

Added support for CI testing based on `plptest` framework.

### Added
- `*/testset.cfg`: add tests configuration file;

### Changed
- `*/Makefile`: `default.mk` include is now based on absolute path.


## v1.2.1 - 2018-10-2

### Changed

- Rename `make.inc` in `common/default.mk`.

## v1.2.0 - 2018-09-25

### Added
- Add top level `Makefile` for CI and automatic test generation.

### Changed
- In `make.inc`:
  - Remove useless PULP-related `CFLAGS`.
  - Enable `run` and `clean` rules to be extended (i.e., make them double-colon rules).

### Fixed
- Add `omp.h` to all applications after fixing [#22](https://github.com/pulp-platform/hero-sdk/issues/22) in the HERO SDK.


## v1.1.0 - 2018-09-18

### Added
- Add sobel-filter application.

## v1.0.1 - 2018-09-17

### Fixed
- Add license header to all C files.
- Ensure that remote directory exists during `make install`.
- `common/bench.h:` Add missing include guard.


## v1.0.0 - 2018-09-14

Initial public release
