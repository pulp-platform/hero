# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

### Changed
- Decreased `timeunit` and `timeprecision` to 1ps.  This makes it possible to simulate designs
  clocked at periods lower than 1ns.  For simulators that do not respect units in `time` parameters,
  this change is breaking.

## v0.1.1 - 2019-02-26

### Fixed
- Move all files into the `simulation` target. This precludes synthesis of files in this package
  when this package is included as dependency.

## v0.1.0 - 2019-02-25

### Added
- Add standalone clock and reset generator.
- Add randomizing synchronous driver and holdable driver.
- Add randomizing stream master and slave.
- Add ID queue with randomizing output.
- Add `rand_verif_pkg` with task to wait for a random number (within interval) of clock cycles.
