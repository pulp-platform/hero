# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/), and this project adheres to
[Semantic Versioning](http://semver.org).

## v1.1.0 - 2018-09-13
### Added
- Add function to reset statically allocated data structures in L1.

## v1.0.1 - 2018-09-13
### Fixed
- Allocate TLB entry replacement pointers in L1 instead of L2 memory.  This reduces the access
  latency to these frequently used pointers.

## v1.0.0 - 2018-08-10

Initial public release
