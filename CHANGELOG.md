# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

[Unreleased]: https://github.com/pedromfedricci/mcslock/compare/v0.1.2..HEAD

## [0.1.2] - 2024-03-24

### Added

- Add Default impl for MutexNode ([#10]).

[#10]: https://github.com/pedromfedricci/mcslock/pull/10

### Fixed

- Unbound R from Send/Sync when implementing Send/Sync ([`fda47a7`]).

[`fda47a7`]: https://github.com/pedromfedricci/mcslock/commit/fda47a7195d0a74f215cfa8fd0d41f1ffd0c9bea

## [0.1.1] - 2024-01-05

### Added

- New unchecked locking APIs for `thread_local::Mutex` ([#9]).
- Track caller location when `thread_local::Mutex` panics ([#9]).

[#9]: https://github.com/pedromfedricci/mcslock/pull/9

## [0.1.0] - 2023-12-14

### Added

- Initial release.

