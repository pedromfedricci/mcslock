# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

[Unreleased]: https://github.com/pedromfedricci/mcslock/compare/v0.3.0..HEAD

## [0.3.0] - 2024-07-29

### Changed

- **BREAKING**: Require `unsafe` for `Relax`. `Relax` no longer requires `Default`.
  `Relax` now requires implementing the `new` function. All types under the
  `relax` module no longer implement `Default` ([#14]).

- **BREAKING**: `barging::Mutex` has now two generic parameters for relax
  strategies as oppose to one: `Rs` and `Rq` ([#15]).

- **BREAKING**: The root level `lock_api` module has been moved under the `barging`
  module ([#16]).

[#14]: https://github.com/pedromfedricci/mcslock/pull/14
[#15]: https://github.com/pedromfedricci/mcslock/pull/15
[#16]: https://github.com/pedromfedricci/mcslock/pull/16

## [0.2.0] - 2024-04-09 [YANKED]

### Yanked

- Please use 0.3.0, see [#14].

### Added

- **BREAKING**: Add new thread_local locking design ([#11]).

[#11]: https://github.com/pedromfedricci/mcslock/pull/11

### Removed

- **BREAKING**: Remove MutexNode reexports ([#12]).

[#12]: https://github.com/pedromfedricci/mcslock/pull/12

## [0.1.2] - 2024-03-24 [YANKED]

### Yanked

- Please use 0.3.0, see [#11] and [#14].

### Added

- Add Default impl for MutexNode ([#10]).

[#10]: https://github.com/pedromfedricci/mcslock/pull/10

### Fixed

- Unbound R from Send/Sync when implementing Send/Sync ([`fda47a7`]).

[`fda47a7`]: https://github.com/pedromfedricci/mcslock/commit/fda47a7195d0a74f215cfa8fd0d41f1ffd0c9bea

## [0.1.1] - 2024-01-05 [YANKED]

### Yanked

- Please use 0.3.0, see [#11] and [#14].

### Added

- New unchecked locking APIs for `thread_local::Mutex` ([#9]).
- Track caller location when `thread_local::Mutex` panics ([#9]).

[#9]: https://github.com/pedromfedricci/mcslock/pull/9

## [0.1.0] - 2023-12-14 [YANKED]

### Yanked

- Please use 0.3.0, see [#11] and [#14].

### Added

- Initial release.

