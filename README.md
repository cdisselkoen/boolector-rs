# boolector

[![Crates.io](https://img.shields.io/crates/v/boolector.svg)](https://crates.io/crates/boolector)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/cdisselkoen/boolector-rs/master/LICENSE)

Safe high-level bindings for the [Boolector] SMT solver, version 3.0.0.

## Installation

This crate is on [crates.io](https://crates.io/crates/boolector), so you can
simply add it as a dependency in your `Cargo.toml`:
```toml
[dependencies]
boolector = "0.1.0"
```

This crate relies on the [`boolector-sys`] crate, so you will need to follow
its directions for installation as well. In particular, Boolector 3.0.0 must
be available on the system as a shared library.

[Boolector]: https://boolector.github.io
[`boolector-sys`]: https://crates.io/crates/boolector-sys

## Documentation

Full documentation, including examples, can be found at
[https://docs.rs/boolector](https://docs.rs/boolector).

## Caveats

These bindings are not necessarily complete; there may be some features
present in [`boolector-sys`] which are not directly exposed here, e.g.,
uninterpreted functions (`boolector_uf()`). Contributions are welcome.
