# boolector

[![crates.io](https://img.shields.io/crates/v/boolector.svg)](https://crates.io/crates/boolector)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/cdisselkoen/boolector-rs/main/LICENSE)

Safe high-level bindings for the [Boolector] SMT solver, version 3.2.2.

## Installation

This crate is on [crates.io](https://crates.io/crates/boolector), so you can
simply add it as a dependency in your `Cargo.toml`:
```toml
[dependencies]
boolector = "0.4.3"
```

This crate relies on the [`boolector-sys`] crate, so you will need to follow
its directions for installation as well. In particular, you can either:
  - compile and install Boolector 3.2.2 on your system as a shared library; or
  - activate the `vendor-lgl` feature on this crate, which will automatically
    build a static Boolector and link to it. E.g.,
    ```toml
    [dependencies]
    boolector = { version = "0.4.3", features = ["vendor-lgl"] }
    ```
For more details, see the [`boolector-sys`] README.

[Boolector]: https://boolector.github.io
[`boolector-sys`]: https://crates.io/crates/boolector-sys

## Documentation

Full documentation, including examples, can be found at
[https://docs.rs/boolector](https://docs.rs/boolector).

## Caveats

These bindings are not necessarily complete; there may be some features
present in [`boolector-sys`] which are not directly exposed here, e.g.,
uninterpreted functions (`boolector_uf()`). Contributions are welcome.

This crate currently requires Rust 1.41+.
