# Changelog

All notable changes to this crate will be documented in this file.

The format is based on Keep a Changelog, with an `Unreleased` section for work in progress and versioned entries for published releases.

## [Unreleased]

### Changed

- Standardized rustdoc on the public inherent `InplaceString` and `InplaceVector` APIs to explicitly document panic behavior, and to clarify closure-driven panic behavior where relevant.

## [0.3.5] - 2026-03-19

### Added

- Added `InplaceString::drain`, which removes a byte range on char boundaries and yields the removed characters.
- Added coverage for `InplaceString::drain`, including partial-consumption, reverse iteration, and panic cases.

### Changed

- Updated README examples to prefer the `inplace_vec!` and `inplace_string!` macros for construction.
- Clarified the `InplaceString` UTF-8 safety note in the README.
- Refined README example comments to focus on inline-capacity behavior specific to this crate.
