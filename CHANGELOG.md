# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog], and this project adheres to [Semantic Versioning].

## [0.2.0] - 2023-02-06

### Added

- This changelog
- README links to the sources for the `analyze` and `generate` examples
- README description of the `outcome_map.rmp` file
- Rustdoc examples for _most_ `pub` items ([C-EXAMPLE])
- Rustdoc examples for `std::ops` trait `impl`s for `Ally` and `AllySet`
- `std::iter` trait `impl`s for `allyset::IntoIter`
  - `DoubleEndedIterator`
  - `ExactSizeIterator`
  - `FusedIterator`
- Unit tests for `AllySet` symmetric difference and `allyset::IntoIter`
- `impl Extend<Ally> for AllySet` ([C-COLLECT])

### Changed

- Moved `AllySet` from the `ally` module into `allyset`.
- Moved/renamed `ally::AllySetIter` to `allyset::IntoIter` ([C-ITER-TY]).
- Changed `AllySet` rustdoc examples to consistently `use Ally::*` for brevity/readability.
- Clarified the _Panics_ section of the rustdoc for `death::get_defense_victims`.
- Replaced all occurrences of "second fireteam" with "diversion team" and renamed the respective
  field of `DecisionPath` to `diversion_team_leader`.
- Replaced all occurrences of "first fireteam" with "second fireteam".
- Replaced the `first_leader` field of `DecisionPath` with two separate fields.
  - `ideal_second_fireteam_leaders: AllySet`
  - `second_fireteam_leader_is_ideal: bool`
- Clarified the rustdocs for second-fireteam-related fields of `DecisionPath`.
- Improved wording for which Asari to choose at the end of Samara's loyalty mission in the
  formatting logic for `DecisionPath`.
- Moved `DecisionPathLedger` from the `decision` module to the `generate` module.
- Regenerated `outcome_map.rmp` due to changes in `DecisionPath`.

### Removed

- `AllySet::iter()` ([C-ITER])
- Custom rustdocs for non-`std::ops` trait `impl`s for `AllySet`
- `decision::FirstLeader`
  - This struct's API—or lack thereof—was confusing, leading to a bug in the formatting logic for
    `DecisionPath` that would include the phrase "anyone except nobody".

### Fixed

- Usage description in the rustdocs for `examples/generate.rs`
- Grammatical error in the rustdocs for `src/lib.rs`
- `DecisionPath` formatting logic for the selection of the second fireteam leader that could
  potentially emit the phrase "anyone except nobody".
  - This bug could only be produced by constructing a malformed value for the newly removed
    `first_leader` field, which was not possible using public APIs.
- Redundant logic in a few methods of `OutcomeMapGenerator`
- README instructions on running the `generate` example

## [0.1.0] - 2023-02-05

### Added

- Initial commit of the `me2finale` crate

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html
[C-COLLECT]: https://rust-lang.github.io/api-guidelines/interoperability.html#c-collect
[C-EXAMPLE]: https://rust-lang.github.io/api-guidelines/documentation.html#c-example
[C-ITER-TY]: https://rust-lang.github.io/api-guidelines/naming.html#c-iter-ty
[C-ITER]: https://rust-lang.github.io/api-guidelines/naming.html#c-iter

[0.2.0]: https://github.com/80Ltrumpet/me2finale/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/80Ltrumpet/me2finale/releases/tag/v0.1.0