# sixty

A type checker for a dependent type theory using normalisation by evaluation,
with an eye on performance.
Might go into [Sixten](https://github.com/ollef/sixten) one day.

## Roadmap

- [x] Pre-syntax
- [x] Core syntax
- [x] Safe and fast phantom typed De Bruijn indices
- [x] Evaluation
- [x] Readback
- [x] Parsing
  - [ ] Indentation-sensitivity
- [x] Pretty printing
  - [ ] Scope-aware name printing
- [x] Unification and meta variables
  - [x] Pruning
  - [x] The "same meta variable" rule
  - [ ] Rigidity tracking
  - [ ] Solution inlining
- [x] Basic type checking
- [x] Query architecture
- [ ] Simple modules
  - [x] Top-level definitions
  - [x] Name resolution
  - [ ] Error for circular values
  - [ ] Elaboration of meta variable solutions to top-level
  - [ ] Imports
- [ ] Tests
- [ ] Implicit arguments and subtyping
  - [ ] Deep skolemisation
- [ ] Source location tracking for error messages
- [ ] Recursive let bindings
- [ ] Error recovery during
  - [ ] Parsing
  - [x] Elaboration
  - [ ] Unification
- [ ] Data definitions
- [ ] Pattern matching elaboration
- [ ] Generalisation?
- [ ] Glued evaluation

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
