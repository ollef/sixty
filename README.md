# sixty

A type checker for a dependent type theory using normalisation by evaluation,
with an eye on performance.
Might go into [Sixten](https://github.com/ollef/sixten) one day.

## Roadmap

- [x] Pre-syntax
- [x] Core syntax
- [x] Safe and fast phantom typed De Bruijn indices
- [x] Evaluation
  - [x] Inlining of globals
- [x] Readback
- [x] Parsing
  - [x] Indentation-sensitivity
- [x] Pretty printing
  - [ ] Scope-aware name printing
- [x] Unification and meta variables
  - [x] Pruning
  - [x] The "same meta variable" rule
  - [x] Solution inlining
  - [x] Elaboration of meta variable solutions to local definitions
  - [ ] Rigidity tracking
- [x] Basic type checking
- [x] Query architecture
- [ ] Simple modules
  - [x] Top-level definitions
  - [x] Name resolution
  - [ ] Error for circular values
  - [ ] Imports
- [x] Tests
  - [x] Error tests
- [ ] Implicit arguments
  - [ ] Syntax
  - [x] Type checking
- [ ] Errors
  - [x] Source location tracking
    - [x] Meta variable locations
  - [x] Pretty-printing
  - [ ] Error recovery during
    - [x] Parsing
    - [x] Elaboration
    - [ ] Unification
- [ ] Recursive let bindings
- [ ] Data
  - [ ] Elaboration of data definitions
  - [x] Constructors
    - [ ] Type-based overloading
  - [ ] Pattern matching elaboration
  - [ ] Inductive families
- [ ] Generalisation?
- [ ] Glued evaluation

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
