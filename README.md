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
- [x] Implicit arguments
  - [x] Position-independent application and abstraction syntax
  - [x] Implicits in patterns
  - [ ] Implicit data parameters
- [x] Errors
  - [x] Source location tracking
    - [x] Meta variable locations
  - [x] Error recovery during
    - [x] Parsing
    - [x] Elaboration
    - [x] Unification
  - [ ] Pretty pretty-printing
- [ ] Recursive let bindings
- [x] Data
  - [x] Elaboration of data definitions
  - [x] Constructors
    - [x] Type-based overloading
- [x] Pattern matching elaboration
  - [x] Case expressions
  - [x] Exhaustiveness check
  - [x] Redundant pattern check
  - [x] Clause elaboration
  - [ ] Pattern lambdas and pis
- [ ] Inductive families
- [ ] Generalisation?
- [ ] Glued evaluation
- [ ] Literals
  - [ ] Numbers
  - [ ] Strings
- [ ] Command-line parser
- [ ] Language server
- [ ] Integrate into Sixten

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
