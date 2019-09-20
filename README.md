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
  - [x] Scope-aware name printing
- [x] Unification and meta variables
  - [x] Pruning
  - [x] The "same meta variable" rule
  - [x] Solution inlining
  - [x] Elaboration of meta variable solutions to local definitions
  - [x] Case expression inversion
- [x] Basic type checking
- [x] Query architecture
- [x] Simple modules
  - [x] Top-level definitions
  - [x] Name resolution
  - [x] Imports
- [x] Tests
  - [x] Error tests
  - [x] Multi-module tests
- [x] Position-independent implicit arguments
- [x] Errors
  - [x] Source location tracking
    - [x] Meta variable locations
  - [x] Error recovery during
    - [x] Parsing
    - [x] Elaboration
    - [x] Unification
  - [ ] Print the context and let-bound variables (including metas)
- [x] Data
  - [x] Elaboration of data definitions
  - [x] Constructors
    - [x] Type-based overloading
  - [x] ADT-style data definitions
- [x] Pattern matching elaboration
  - [x] Case expressions
  - [x] Exhaustiveness check
  - [x] Redundant pattern check
  - [x] Clause elaboration
  - [x] Pattern lambdas
- [x] Inductive families
- [x] Glued evaluation
- [x] Let definitions by clauses (non-recursive)
- [x] Command-line parser
- [x] Language server
  - [x] Diagnostics
  - [x] Hover
    - [x] Hovering on binders
    - [ ] Hovering on definitions
    - [ ] Print the context and let-bound variables (including metas)
  - [ ] Jump to definition
  - [ ] Multi file projects
- [ ] Prevent CBV-incompatible circular values
- [ ] Generalisation?
- [ ] Literals
  - [ ] Numbers
  - [ ] Strings
- [ ] Records
- [ ] Binary/mixfix operators
- [ ] REPL
- [ ] File watcher
- [ ] Integrate into Sixten

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
