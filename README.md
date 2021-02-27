# sixty ![](https://github.com/ollef/sixty/workflows/Tests/badge.svg) [![Gitter chat](https://badges.gitter.im/ollef/sixten.svg)](https://gitter.im/sixten-lang)

A type checker for a dependent type theory using normalisation by evaluation,
with an eye on performance.
Might go into [Sixten](https://github.com/ollef/sixten) one day.

## Roadmap

- [x] Surface syntax
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
  - [x] The "same meta variable" intersection rule
  - [x] Solution inlining
  - [x] Elaboration of meta variable solutions to local definitions
  - [x] Case expression inversion
  - [x] Ordered meta variables
- [x] Basic type checking
- [x] Elaboration postponement
  - [x] Lazily written solutions
- [x] Query architecture
  - [x] Parallel type checking
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
- [x] Let definitions by clauses
  - [ ] Recursive lets
- [x] Command-line parser
- [x] Language server
  - [x] Diagnostics
  - [x] Hover
    - [ ] Print the context and let-bound variables (including metas)
  - [x] Jump to definition
  - [x] Multi file projects
  - [x] Reverse dependency tracking
  - [x] Completion
  - [x] Type-based refinement completion snippets
  - [x] Find references
  - [x] Renaming
  - [x] Code lenses
  - [ ] Language server tests
- [x] File watcher
- [ ] Cached builds
  - [ ] Per-module caches
- [ ] Backend
  - [x] Typed lambda lifting
  - [x] Typed closure conversion
  - [ ] Code generation
  - [ ] Garbage collection
  - [ ] Extern code
- [ ] Prevent CBV-incompatible circular values
- [ ] Literals
  - [x] Numbers
  - [ ] Strings
- [ ] Records
- [ ] Binary/mixfix operators
- [ ] REPL
- [ ] Integrate into Sixten

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
