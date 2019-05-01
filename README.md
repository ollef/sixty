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
- [x] Pretty printing
- [ ] Unification and meta variables
- [ ] Basic type checking
- [ ] Tests
- [ ] Implicit arguments and subtyping
- [ ] Source location tracking for error messages
- [ ] Top-level definitions
- [ ] Data definitions
- [ ] Pattern matching elaboration
- [ ] Glued evaluation

## Inspiration

* András Kovács' [smalltt](https://github.com/AndrasKovacs/smalltt) and [work on Dhall](https://discourse.dhall-lang.org/t/nbe-type-checking-conversion-checking/55)
* Thierry Coquand's [semantic type checking](http://www.cse.chalmers.se/~coquand/type.ps)
* Danny Gratzer's [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt)
