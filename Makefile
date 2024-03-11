RELEASE ?= 0
STACK := stack
STACK_BENCH := $(STACK) build --bench --test --no-run-tests
STACK_TEST := $(STACK) build --bench --test --no-run-benchmarks
ifneq ($(RELEASE), 1)
  STACK_TEST += --fast
endif
STACK_BUILD := $(STACK_TEST) --no-run-tests
STACK_INSTALL := $(STACK_BUILD) --copy-bins
HASKELL_SOURCE_DIRECTORIES = $$(yq -r '.. | .["source-dirs"]? | select(. != null)' package.yaml)
HASKELL_SOURCE_FILES = $$(find $(HASKELL_SOURCE_DIRECTORIES) -name "*.hs*")

.PHONY: install
install:
	$(STACK_INSTALL)

.PHONY: test
test:
	$(STACK_TEST)

.PHONY: watch-test
watch-test:
	$(STACK) exec --package ghcid -- ghcid \
		--command="stack ghci sixty:lib sixty:test:test-sixty --test --ghci-options=-fno-break-on-exception --ghci-options=-fno-break-on-error --ghci-options=-v1 --ghci-options=-ferror-spans --ghci-options=-j" \
		--test="Main.main"

.PHONY: install-profile
install-profile:
	$(STACK_INSTALL) --profile

.PHONY: profile-tests
profile-tests:
	$(STACK_TEST) --profile
	$(STACK) exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph test-sixty.prof

.PHONY: profile-bench
bench:
	$(STACK_BENCH)

.PHONY: profile-bench
profile-bench:
	$(STACK_BENCH) --profile
	$(STACK) exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph benchmark-parser.prof

.PHONY: ddump-simpl
ddump-simpl:
	$(STACK_BUILD) --ghc-options='-ddump-simpl -ddump-to-file'

.PHONY: ghcid
ghcid:
	$(STACK) exec --package ghcid -- ghcid

.PHONY: lint
lint: hlint weeder

.PHONY: hlint
hlint:
	$(STACK) exec --package hlint -- hlint .

.PHONY: weeder
weeder:
	$(STACK) exec --package weeder -- weeder

.PHONY: format
format:
	stack exec --package fourmolu -- fourmolu --mode inplace $(HASKELL_SOURCE_FILES)

.PHONY: check-format
check-format:
	stack exec --package fourmolu -- fourmolu --mode check $(HASKELL_SOURCE_FILES)

.PHONY: debug
debug:
	llvm-as out/program.ll -o out/program.bc
	gdb --quiet -ex "b initCloneLookups" -ex "r" --args lli -jit-kind=mcjit out/program.bc
