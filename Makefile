.PHONY: install
install:
	stack build --test --no-run-tests --copy-bins

.PHONY: test
test:
	stack build --test

.PHONY: install-profile
install-profile:
	stack build --profile --test --no-run-tests --copy-bins

.PHONY: profile-tests
profile-tests:
	stack build --test --profile
	stack exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph test-sixty.prof

# Workaround for https://gitlab.haskell.org/ghc/ghc/issues/16682 -- fixed in
# future GHC versions
.PHONY: ghcid
ghcid:
	stack exec --package ghcid -- ghcid --command="stack ghci --test --bench --ghci-options=-fno-break-on-exception --ghci-options=-fno-break-on-error --ghci-options=-v1 --ghci-options=-ferror-spans --ghci-options=-j"

.PHONY: lint
lint: hlint weeder

.PHONY: hlint
hlint:
	stack exec --package hlint -- hlint .

.PHONY: weeder
weeder:
	stack exec --package weeder -- weeder
