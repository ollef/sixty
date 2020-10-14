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

.PHONY: ddump-simpl
ddump-simpl:
	stack build --test --no-run-tests --ghc-options='-ddump-simpl -ddump-to-file'

.PHONY: ghcid
ghcid:
	stack exec --package ghcid -- ghcid

.PHONY: lint
lint: hlint weeder

.PHONY: hlint
hlint:
	stack exec --package hlint -- hlint .

.PHONY: weeder
weeder:
	stack exec --package weeder -- weeder
