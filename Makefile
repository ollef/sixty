.PHONY: install
install:
	stack install --fast

.PHONY: test
test:
	stack test --fast

.PHONY: profile-tests
profile-tests:
	stack test --profile
	stack exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph test-sixty.prof

.PHONY: lint
lint: hlint weeder

.PHONY: hlint
hlint:
	stack exec --package hlint -- hlint .

.PHONY: weeder
weeder:
	stack exec --package weeder -- weeder
