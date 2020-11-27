RELEASE ?= 0
STACK := stack
STACK_TEST := $(STACK) build --test
ifneq ($(RELEASE), 1)
  STACK_TEST += --fast
endif
STACK_BUILD := $(STACK_TEST) --no-run-tests
STACK_INSTALL := $(STACK_BUILD) --copy-bins

.PHONY: install
install:
	$(STACK_INSTALL)

.PHONY: test
test:
	$(STACK_TEST)

.PHONY: install-profile
install-profile:
	$(STACK_INSTALL) --profile

.PHONY: profile-tests
profile-tests:
	$(STACK_BUILD)
	$(STACK) exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph test-sixty.prof

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
	$(STACK) --package hlint -- hlint .

.PHONY: weeder
weeder:
	$(STACK) --package weeder -- weeder
