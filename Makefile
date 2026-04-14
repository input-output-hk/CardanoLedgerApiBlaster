.PHONY: usage

usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
	@echo " - build_cardano_ledger_api: Build CardanoLedgerApi formalization."
	@echo " - clean_cardano_ledger_api: Clean compiled lean files for CardanoLedgerApi formalization."
	@echo " - check_cardano_ledger_api: Same as build_cardano_ledger_api but also checks that each lean file"
	@echo "                            in the CardanoLedgerApi formalization is considered during compilatio
	@echo " - build_tests: Build Tests."
	@echo " - clean_tests: Clean compiled lean files for Tests."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"

.PHONY: build_cardano_ledger_api
build_cardano_ledger_api:
	lake build CardanoLedgerApi

.PHONY: clean_cardano_ledger_api
clean_cardano_ledger_api:
	lake clean CardanoLedgerApi

.PHONY: check_cardano_ledger_api
check_cardano_ledger_api:
	./scripts/check_lean_project_compilation.sh CardanoLedgerApi

.PHONY: build_tests
build_tests:
	LEAN_NUM_THREADS=5 lake test

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests: clean_tests
	LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_cardano_ledger_api build_tests

.PHONY: clean_all
clean_all: clean_cardano_ledger_api clean_tests

.PHONY: check_all
check_all: check_cardano_ledger_api check_tests
