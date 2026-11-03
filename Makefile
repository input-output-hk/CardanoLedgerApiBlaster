.PHONY: usage

usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
	@echo " - build_cardano_ledger_api: Build CardanoLedgerApi formalization."
	@echo " - clean_cardano_ledger_api: Clean compiled lean files for CardanoLedgerApi formalization."
	@echo " - check_cardano_ledger_api: Same as build_cardano_ledger_api but also checks that each lean file"
	@echo "                            in the CardanoLedgerApi formalization is considered during compilation."
	@echo " - build_tests: Build Tests."
	@echo " - clean_tests: Clean compiled lean files for Tests."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"
	@echo " - build_equivalence: Build the UPLC equivalence library and CLI."
	@echo " - clean_equivalence: Clean the compiled UPLC equivalence library and CLI modules."
	@echo " - check_equivalence: Rebuild the UPLC equivalence CLI and run Lean and process tests."

.PHONY: build_cardano_ledger_api
build_cardano_ledger_api:
	lake build CardanoLedgerApi

.PHONY: clean_cardano_ledger_api
clean_cardano_ledger_api:
	lake clean CardanoLedgerApi

.PHONY: check_cardano_ledger_api
check_cardano_ledger_api: clean_cardano_ledger_api
	./scripts/check_lean_project_compilation.sh CardanoLedgerApi

.PHONY: build_tests
build_tests:
	lake test

.PHONY: clean_tests
clean_tests:
	rm -rf .lake/build/lib/lean/Tests* .lake/build/ir/Tests*

.PHONY: check_tests
check_tests: clean_tests
	./scripts/check_lean_project_compilation.sh Tests

.PHONY: build_equivalence
build_equivalence:
	lake build UplcEquivalence uplc_equiv

.PHONY: clean_equivalence
clean_equivalence:
	rm -rf .lake/build/lib/lean/Equivalence* .lake/build/ir/Equivalence*

.PHONY: check_equivalence
check_equivalence: clean_equivalence
	$(MAKE) build_equivalence
	lake build Tests.Equivalence
	python3 -m unittest discover -s equivalence -p 'test_*.py'

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_cardano_ledger_api build_tests build_equivalence

.PHONY: clean_all
clean_all: clean_cardano_ledger_api clean_tests clean_equivalence

.PHONY: check_all
check_all: check_cardano_ledger_api check_tests check_equivalence
