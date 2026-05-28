.PHONY: build verify check-doc-names audit lint update clean

build:
	lake build --wfail

verify:
	lake build --wfail OrdvecFormalization.Verify

check-doc-names:
	python3 scripts/check_doc_names.py

audit:
	! rg -n '\bsorry\b|sorryAx' OrdvecFormalization OrdvecFormalization.lean README.md docs scripts

lint:
	lake exe runLinter OrdvecFormalization

update:
	lake update

clean:
	lake clean
