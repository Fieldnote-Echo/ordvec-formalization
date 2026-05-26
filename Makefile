.PHONY: build verify audit lint update clean

build:
	lake build --wfail

verify:
	lake build --wfail OrdvecFormalization.Verify

audit:
	! rg -n '\bsorry\b|sorryAx' OrdvecFormalization OrdvecFormalization.lean README.md

lint:
	lake exe runLinter OrdvecFormalization

update:
	lake update

clean:
	lake clean
