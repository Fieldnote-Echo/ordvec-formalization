.PHONY: build verify audit update clean

build:
	lake build --wfail

verify:
	lake build --wfail OrdvecFormalization.Verify

audit:
	! rg -n '\bsorry\b|sorryAx' OrdvecFormalization OrdvecFormalization.lean README.md

update:
	lake update

clean:
	lake clean
