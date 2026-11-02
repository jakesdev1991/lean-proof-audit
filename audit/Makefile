.PHONY: test selfcheck doctor example clean publish-contract

test:
	python3 -m unittest discover -s tests -t . -v

selfcheck:
	python3 -m lean_audit.cli selfcheck

doctor:
	python3 -m lean_audit.cli doctor

example:
	python3 -m lean_audit.cli audit corpus/vacuous.lean \
		--markdown docs/example-report/report.md \
		--json docs/example-report/report.json

publish-contract:
	@# The vault-side script is a verbatim copy so the vault needs nothing but Python.
	@# tests/test_audit.py fails if the two ever diverge.
	cp lean_audit/conformance_probe.py ../contract/vault_conformance.py
	chmod +x ../contract/vault_conformance.py
	@echo "published contract/vault_conformance.py"

clean:
	rm -rf build dist *.egg-info **/__pycache__
