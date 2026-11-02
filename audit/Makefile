.PHONY: test selfcheck doctor example clean

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

clean:
	rm -rf build dist *.egg-info **/__pycache__
