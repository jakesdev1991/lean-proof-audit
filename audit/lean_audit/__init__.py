"""lean-audit: machine-checked, evidence-carrying verdicts for Lean 4 code.

The design rule for this package is: **never re-implement the kernel.**
Every statement the audit makes about a Lean file is either

  * produced by a real `lean` invocation whose exact command and stdout are
    attached to the finding as evidence, or
  * explicitly labelled a heuristic (`confidence: "heuristic"`) and backed by
    an independent Lean run before it is raised in severity.

Anything the audit cannot establish is reported as `inconclusive`, never as a
pass. A cheap false pass is the one failure mode this tool must not have.
"""

__version__ = "2.0.0"
SCHEMA_VERSION = "lean-audit/2"
