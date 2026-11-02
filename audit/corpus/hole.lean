/-
  The file compiles. The theorem is not proved.

  `sorry` is a *warning* in Lean, not an error, so a green build tells you
  nothing. `#print axioms` is what exposes it.
-/
set_option autoImplicit false

theorem headline_theorem (n : Nat) : n + 0 = n := by
  sorry
