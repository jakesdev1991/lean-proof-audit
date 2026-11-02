/-
  A theorem that does everything right: the hypothesis is genuinely used, the
  proof is specific to the conclusion, and nothing leans on an axiom beyond
  what Lean grants. The audit must report PASS and must not invent findings.
-/
set_option autoImplicit false

theorem uses_hypothesis (n : Nat) (h : n > 0) : n > 0 ∨ n = 0 := by
  exact Or.inl h
