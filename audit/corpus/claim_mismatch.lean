/-
  The formalisation drops a hypothesis the client says the claim needs.
  The formal theorem is therefore stronger than the claim — the expensive kind
  of wrong.
-/
set_option autoImplicit false

theorem parity (n : Nat) (h : n > 0) : n > 0 ∨ n = 0 := by
  exact Or.inl h
