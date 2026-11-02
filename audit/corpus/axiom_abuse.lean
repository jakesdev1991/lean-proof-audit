/-
  The single most common way a "kernel-verified" claim collapses: a custom axiom.
  The kernel is happy; the assumption is doing the work.
-/
set_option autoImplicit false

axiom arithmetic_is_broken : False

theorem everything_is_true (n : Nat) : n = 0 := by
  exact absurd rfl arithmetic_is_broken
