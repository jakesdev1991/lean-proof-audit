/-
  Does not compile, and the failure must be reduced to something small.
-/
set_option autoImplicit false

theorem fine_one (n : Nat) : n = n := rfl

theorem broken (n : Nat) : n = n + 1 := by
  --!error: application type mismatch
  exact rfl

theorem fine_two (n : Nat) : n = n := rfl
