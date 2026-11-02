/-
  A hypothesis that looks load-bearing and is not. A reader sees `h : n > 5`
  and assumes the result depends on it; deleting it leaves the proof intact.
-/
set_option autoImplicit false

theorem decorative (n : Nat) (h : n > 5) : n = n ∨ n = 0 := by
  exact Or.inr rfl
