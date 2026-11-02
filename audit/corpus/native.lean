/-
  `native_decide` proves a goal by compiling and running code. Accepted by Lean;
  the trust boundary moves off the kernel.
-/
set_option autoImplicit false

theorem two_plus_two : 2 + 2 = 4 := by
  native_decide
