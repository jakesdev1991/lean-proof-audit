/-
  Two independent statement-level defects, neither of which the kernel can see:

    * the conclusion is `True`, so the theorem asserts nothing;
    * the hypothesis `n > 5` is never used by the proof.

  It compiles, it is axiom-clean, and it means nothing.
-/
set_option autoImplicit false

theorem vacuous (n : Nat) (h : n > 5) : True := trivial
