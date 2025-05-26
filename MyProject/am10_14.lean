import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-
  # Proposition 10.14
  Let `A` be a Noetherian ring and `I` an ideal of `A`. Let `Â` denote the `I`-adic completion.
  Then `Â` is a flat `A`-algebra.
-/

variable {A : Type*} [CommRing A] (I : Ideal A) [IsNoetherianRing A]

lemma am10_14 : Module.Flat A (AdicCompletion I A) := AdicCompletion.flat_of_isNoetherian I
