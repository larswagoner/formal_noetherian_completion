import Mathlib.RingTheory.Polynomial.Basic

/-
  # Corollary 7.6
  Let `A` be a Noetherian ring. Then `A[x₁, …, xₙ]` is Noetherian.
-/
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

lemma am7_6 (n : ℕ): IsNoetherianRing (MvPolynomial (Fin n) A) :=
  MvPolynomial.isNoetherianRing_fin
