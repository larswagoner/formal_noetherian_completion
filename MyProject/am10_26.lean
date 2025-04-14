import MyProject.am10_22
import MyProject.am10_25

/-
  # Theorem 10.26
  If `A` is a Noetherian ring and `I` an ideal of of `A`,
  then the `I`-completion `Â` of `A` is Noetherian.
-/

theorem AdicCompletion.noetherian_of_isNoetherian {A : Type*} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AdicCompletion I A) := by
  sorry
