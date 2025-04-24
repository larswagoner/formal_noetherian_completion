import MyProject.am10_22
import MyProject.am10_25

/-
  # Theorem 10.26
  If `A` is a Noetherian ring and `I` an ideal of of `A`,
  then the `I`-completion `Â` of `A` is Noetherian.
-/

theorem AdicCompletion.noetherian_of_isNoetherian {A : Type*} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AdicCompletion I A) := by
  apply am10_25 (I.adicCompletion I) ((I.adicCompletion I).stableFiltration (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I A)))
  · apply IsHausdorff.iInf_pow_smul
    apply IsAdicComplete.toIsHausdorff
  · apply isNoetherianRing_of_ringEquiv (AssociatedGradedRing I)
    apply am10_22_ii
