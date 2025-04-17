import MyProject.am10_22
import MyProject.am10_25

/-
  # Theorem 10.26
  If `A` is a Noetherian ring and `I` an ideal of of `A`,
  then the `I`-completion `Â` of `A` is Noetherian.
-/



theorem AdicCompletion.noetherian_of_isNoetherian {A : Type*} [CommRing A] (I : Ideal A) [IsNoetherianRing A] :
  IsNoetherianRing (AdicCompletion I A) := by
  apply am10_25 (I.adicCompletion I) ((I.adicCompletion I).stableFiltration (⊤))
  · apply IsHausdorff.iInf_pow_smul
    apply IsAdicComplete.toIsHausdorff
  · --unfold AssociatedGradedRing
    --have h := (@isNoetherianRing_iff (AssociatedGradedRing (I.adicCompletion I))).mp
    --unfold AssociatedGradedRing at h

    have h₁ : IsNoetherianRing (AssociatedGradedRing (I.adicCompletion I)) := by
      apply isNoetherianRing_of_ringEquiv (AssociatedGradedRing I)
      apply am10_22_ii
    -- exact h₁

    sorry
