import MyProject.AssociatedGradedRing.Map


namespace AssociatedGradedRing

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] {I : Ideal A} (φ : R →+* AssociatedGradedRing I)

lemma hom_surjective_of_eq_of_eq (h₀ : (DirectSum.of (GradedRingPiece I) 0) ⁻¹' (φ '' ⊤) = ⊤) 
    (h₁ :(DirectSum.of (GradedRingPiece I) 1) ⁻¹' (φ '' ⊤) = ⊤) : Function.Surjective φ := by 

  unfold Function.Surjective
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · use 0
    simp
  · sorry
  · rintro _ _ ⟨a, rfl⟩   ⟨b, rfl⟩ 
    use a + b
    simp
    



end AssociatedGradedRing 