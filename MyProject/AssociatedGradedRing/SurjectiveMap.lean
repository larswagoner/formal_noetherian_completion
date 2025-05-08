import MyProject.AssociatedGradedRing.Map


namespace AssociatedGradedRing

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] {I : Ideal A} (φ : R →+* AssociatedGradedRing I)

lemma hom_surjective_of_incl_of_incl  (h₀ : (GradedRingPiece I 0) = (((Subring.map φ ⊤)).toAddSubgroup).comap (DirectSum.of (GradedRingPiece I) 0)) (h₁ : (GradedRingPiece I 1) = (DirectSum.of (GradedRingPiece I) 1) ⁻¹' (φ '' ⊤))
    (h₁ : (GradedRingPiece I 1) = (((Subring.map φ ⊤)).toAddSubgroup).comap (DirectSum.of (GradedRingPiece I) 1)) : Function.Surjective φ := sorry



end AssociatedGradedRing 