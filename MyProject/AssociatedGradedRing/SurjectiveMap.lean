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
  · rintro n
    induction' n with n hn I
    · intro x
      have h₃ : x ∈ (⊤ : Set ((GradedRingPiece I) 0)) := by 
        exact trivial
      rw[← h₀] at h₃
      simp at h₃
      obtain ⟨b, hb⟩ := h₃
      use b
      
    · -- trick is to write goal x as I-linear combination of elements in IH n.
      
      sorry
    -- hz says that z is in Iⁿ
    
    -- so this y is an element of Iⁿ/Iⁿ⁺¹
    --- I^n can be written as a a finite sum of things I^n-1 over I, for al  n, use induction, work with quotients, pull stuff out. 
    

  · rintro _ _ ⟨a, rfl⟩   ⟨b, rfl⟩ 
    use a + b
    simp
    



end AssociatedGradedRing 