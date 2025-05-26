import MyProject.GradedStarRing.GradedStarRing

variable {A : Type*} [CommRing A] (I : Ideal A)

/- We define a surjection `GradedStarRing I →+* G(A)` by componentwise quotients -/

def GradedStarRing_to_AssociatedGradedRingHom :
    GradedStarRing I →+* AssociatedGradedRing I where
  __ := @DirectSum.map ℕ (fun n ↦ ↥(I^n)) (GradedRingPiece I) _ _ (fun n ↦ {
    toFun := fun x ↦ ⟦⟨x, by simp⟩⟧ₘ
    map_zero' := rfl
    map_add' := fun x y ↦ rfl
  })
  map_one' := by
    have : (1 : GradedStarRing I) = DirectSum.of _ 0 one_star_ideal := rfl
    rw [this]
    simp
    rfl
  map_mul' := by
    intro x y
    induction' x using DirectSum.induction_on with n x x x' hx hx'
    · simp
    · induction' y using DirectSum.induction_on with m y y y' hy hy'
      · simp
      · simp
        rw [DirectSum.of_mul_of]
        rw [DirectSum.of_mul_of]
        rw [DirectSum.map_of]
        rfl
      · rw [mul_add]
        rw [(DirectSum.map _).map_add']
        rw [hy]
        rw [hy']
        simp
        rw [mul_add]
    · rw [add_mul]
      rw [(DirectSum.map _).map_add']
      rw [hx]
      rw [hx']
      simp
      rw [add_mul]

lemma GradedStarRing_to_AssociatedGradedRingHom_surjective :
    Function.Surjective (GradedStarRing_to_AssociatedGradedRingHom I) := by
  apply (DirectSum.map_surjective _).mpr
  intro n
  show Function.Surjective ((QuotientAddGroup.mk' _) ∘ (idealPowerToFiltrationComponent I n))
  apply Function.Surjective.comp
  · exact QuotientAddGroup.mk'_surjective _
  · rintro ⟨x, hx⟩
    simp at hx
    use ⟨x, hx⟩
    rfl
