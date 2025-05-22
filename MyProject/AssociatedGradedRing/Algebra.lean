import MyProject.AssociatedGradedRing.Ring

/-
  In this file, we prove that the associated graded ring `G(A)` of a ring `A` is an
  `A`-algebra.
-/

variable {A : Type u} [CommRing A] (I : Ideal A)

def algebraMap_fn₁_morphism :
    A →+* (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) where
  toFun := fun a => ⟦(⟨a, by simp⟩)⟧
  map_one' := by rfl
  map_mul' := by
    intro x y
    simp
    rfl
  map_zero' := by rfl
  map_add' := by
    intro x y
    simp
    rfl

def algebraMap_fn₂_morphism :
    (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) →+* AssociatedGradedRing I where
  toFun := fun a ↦ (DirectSum.of _ 0 a )
  map_one' := by rfl
  map_mul' := by
    intro x y
    simp
  map_zero' := by
    simp
  map_add' := by
    intro x y
    simp

instance {A : Type u} [CommRing A] (I : Ideal A) : Algebra A (AssociatedGradedRing I) where
  smul a x := a • x
  algebraMap := (algebraMap_fn₂_morphism I).comp (algebraMap_fn₁_morphism I)
  commutes' := by
    intro r x
    ring
  smul_def' := by
    intro r x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp
    · rintro i ⟨y, hy⟩
      unfold algebraMap_fn₁_morphism algebraMap_fn₂_morphism
      show r • (DirectSum.of (GradedPiece (CanonicalFiltration I)) i) ⟦⟨y, hy⟩⟧ₘ =
        (DirectSum.of (GradedPiece (CanonicalFiltration I)) 0) ⟦⟨r, by simp⟩⟧ₘ *
          (DirectSum.of (GradedPiece (CanonicalFiltration I)) i) ⟦⟨y, hy⟩⟧ₘ
      rw [mul_comm]
      rw [←DirectSum.of_smul]
      rw [DirectSum.of_mul_of]
      congr
      show r • Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      simp [filtration_smul]
      rw [←Submodule.Quotient.mk_smul]
      congr
      simp
      exact mul_comm r y
    · intro x y hx hy
      simp
      rw [hx, hy]
      rw [mul_add]
      rfl