import MyProject.GradedStarRing.GradedStarRing

/-
  In this file, we prove that the graded star ring `A*` of a ring `A` is an
  `A`-algebra.
-/

variable {A : Type u} [CommRing A] (I : Ideal A)

def star_algebraMap_fn₁_morphism :
    A →+* ↥(I^0) where
  toFun := fun a => (⟨a, by simp⟩)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def star_algebraMap_fn₂_morphism :
    ↥(I^0) →+* GradedStarRing I where
  toFun := fun a ↦ (DirectSum.of _ 0 a)
  map_one' := by rfl
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

instance : Algebra A (GradedStarRing I) where
  smul a x := a • x
  algebraMap := (star_algebraMap_fn₂_morphism I).comp (star_algebraMap_fn₁_morphism I)
  commutes' := by
    intro r x
    ring
  smul_def' := by
    intro r x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp
    · rintro i y
      unfold star_algebraMap_fn₁_morphism star_algebraMap_fn₂_morphism
      simp
      rw [←DirectSum.of_smul]
      rw [mul_comm]
      rw [DirectSum.of_mul_of]
      congr
      apply Subtype.coe_inj.mp
      simp
      rw [mul_comm]
    · intro x y hx hy
      simp
      rw [hx, hy]
      rw [mul_add]
      rfl
