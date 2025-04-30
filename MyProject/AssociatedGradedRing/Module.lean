import MyProject.AssociatedGradedRing.Ring
import Mathlib.Algebra.Module.GradedModule

/-
  # Associated Graded Module
  In this file, we prove that the associated graded module `G(M)` of an
  `A`-module `M` is a `G(A)`-module.
-/

universe u

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)

instance : GradedMonoid.GSMul (GradedRingPiece I) (GradedPiece F) where
  smul := graded_smul

instance : GradedMonoid.GMulAction (GradedRingPiece I) (GradedPiece F) where
  one_smul := by
    intro ⟨n, a⟩
    show (⟨0 + n, graded_smul ⟦one_cf⟧ₘ a⟩ : GradedMonoid (GradedPiece F)) = ⟨n, a⟩
    rw [←Quotient.out_eq a]
    apply AssociatedGradedModule.ext
    · exact zero_add n
    rw [filtration_one_fsmul a.out]
  mul_smul := by
    intro ⟨k, a⟩ ⟨m, b⟩ ⟨n, c⟩
    show (⟨k + m + n, graded_smul (graded_mul a b) c⟩ : GradedMonoid (GradedPiece F)) =
        ⟨k + (m + n), graded_smul a (graded_smul b c)⟩
    rw [←Quotient.out_eq a]
    rw [←Quotient.out_eq b]
    rw [←Quotient.out_eq c]
    apply AssociatedGradedModule.ext
    · exact add_assoc k m n
    exact filtration_mul_smul_coe _ _ _

instance : DirectSum.GdistribMulAction (GradedRingPiece I) (GradedPiece F) where
  smul_add := fun a ↦ LinearMap.map_add (graded_smul_hom a)
  smul_zero := fun a ↦ LinearMap.map_zero (graded_smul_hom a)

instance : DirectSum.Gmodule (GradedRingPiece I) (GradedPiece F) where
  add_smul := LinearMap.map_add₂ graded_smul_hom
  zero_smul := LinearMap.map_zero₂ graded_smul_hom

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
instance : Module (AssociatedGradedRing I) (AssociatedGradedModule F) :=
  DirectSum.Gmodule.module (GradedRingPiece I) (GradedPiece F)

lemma AssociatedGradedModule.of_smul_of {F : I.Filtration M} {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece F n) :
  (AssociatedGradedRing.of s) • (AssociatedGradedModule.of x) =
    (AssociatedGradedModule.of (graded_smul s x)) :=
  DirectSum.Gmodule.of_smul_of _ _ _ _
