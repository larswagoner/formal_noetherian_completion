import MyProject.AssociatedGradedRing.Ring
import Mathlib.Algebra.Module.GradedModule

/-
  # Associated Graded Module
  In this file, we prove that the associated graded module `G(M)` of an
  `A`-module `M` is a `G(A)`-module.
-/

universe u

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M] {F : I.Filtration M}

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GSMul (GradedRingPiece I) (GradedPiece F) where
  smul := graded_smul F

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GMulAction (GradedRingPiece I) (GradedPiece F) where
  one_smul := sorry
  mul_smul := sorry

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    DirectSum.GdistribMulAction (GradedRingPiece I) (GradedPiece F) where
  smul_add := fun a ↦ LinearMap.map_add ((graded_smul_hom F) a)
  smul_zero := fun a ↦ LinearMap.map_zero ((graded_smul_hom F) a)

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    DirectSum.Gmodule (GradedRingPiece I) (GradedPiece F) where
  add_smul := LinearMap.map_add₂ (graded_smul_hom F)
  zero_smul := LinearMap.map_zero₂ (graded_smul_hom F)

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
    [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Module (AssociatedGradedRing I) (AssociatedGradedModule F) :=
  DirectSum.Gmodule.module (GradedRingPiece I) (GradedPiece F)

lemma AssociatedGradedModule.of_smul_of {F : I.Filtration M} {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece F n) :
  (AssociatedGradedRing.of s) • (AssociatedGradedModule.of x) =
    (AssociatedGradedModule.of (graded_smul F s x)) :=
  DirectSum.Gmodule.of_smul_of _ _ _ _
