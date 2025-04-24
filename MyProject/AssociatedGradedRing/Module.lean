import MyProject.AssociatedGradedRing.Ring
import Mathlib.Algebra.Module.GradedModule

/--
  # Associated Graded Module
  In this file, we prove that the associated graded module `G(M)` of an
  `A`-module `M` is a `G(A)`-module.
-/

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GSMul (GradedRingPiece I) (GradedPiece F) where
  smul := by
    intro n m a b
    sorry

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GMulAction (GradedRingPiece I) (GradedPiece F) where
  one_smul := sorry
  mul_smul := sorry

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    DirectSum.GdistribMulAction (GradedRingPiece I) (GradedPiece F) where
  smul_add := sorry
  smul_zero := sorry

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    DirectSum.Gmodule (GradedRingPiece I) (GradedPiece F) where
  add_smul := sorry
  zero_smul := sorry

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
    [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Module (AssociatedGradedRing I) (AssociatedGradedModule F) :=
  DirectSum.Gmodule.module (GradedRingPiece I) (GradedPiece F)
