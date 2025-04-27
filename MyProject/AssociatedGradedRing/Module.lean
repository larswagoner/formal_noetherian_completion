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

lemma filtration_smul_deg {m n : ℕ} {x : A} {y : M} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ F.N n) :
    x • y ∈ F.N (m + n) := by
  apply Ideal.Filtration.pow_smul_le F m n
  rw [mem_filtration_iff_mem_Im] at *
  exact Submodule.smul_mem_smul hx hy

/--
  Let `A` be a ring, `I` an ideal, `M` an `A`-module and `F` an `I`-filtration on `M`.
  Then for `m n : ℕ` we obtain a multiplication map `Iᵐ → F.N n → F.N (m+n)`
-/
def filtration_smul (F : I.Filtration M) (m n : ℕ) :
    ↑((CanonicalFiltration I).N m) → ↑(F.N n) → ↑(F.N (m + n)) :=
  fun x y ↦ ⟨(x.1 • y.1 : M), filtration_smul_deg x.2 y.2⟩

lemma filtration_smul_coe_eval {m n : ℕ} {x : A} {y : M} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ F.N n) :
    ↑(filtration_smul F m n ⟨x, hx⟩ ⟨y, hy⟩ : M) = x • y := rfl

lemma filtration_smul_zero {m : ℕ} (n : ℕ) (x : (CanonicalFiltration I).N m) :
    filtration_smul F m n x (0 : F.N n) = 0 := by
  unfold filtration_smul
  simp

lemma filtration_zero_smul (m : ℕ) {n : ℕ} (x : F.N n) :
    filtration_smul F m n (0 : (CanonicalFiltration I).N m) x = 0 := by
  unfold filtration_smul
  simp

lemma filtration_one_smul {n : ℕ} (x : F.N n) :
    filtration_smul F 0 n one_cf x = ⟨↑x, by rw [zero_add]; exact x.2⟩ := by
  unfold filtration_smul
  simp




noncomputable def graded_smul (F : I.Filtration M) {m n : ℕ} :
    (GradedRingPiece I m) → (GradedPiece F n) → (GradedPiece F (m+n)) :=
  fun x y ↦ ⟦filtration_smul F m n x.out y.out⟧ₘ

lemma graded_smul_of_mk {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : F.N n) :
    graded_smul F ⟦x⟧ₘ ⟦y⟧ₘ = ⟦filtration_smul F m n x y⟧ₘ := by
  unfold graded_smul
  apply GradedPiece_mk_eq_iff.mp
  rw [filtration_smul_coe_eval, filtration_smul_coe_eval]
  have : (⟦x⟧ₘ.out : A) • (⟦y⟧ₘ.out : M) - (x : A) • (y : M) =
      (⟦x⟧ₘ.out - x : A) • (⟦y⟧ₘ.out : M) + (x : A) • (⟦y⟧ₘ.out - y : M) := by module
  rw [this]
  apply Submodule.add_mem
  · have := filtration_smul_deg (GradedPiece_out_mk_sub x) ⟦y⟧ₘ.out.2
    convert this using 2
    abel
  · have := filtration_smul_deg x.2 (GradedPiece_out_mk_sub y)
    exact this

lemma GradedPiece_zero (F : I.Filtration M) (m : ℕ) :
    ↑(0 : GradedPiece F m).out ∈ F.N (m+1) := by
  apply GradedPiece_eq_zero_iff.mp rfl

lemma graded_one_smul {n : ℕ} (x : F.N n) :
    graded_smul F one_gp ⟦x⟧ₘ =
      (⟦(⟨(x : M), by rw [zero_add]; exact x.2⟩ : F.N (0 + n))⟧ : GradedPiece F (0 + n)) := by
  rw [graded_smul_of_mk]
  rw [filtration_one_smul]

noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GSMul (GradedRingPiece I) (GradedPiece F) where
  smul := graded_smul F

noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    GradedMonoid.GMulAction (GradedRingPiece I) (GradedPiece F) where
  one_smul := sorry
  mul_smul := sorry

noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    DirectSum.GdistribMulAction (GradedRingPiece I) (GradedPiece F) where
  smul_add := sorry
  smul_zero := sorry

noncomputable instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
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

lemma AssociatedGradedModule.of_smul_of {F : I.Filtration M} {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece F n) :
  (AssociatedGradedRing.of s) • (AssociatedGradedModule.of x) =
    (AssociatedGradedModule.of (graded_smul F s x)) :=
  DirectSum.Gmodule.of_smul_of _ _ _ _
