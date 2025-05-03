import MyProject.AssociatedGradedRing.Basic

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
def filtration_smul {m n : ℕ} :
    (CanonicalFiltration I).N m →ₗ[A] F.N n →ₗ[A] F.N (m + n) where
  toFun := fun x ↦ {
    toFun := fun y ↦ ⟨x.1 • y.1, filtration_smul_deg x.2 y.2⟩
    map_add' := fun y z ↦ by
      simp
    map_smul' := fun y z ↦ by
      simp
      module
  }
  map_add' := fun x y ↦ by
    ext z
    simp
    module
  map_smul' := fun x y ↦ by
    ext z
    simp
    module

notation x "×" y => filtration_smul x y

lemma filtration_smul_coe_eval {m n : ℕ} {x : A} {y : M} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ F.N n) :
    ↑(filtration_smul ⟨x, hx⟩ ⟨y, hy⟩) = x • y := rfl

lemma filtration_fsmul_zero {m : ℕ} (n : ℕ) (x : (CanonicalFiltration I).N m) :
    filtration_smul x (0 : F.N n) = 0 :=
  LinearMap.map_zero (filtration_smul x)

lemma filtration_zero_fsmul (m : ℕ) {n : ℕ} (x : F.N n) :
    filtration_smul (0 : (CanonicalFiltration I).N m) x = 0 :=
  LinearMap.map_zero₂ filtration_smul x

lemma filtration_add_fsmul {m n : ℕ} (x y : (CanonicalFiltration I).N m) (z : F.N n) :
    filtration_smul (x + y) z = filtration_smul x z + filtration_smul y z :=
  LinearMap.map_add₂ filtration_smul x y z

lemma filtration_fsmul_add {m n : ℕ} (x : (CanonicalFiltration I).N m) (y z : F.N n) :
    filtration_smul x (y + z) = filtration_smul x y + filtration_smul x z :=
  LinearMap.map_add (filtration_smul x) y z

lemma filtration_smul_fsmul {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : F.N n) :
    filtration_smul (a • x) y = a • (filtration_smul x y) :=
  LinearMap.map_smul₂ filtration_smul a x y

lemma filtration_fsmul_smul {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : F.N n) :
    filtration_smul x (a • y) = a • (filtration_smul x y) :=
  LinearMap.CompatibleSMul.map_smul (filtration_smul x) a y

lemma filtration_one_fsmul {n : ℕ} (x : F.N n) :
    filtration_smul ⟨1, show 1 ∈ (CanonicalFiltration I).N 0 by simp⟩ x = ⟨↑x, by rw [zero_add]; exact x.2⟩ := by
  unfold filtration_smul
  simp

lemma filtration_one_fsmul_coe {n : ℕ} (x : F.N n) :
    ↑(filtration_smul ⟨1, show 1 ∈ (CanonicalFiltration I).N 0 by simp⟩ x : M) = ↑x := by
  unfold filtration_smul
  simp

lemma filtration_mul_smul_coe {k m n : ℕ} (x : (CanonicalFiltration I).N k) (y : (CanonicalFiltration I).N m) (z : F.N n) :
    (↑(filtration_smul (filtration_smul x y) z) : M) = ↑(filtration_smul x (filtration_smul y z)) := by
  rw [filtration_smul_coe_eval, filtration_smul_coe_eval, filtration_smul_coe_eval, filtration_smul_coe_eval]
  simp
  module

def graded_smul_left {m n : ℕ} :
    (CanonicalFiltration I).N m →ₗ[A] (GradedPiece F n) →ₗ[A] (GradedPiece F (m+n)) where
  toFun := fun x ↦ Submodule.mapQ _ _ (filtration_smul x) (by
      intro y h
      have := filtration_smul_deg x.2 h
      exact this
    )
  map_add' := by
    intro x y
    ext ⟨t⟩
    show ⟦filtration_smul (x + y) t⟧ₘ = _
    rw [filtration_add_fsmul]
    rfl
  map_smul' := by
    intro a x
    ext ⟨t⟩
    show ⟦filtration_smul (a • x) t⟧ₘ = _
    rw [filtration_smul_fsmul]
    rfl

def graded_smul_hom {m n : ℕ} :
    GradedRingPiece I m →ₗ[A] GradedPiece F n →ₗ[A] GradedPiece F (m+n) :=
  Submodule.liftQ _ graded_smul_left (by
    intro x h
    ext ⟨y⟩
    show ⟦filtration_smul x y⟧ₘ = 0
    rw [←GradedPiece_mk_zero_iff]
    convert filtration_smul_deg h y.2 using 2
    abel
  )

def graded_smul {m n : ℕ} :
    GradedRingPiece I m → GradedPiece F n → GradedPiece F (m+n) :=
  fun x y ↦ graded_smul_hom x y

lemma graded_smul_of_mk {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : F.N n) :
    graded_smul ⟦x⟧ₘ ⟦y⟧ₘ = ⟦filtration_smul x y⟧ₘ := rfl

lemma GradedPiece_zero (F : I.Filtration M) (m : ℕ) :
    ↑(0 : GradedPiece F m).out ∈ F.N (m+1) := by
  apply GradedPiece_eq_zero_iff.mp rfl

lemma graded_one_smul {n : ℕ} (x : F.N n) :
    graded_smul ⟦⟨1, show 1 ∈ (CanonicalFiltration I).N 0 by simp⟩⟧ₘ ⟦x⟧ₘ =
      (⟦(⟨(x : M), by rw [zero_add]; exact x.2⟩ : F.N (0 + n))⟧ : GradedPiece F (0 + n)) := by
  rw [graded_smul_of_mk]
  rw [filtration_one_fsmul]
