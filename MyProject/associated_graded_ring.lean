import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.GradedAlgebra.Basic

-- define associated graded module, then associated graded ring in terms of that.

/- # Associated Graded Ring
  Consider a ring `A` and an ideal `I : Ideal A`.

  Given an `A`-module `M` and an `I`-filtration `(Mₙ)`, define the associated graded module
    `G(M) = ⊕ₙ Mₙ/Mₙ₊₁`
  This has a natural group structure.

  In the case that `M = A` and `Mₙ = Iⁿ`, we obtain the associated graded ring of `A`
    `G(A) = ⊕ₙ Iⁿ/Iⁿ⁺¹`
  Multiplication is defined by `[xₙ] ⬝ [xₘ] = [xₙ ⬝ xₘ] ∈ Iⁿ⁺ᵐ/Iⁿ⁺ᵐ⁺¹`.

  Now `G(M)` is a `G(A)`-module in a natural way.
-/



open DirectSum

/--
  The `n`-th summand of `G(M)` is given by `Mₙ/Mₙ₊₁`. We use Submodule.comap to pull back the
  submodule `F.N (n + 1) = Mₙ₊₁ ⊆ M` along the map `(F.N n).subtype : Mₙ ⟶ M`.
-/
def GradedPiece {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ):
    Type u := (F.N n) ⧸ (Submodule.comap (F.N n).subtype (F.N (n + 1)))

/--
  `Mₙ/Mₙ₊₁` is an abelian group.
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    AddCommGroup (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance

/--
  `Mₙ/Mₙ₊₁` is an `A`-module.
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    Module A (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance


/--
  The associated graded module is defined by `G(M) = ⊕ₙ Mₙ/Mₙ₊₁`.
-/
def AssociatedGradedModule {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Type u := ⨁ n : ℕ, GradedPiece F n

/--
  `G(M)` is an abelian group.
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
    [Module A M] (F : I.Filtration M) : AddCommGroup (AssociatedGradedModule F) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, GradedPiece F n))

/--
  `G(M)` is an `A`-module.
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M]
    [Module A M] (F : I.Filtration M) : Module A (AssociatedGradedModule F) := by
  unfold AssociatedGradedModule
  infer_instance

/--
  The associated graded ring is defined by `G(A) = ⊕ₙ aⁿ/aⁿ⁺¹` and is a specific instance of `G(M)`.
-/
def AssociatedGradedRing {A : Type u} [CommRing A] (I : Ideal A) : Type u :=
  AssociatedGradedModule (I.stableFiltration (⊤ : Submodule A A))

/--
  `G(A)` is an abelian group.
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : AddCommGroup (AssociatedGradedRing I) :=
  instAddCommGroupAssociatedGradedModule _

/--
  `G(A)` is an `A`-module.
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : Module A (AssociatedGradedRing I) :=
  instModuleAssociatedGradedModule _

namespace AssociatedGradedRing

abbrev CanonicalFiltration {A : Type u} [CommRing A] (I : Ideal A) := I.stableFiltration (⊤ : Submodule A A)

lemma canonicalFiltration_eval {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :
    (CanonicalFiltration I).N m = I ^ m := by simp

lemma mem_filtration_iff_mem_Im {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) (x : A) :
    x ∈ (CanonicalFiltration I).N m ↔ x ∈ I^m := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

lemma canonicalFiltration_mul_deg {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    x * y ∈ (CanonicalFiltration I).N (m + n) := by
  rw [mem_filtration_iff_mem_Im] at *
  exact SetLike.GradedMul.mul_mem hx hy

abbrev GradedRingPiece {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :=
  GradedPiece (CanonicalFiltration I) m

@[simp]
lemma GradedRingPiece_mk_out {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : GradedRingPiece I m) :
    ⟦x.out⟧ = x :=
  Quotient.out_eq x

@[simp]
lemma GradedRingPiece_mk_eq_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} {x y : (CanonicalFiltration I).N m} :
    x.1 - y.1 ∈ (CanonicalFiltration I).N (m+1) ↔ (⟦x⟧ : GradedRingPiece I m) = ⟦y⟧ := by
  rw [Quotient.eq'']
  rw [(Submodule.quotientRel_def
            (Submodule.comap ((CanonicalFiltration I).N m).subtype
              ((CanonicalFiltration I).N (m + 1))))]
  simp

@[simp]
lemma GradedRingPiece_mk_zero {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} :
    (⟦0⟧ : GradedRingPiece I m) = (0 : GradedRingPiece I m) := rfl

lemma GradedRingPiece_mk_zero_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) :
    ↑x ∈ (CanonicalFiltration I).N (m+1) ↔ (⟦x⟧ : GradedRingPiece I m) = (0 : GradedRingPiece I m) := by
  rw [←GradedRingPiece_mk_zero]
  rw [←GradedRingPiece_mk_eq_iff]
  simp

lemma GradedRingPiece_eq_zero_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} {x : GradedRingPiece I m} :
    ↑x.out ∈ (CanonicalFiltration I).N (m+1) ↔ x = (0 : GradedRingPiece I m) := by
  rw [←Quotient.out_eq x]
  rw [←GradedRingPiece_mk_zero]
  rw [←GradedRingPiece_mk_eq_iff]
  simp

@[simp]
lemma GradedRingPiece_out_mk_sub {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) :
    ↑((⟦x⟧ : GradedRingPiece I m).out - x) ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedRingPiece_mk_eq_iff.mpr
  simp

/--
  Let `A` be a ring and `I` be an ideal. Then for `m n : ℕ` we obtain a multiplication map
  `I^m → I^n → I^(m+n)`
-/
def ideal_mul {A : Type u} [CommRing A] (I : Ideal A) (m n : ℕ) :
    ↑((CanonicalFiltration I).N m) →
      ↑((CanonicalFiltration I).N n) →
        ↑((CanonicalFiltration I).N (m + n)) :=
  fun x y ↦ ⟨x.1 * y.1, canonicalFiltration_mul_deg x.2 y.2⟩

lemma ideal_mul_eval {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    ↑(ideal_mul I m n ⟨x, hx⟩ ⟨y, hy⟩ : A) = ↑(x * y) := rfl

lemma ideal_mul_eval₂ {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    ↑(ideal_mul I m n x y : A) = (x : A) * ↑y := rfl

lemma ideal_mul_zero {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) (x : (CanonicalFiltration I).N m) :
    ideal_mul I m n x (0 : (CanonicalFiltration I).N n) = 0 := by
  unfold ideal_mul
  simp


lemma ideal_zero_mul {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) (x : (CanonicalFiltration I).N n) :
    ideal_mul I m n  (0 : (CanonicalFiltration I).N m) x = 0 := by
  unfold ideal_mul
  simp



/--
  Defining multiplication on `G(A)`
        : (h : GradedPiece I m) component_map : GradedPiece I n → GradedPiece I n+m
-/
noncomputable def graded_mul {A : Type u} [CommRing A] (I : Ideal A) {m n :ℕ} :
    (GradedRingPiece I m) → (GradedRingPiece I n) → (GradedRingPiece I (m+n)) :=
  fun x y ↦ ⟦ideal_mul I m n x.out y.out⟧

lemma graded_mul_of_mk {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    graded_mul I ⟦x⟧ ⟦y⟧ = ⟦ideal_mul I m n x y⟧ := by
  unfold graded_mul
  apply GradedRingPiece_mk_eq_iff.mp
  rw [ideal_mul_eval, ideal_mul_eval]
  have : (↑(⟦x⟧ : GradedRingPiece I m).out : A) * ↑(⟦y⟧ : GradedRingPiece I n).out - ↑x * ↑y =
      ((⟦x⟧ : GradedRingPiece I m).out - x) * (⟦y⟧ : GradedRingPiece I n).out + x * ((⟦y⟧ : GradedRingPiece I n).out - y) := by ring
  rw [this]
  apply Submodule.add_mem
  · have := canonicalFiltration_mul_deg (GradedRingPiece_out_mk_sub x) (⟦y⟧ : GradedRingPiece I n).out.2
    convert this using 2
    ring
  · have := canonicalFiltration_mul_deg x.2 (GradedRingPiece_out_mk_sub y)
    exact this

lemma GradedRingPiece_zero {A : Type u} [CommRing A] {I : Ideal A} (m : ℕ) :
    ↑(0 : GradedRingPiece I m).out ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedRingPiece_eq_zero_iff.mpr rfl

/--
  The map `ℕ → Type` given by `GradedRingPiece I` defines a
  graded ring structure.
-/
noncomputable instance {A : Type u} [hA: CommRing A] (I : Ideal A) : GCommRing (GradedPiece (I.stableFiltration (⊤ : Submodule A A))) where
  mul := (graded_mul I)
  mul_zero := by
    intro m n a
    calc graded_mul I a 0 = graded_mul I ⟦a.out⟧ 0 := by rw [Quotient.out_eq]
        _ = graded_mul I ⟦a.out⟧ ⟦0⟧ := by rw [←GradedRingPiece_mk_zero]
        _ = ⟦ideal_mul I m n a.out 0⟧ := by rw [graded_mul_of_mk]
        _ = (⟦0⟧ : GradedRingPiece I (m + n)) := by rw [ideal_mul_zero]
        _ = (0 : GradedRingPiece I (m + n)) := rfl
  zero_mul := by
    intro m n b
    calc graded_mul I 0 b = graded_mul I  0 ⟦b.out⟧  := by rw [Quotient.out_eq]
        _ = graded_mul I ⟦0⟧ ⟦b.out⟧  := by rw [←GradedRingPiece_mk_zero]
        _ = ⟦ideal_mul I m n 0 b.out⟧ := by rw [graded_mul_of_mk]
        _ = (⟦0⟧ : GradedRingPiece I (m + n)) := by rw [ideal_zero_mul]
        _ = (0 : GradedRingPiece I (m + n)) := rfl

  mul_add := sorry
  add_mul := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  intCast := sorry
  intCast_ofNat := sorry
  intCast_negSucc_ofNat := sorry
  mul_comm :=  sorry


/-
  It follows that `G(A)` is a commutative ring.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) :=
  DirectSum.commRing _

/-
  `G(A)` should be an `A`-algebra
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : Algebra A (AssociatedGradedRing I) := sorry

end AssociatedGradedRing

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Module (AssociatedGradedRing I) (AssociatedGradedModule F) := sorry




/-
  This should be the map `ℕ → Submodule A Gₐ(M)` where `n ↦ Mₙ/Mₙ₊₁`
-/
def AssociatedGradedModule_degMap {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
  [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    ℕ → Submodule A (AssociatedGradedModule F) :=
  fun i ↦ LinearMap.range (lof A ℕ (fun n => (GradedPiece F n)) i)

/-
  This should be the map `ϕ : ℕ → Submodule A Gₐ(A)` where `n ↦ aⁿ/aⁿ⁺¹`
-/
def AssociatedGradedRing_degMap {A : Type u} [CommRing A] (I : Ideal A) :
    ℕ → Submodule A (AssociatedGradedRing I) :=
  AssociatedGradedModule_degMap (I.stableFiltration (⊤ : Submodule A A))

/-
  `Gₐ(M)` should be a graded `Gₐ(A)`-module
-/
-- instance : ??? := sorry