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
    (I.stableFiltration ⊤).N m = I ^ m := by simp

def CanonicalMap {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :
    ↑((CanonicalFiltration I).N m) → ↑(I ^ m) := by
  intro x
  rw [←canonicalFiltration_eval I m]
  exact x

def CanonicalMapInv {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :
     ↑(I ^ m) → ↑((CanonicalFiltration I).N m) := by
  intro x
  rw [canonicalFiltration_eval I m]
  exact x

lemma canonicalMapInv_comp_map {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) (x : ↑((CanonicalFiltration I).N m)) :
    (CanonicalMapInv I m (CanonicalMap I m x)) = x := by
  simp [CanonicalMapInv, CanonicalMap]

lemma canonicalMap_comp_mapInv {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) (x : ↑(I^m)) :
    (CanonicalMap I m (CanonicalMapInv I m x)) = x := by
  simp [CanonicalMapInv, CanonicalMap]

abbrev GradedRingPiece {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :=
  GradedPiece (CanonicalFiltration I) m

def GradedRingPiece_mk {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : ↑(I^m)) :
    (GradedRingPiece I m) :=
  Quotient.mk _ (CanonicalMapInv I m x)

noncomputable def GradedRingPiece_out {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : GradedRingPiece I m) :
    ↑(I ^ m) :=
  CanonicalMap I m x.out

@[simp]
lemma GradedRingPiece_mk_out {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : GradedRingPiece I m) :
    (GradedRingPiece_mk (GradedRingPiece_out x)) = x := by
  unfold GradedRingPiece_mk GradedRingPiece_out
  rw [canonicalMapInv_comp_map]
  exact Quotient.out_eq x

/--
  Let `A` be a ring and `I` be an ideal. Then for `m n : ℕ` we obtain a multiplication map
  `I^m → I^n → I^(m+n)`
-/
def ideal_mul {A : Type u} [CommRing A] (I : Ideal A) (m n : ℕ) :
    ↑(I^m) → ↑(I^n) → ↑(I^(m+n)) :=
  fun x y ↦ ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩

lemma ideal_mul_eval {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) {x y : A} (hx : x ∈ I^m) (hy : y ∈ I^n) :
    ↑(ideal_mul I m n ⟨x, hx⟩ ⟨y, hy⟩ : A) = ↑(x * y) := rfl

/--
  Defining multiplication on `G(A)`
        : (h : GradedPiece I m) component_map : GradedPiece I n → GradedPiece I n+m
-/
noncomputable def graded_mul {A : Type u} [CommRing A] (I : Ideal A) {m n :ℕ} :
    (GradedRingPiece I m) → (GradedRingPiece I n) → (GradedRingPiece I (m+n)) :=
  fun x y ↦
    GradedRingPiece_mk (ideal_mul I m n
      (GradedRingPiece_out x)
      (GradedRingPiece_out y))

lemma graded_mul_of_mk {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (x : ↑(I^m)) (y : ↑(I^n)) :
    graded_mul I
      (GradedRingPiece_mk x) (GradedRingPiece_mk y) =
      (GradedRingPiece_mk (ideal_mul I m n x y)) := by
  unfold graded_mul
  sorry


/--
  The map `ℕ → Type` given by `GradedRingPiece I` defines a
  graded ring structure.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommRing (GradedRingPiece I) where
  mul := graded_mul I
  mul_zero := sorry
  zero_mul := sorry
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
  mul_comm := sorry

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
