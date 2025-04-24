import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.GradedAlgebra.Basic

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
def GradedPiece {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    Type u := (F.N n) ⧸ (Submodule.comap (F.N n).subtype (F.N (n + 1)))

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    AddCommGroup (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance

instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M) (n : ℕ) :
    Module A (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance

abbrev GradedPiece_mk {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] {F : I.Filtration M} {n : ℕ} (x : F.N n) :
    GradedPiece F n := ⟦x⟧

notation "⟦" x "⟧ₘ" => GradedPiece_mk x

variable {A : Type u} [CommRing A] {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] {F : I.Filtration M} {m : ℕ}

@[simp]
lemma GradedPiece_mk_out (x : GradedPiece F m) :
    ⟦x.out⟧ₘ = x :=
  Quotient.out_eq x

@[simp]
lemma GradedPiece_mk_eq_iff {x y : F.N m} :
    x.1 - y.1 ∈ F.N (m+1) ↔ ⟦x⟧ₘ = ⟦y⟧ₘ := by
  rw [Quotient.eq'']
  rw [(Submodule.quotientRel_def
            (Submodule.comap (F.N m).subtype
              (F.N (m + 1))))]
  simp

@[simp]
lemma GradedPiece_mk_zero :
    ⟦0⟧ₘ = (0 : GradedPiece F m) := rfl

lemma GradedPiece_mk_zero_iff {x : F.N m} :
    ↑x ∈ F.N (m+1) ↔ ⟦x⟧ₘ = 0 := by
  rw [←GradedPiece_mk_zero]
  rw [←GradedPiece_mk_eq_iff]
  simp

lemma GradedPiece_eq_zero_iff {x : GradedPiece F m} :
    x = (0 : GradedPiece F m) ↔ ↑x.out ∈ F.N (m+1) := by
  rw [←Quotient.out_eq x]
  rw [←GradedPiece_mk_zero]
  rw [←GradedPiece_mk_eq_iff]
  simp

@[simp]
lemma GradedPiece_out_mk_sub(x : F.N m) :
    ↑(⟦x⟧ₘ.out - x) ∈ F.N (m+1) := by
  apply GradedPiece_mk_eq_iff.mpr
  simp

lemma GradedPiece_mk_add (x y : F.N m) :
  ⟦x + y⟧ₘ = ⟦x⟧ₘ + ⟦y⟧ₘ := rfl

lemma GradedPiece_mk_neg (x : F.N m) :
  ⟦-x⟧ₘ = -⟦x⟧ₘ := rfl

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
