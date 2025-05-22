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

section GradedPiece

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

/--
  The `n`-th summand of `G(M)` is given by `Mₙ/Mₙ₊₁`. We use Submodule.comap to pull back the
  submodule `F.N (n + 1) = Mₙ₊₁ ⊆ M` along the map `(F.N n).subtype : Mₙ ⟶ M`.
-/
def GradedPiece(F : I.Filtration M) (n : ℕ) :
    Type v := (F.N n) ⧸ (Submodule.comap (F.N n).subtype (F.N (n + 1)))

instance (F : I.Filtration M) (n : ℕ) :
    AddCommGroup (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance

instance (F : I.Filtration M) (n : ℕ) :
    Module A (GradedPiece F n) := by
  unfold GradedPiece
  infer_instance

abbrev GradedPiece_mk {F : I.Filtration M} {n : ℕ} (x : F.N n) :
    GradedPiece F n := ⟦x⟧

notation "⟦" x "⟧ₘ" => GradedPiece_mk x

variable {F : I.Filtration M} {m : ℕ}

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

end GradedPiece

section AssociatedGradedModule

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

/--
  The associated graded module is defined by `G(M) = ⊕ₙ Mₙ/Mₙ₊₁`.
-/
def AssociatedGradedModule (F : I.Filtration M) :
    Type v := ⨁ n : ℕ, GradedPiece F n

def AssociatedGradedModule.of {F : I.Filtration M} {n : ℕ} (x : GradedPiece F n) :
  AssociatedGradedModule F := DirectSum.of (GradedPiece F) n x

lemma AssociatedGradedModule.ext {F : I.Filtration M} {m n : ℕ} {x : F.N m} {y : F.N n} (h : m = n) (hxy : (↑x : M) = (↑y : M)):
    (⟨m, ⟦x⟧ₘ⟩ : GradedMonoid (GradedPiece F)) = ⟨n, ⟦y⟧ₘ⟩ := by
  subst h
  have : x = y := SetLike.coe_eq_coe.mp hxy
  subst this
  rfl

/--
  `G(M)` is an abelian group.
-/
instance (F : I.Filtration M) : AddCommGroup (AssociatedGradedModule F) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, GradedPiece F n))

/--
  An element of `AssociatedGradedModule F` can be considered as a map `(n : ℕ) → GradedPiece F n`.
-/
instance (F : I.Filtration M) : DFunLike (AssociatedGradedModule F) _ fun n : ℕ => GradedPiece F n :=
  inferInstanceAs (DFunLike (Π₀ n, GradedPiece F n) _ _)

/--
  An element of `AssociatedGradedModule F` can be considered as a map `(n : ℕ) → GradedPiece F n`.
-/
instance (F : I.Filtration M) : CoeFun (AssociatedGradedModule F) fun _ => ∀ n : ℕ, GradedPiece F n :=
  inferInstanceAs (CoeFun (Π₀ n, GradedPiece F n) fun _ => ∀ n : ℕ, GradedPiece F n)

/--
  `G(M)` is an `A`-module.
-/
instance (F : I.Filtration M) : Module A (AssociatedGradedModule F) := by
  unfold AssociatedGradedModule
  infer_instance

end AssociatedGradedModule

section AssociatedGradedRing

variable {A : Type u} [CommRing A]

/--
  `CanonicalFiltration I` is an abbreviation for `I.stableFiltration (⊤ : Submodule A A)` and is thus given by the filtration `n ↦ Iⁿ`.
-/
abbrev CanonicalFiltration (I : Ideal A) := I.stableFiltration (⊤ : Submodule A A)

lemma canonicalFiltration_eval (I : Ideal A) (m : ℕ) :
    (CanonicalFiltration I).N m = I ^ m := by simp

lemma mem_filtration_iff_mem_Im (I : Ideal A) (m : ℕ) (x : A) :
    x ∈ (CanonicalFiltration I).N m ↔ x ∈ I^m := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

/--
  `GradedRingPiece I m` is an abbreviation for `GradedPiece (CanonicalFiltration I) m` and thus informally reduces to `Iᵐ/Iᵐ⁺¹`.
-/
abbrev GradedRingPiece (I : Ideal A) (m : ℕ) :=
  GradedPiece (CanonicalFiltration I) m


def idealPowerToFiltrationComponent (I : Ideal A) (m : ℕ ): ↥(I^m) →+ (CanonicalFiltration I).N m where
  toFun := (fun a => ⟨ a , by simp ⟩)
  map_zero' := rfl
  map_add' := fun _ _ => rfl





/--
  The associated graded ring is defined by `G(A) = ⊕ₙ aⁿ/aⁿ⁺¹` and is a specific instance of `G(M)`.
-/
def AssociatedGradedRing (I : Ideal A) : Type u :=
  AssociatedGradedModule (CanonicalFiltration I)

def AssociatedGradedRing.of {I : Ideal A} {n : ℕ} (x : GradedRingPiece I n) :
  AssociatedGradedRing I := DirectSum.of _ n x


/- Map from `Iᵐ/Iᵐ⁺¹` to `AssociatedGradedRing I` -/

def GradedRingPiece.toAssociatedGradedRing (I : Ideal A): GradedRingPiece I m → AssociatedGradedRing I :=  fun a ↦ AssociatedGradedRing.of a




/--
  `G(A)` is an abelian group.
-/
instance (I : Ideal A) : AddCommGroup (AssociatedGradedRing I) :=
  instAddCommGroupAssociatedGradedModule _

/--
  An element of `AssociatedGradedModule F` can be considered as a map `(n : ℕ) → GradedPiece F n`.
-/
instance (I : Ideal A) :
    DFunLike (AssociatedGradedRing I) _ fun n : ℕ => GradedRingPiece I n :=
  instDFunLikeAssociatedGradedModuleNatGradedPiece (CanonicalFiltration I)

instance (I : Ideal A) :
    CoeFun (AssociatedGradedRing I) fun _ => ∀ n : ℕ, GradedRingPiece I n :=
  instCoeFunAssociatedGradedModuleForallGradedPiece (CanonicalFiltration I)

/--
  `G(A)` is an `A`-module.
-/
instance (I : Ideal A) : Module A (AssociatedGradedRing I) :=
  instModuleAssociatedGradedModule _

end AssociatedGradedRing
