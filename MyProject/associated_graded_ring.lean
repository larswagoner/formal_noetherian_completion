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

/--
  `CanonicalFiltration I` is an abbreviation for `I.stableFiltration (⊤ : Submodule A A)` and is thus given by the filtration `n ↦ Iⁿ`.
-/
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


/--
  `GradedRingPiece I m` is an abbreviation for `GradedPiece (CanonicalFiltration I) m` and thus informally reduces to `Iᵐ/Iᵐ⁺¹`.
-/
abbrev GradedRingPiece {A : Type u} [CommRing A] (I : Ideal A) (m : ℕ) :=
  GradedPiece (CanonicalFiltration I) m

abbrev GradedRingPiece_mk {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) : GradedRingPiece I m := ⟦x⟧

notation "⟦" x "⟧ₘ" => GradedRingPiece_mk x

@[simp]
lemma GradedRingPiece_mk_out {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : GradedRingPiece I m) :
    ⟦x.out⟧ₘ = x :=
  Quotient.out_eq x

@[simp]
lemma GradedRingPiece_mk_eq_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} {x y : (CanonicalFiltration I).N m} :
    x.1 - y.1 ∈ (CanonicalFiltration I).N (m+1) ↔ ⟦x⟧ₘ = ⟦y⟧ₘ := by
  rw [Quotient.eq'']
  rw [(Submodule.quotientRel_def
            (Submodule.comap ((CanonicalFiltration I).N m).subtype
              ((CanonicalFiltration I).N (m + 1))))]
  simp

@[simp]
lemma GradedRingPiece_mk_zero {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} :
    ⟦0⟧ₘ = (0 : GradedRingPiece I m) := rfl

lemma GradedRingPiece_mk_zero_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) :
    ↑x ∈ (CanonicalFiltration I).N (m+1) ↔ ⟦x⟧ₘ = 0 := by
  rw [←GradedRingPiece_mk_zero]
  rw [←GradedRingPiece_mk_eq_iff]
  simp

lemma GradedRingPiece_eq_zero_iff {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} {x : GradedRingPiece I m} :
    x = (0 : GradedRingPiece I m) ↔ ↑x.out ∈ (CanonicalFiltration I).N (m+1) := by
  rw [←Quotient.out_eq x]
  rw [←GradedRingPiece_mk_zero]
  rw [←GradedRingPiece_mk_eq_iff]
  simp

@[simp]
lemma GradedRingPiece_out_mk_sub {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) :
    ↑(⟦x⟧ₘ.out - x) ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedRingPiece_mk_eq_iff.mpr
  simp

lemma GradedRingPiece_mk_add {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x y : (CanonicalFiltration I).N m) :
  ⟦x + y⟧ₘ = ⟦x⟧ₘ + ⟦y⟧ₘ := rfl

lemma GradedRingPiece_mk_neg {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : (CanonicalFiltration I).N m) :
  ⟦-x⟧ₘ = -⟦x⟧ₘ := rfl

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

lemma ideal_mul_comm_coe {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    (↑(ideal_mul I m n x y) : A) = (↑(ideal_mul I n m y x) : A) := by
  rw [ideal_mul_eval]
  rw [ideal_mul_eval]
  apply mul_comm

abbrev one_cf {A : Type u} [CommRing A] {I : Ideal A} : (CanonicalFiltration I).N 0 := ⟨(1 : A), by simp⟩

lemma ideal_one_mul {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul I 0 n one_cf x = ⟨↑x, by rw [zero_add]; exact x.2⟩ := by
  unfold ideal_mul
  simp

lemma ideal_mul_one {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul I n 0 x one_cf = x := by
  unfold ideal_mul
  simp

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
  apply GradedRingPiece_eq_zero_iff.mp rfl

abbrev one_gp {A : Type u} [CommRing A] {I : Ideal A} : GradedRingPiece I 0 := ⟦one_cf⟧

lemma graded_one_mul {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    graded_mul I one_gp ⟦x⟧ₘ =
      (⟦(⟨(↑x : A), by rw [zero_add]; exact x.2⟩ : (CanonicalFiltration I).N (0 + n))⟧ : GradedRingPiece I (0 + n)) := by
  rw [graded_mul_of_mk]
  rw [ideal_one_mul]


/--
  Let `F : ℕ → Submodule A A` denote the Canonical Filtration given by `F m = I^m`.
  If `x ∈ F m` and `y ∈ F n` such that `m = n` and `↑x = ↑y : A`, then `⟦x⟧ : GradedRingPiece I m` and `⟦y⟧ : GradedRingPiece I n` are heterogenously equal.
-/
lemma aux₁ {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} {x : (CanonicalFiltration I).N m} {y : (CanonicalFiltration I).N n} (hxy : (↑x : A) = (↑y : A)) (h : m = n):
    HEq ⟦x⟧ₘ ⟦y⟧ₘ := by
  subst h
  have : x = y := SetLike.coe_eq_coe.mp hxy
  subst this
  exact HEq.refl ⟦x⟧ₘ

/--
  The map `ℕ → Type` given by `GradedRingPiece I` defines a
  graded ring structure.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMul (GradedRingPiece I) where
  mul := graded_mul I

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GOne (GradedRingPiece I) where
  one := one_gp

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GNonUnitalNonAssocSemiring (GradedRingPiece I) where
  mul_zero := by
    intro m n a
    calc graded_mul I a 0 = graded_mul I ⟦a.out⟧ₘ 0 := by rw [GradedRingPiece_mk_out]
        _ = graded_mul I ⟦a.out⟧ₘ ⟦0⟧ₘ := by rw [←GradedRingPiece_mk_zero]
        _ = ⟦ideal_mul I m n a.out 0⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦0⟧ₘ := by rw [ideal_mul_zero]
  zero_mul := by
    intro m n b
    calc graded_mul I 0 b = graded_mul I  0 ⟦b.out⟧ₘ := by rw [GradedRingPiece_mk_out]
        _ = graded_mul I ⟦0⟧ₘ ⟦b.out⟧ₘ := by rw [←GradedRingPiece_mk_zero]
        _ = ⟦ideal_mul I m n 0 b.out⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦0⟧ₘ := by rw [ideal_zero_mul]
  mul_add := sorry
  add_mul := sorry

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMonoid (GradedRingPiece I) where
  one_mul := by
    intro ⟨n, a⟩
    apply Sigma.ext
    · simp
    simp
    rw [←Quotient.out_eq a]
    show HEq (graded_mul I one_gp _) _
    rw [graded_one_mul a.out]
    apply aux₁
    simp
    exact zero_add n
  mul_one := by
    intro ⟨n, a⟩
    apply Sigma.ext
    · rfl
    simp
    calc
      graded_mul I a one_gp = graded_mul I ⟦a.out⟧ₘ one_gp := by rw [GradedRingPiece_mk_out]
        _ = graded_mul I ⟦a.out⟧ₘ ⟦one_cf⟧ₘ := rfl
        _ = ⟦ideal_mul I n 0 a.out one_cf⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦a.out⟧ₘ := by rw [ideal_mul_one]; rfl
        _ = (a : GradedRingPiece I n) := by rw [GradedRingPiece_mk_out]
  mul_assoc := sorry

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GCommMonoid (GradedRingPiece I) where
  mul_comm := by
    rintro ⟨m, x⟩ ⟨n, y⟩
    apply Sigma.ext
    · show (m + n) = (n + m)
      exact add_comm m n
    · simp
      show HEq (graded_mul I _ _) (graded_mul I _ _)
      unfold graded_mul
      apply aux₁
      · exact ideal_mul_comm_coe _ _
      · exact add_comm _ _

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GSemiring (GradedRingPiece I) where
  natCast := fun n => ⟦⟨n, by simp⟩⟧ₘ
  natCast_zero := by
    simp
    rfl
  natCast_succ := by
    intro n
    show _ = _ + one_gp
    rw [←GradedRingPiece_mk_add]
    simp

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GRing (GradedRingPiece I) where
  intCast := fun n => ⟦⟨n, by simp⟩⟧ₘ
  intCast_ofNat := by
    intro n
    simp
    rfl
  intCast_negSucc_ofNat := by
    intro n
    show ⟦_⟧ₘ = -⟦_⟧ₘ
    rw [←GradedRingPiece_mk_neg]
    congr
    simp

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommSemiring (GradedRingPiece I) where

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommRing (GradedRingPiece I) where

/-
  It follows that `G(A)` is a commutative ring.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) :=
  DirectSum.commRing _

/-
  `G(A)` should be an `A`-algebra
-/


def algebraMap_fn₁ {A : Type u} [CommRing A] (I : Ideal A) : A →  (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) := fun a => ⟦(⟨a, by simp⟩)⟧


def algebraMap_fn₁_morphism {A : Type u} [CommRing A] (I : Ideal A) : A →+*(GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) where
  toFun := algebraMap_fn₁ I
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def algebraMap_fn₂ {A : Type u} [CommRing A] (I : Ideal A) :
    (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) → AssociatedGradedRing I := fun a
 => (DirectSum.of _ 0 a )


def algebraMap_fn₂_morphism {A : Type u} [CommRing A] (I : Ideal A) : (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) →+* AssociatedGradedRing I where
  toFun := algebraMap_fn₂ I
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry


def AssociatedGradedRing_algebraMap {A : Type u} [CommRing A] (I : Ideal A) : A →+* AssociatedGradedRing I := (algebraMap_fn₂_morphism I).comp (algebraMap_fn₁_morphism I)



instance {A : Type u} [CommRing A] (I : Ideal A) : Algebra A (AssociatedGradedRing I) where
  smul a x := a • x
  algebraMap := AssociatedGradedRing_algebraMap I
  commutes' := sorry
  smul_def' := sorry

end AssociatedGradedRing

/-
  `Gₐ(M)` should be an `Gₐ(A)`-module
-/
instance {A : Type u} [CommRing A] {I : Ideal A} {M : Type u}
    [AddCommGroup M] [Module A M] (F : I.Filtration M) :
    Module (AssociatedGradedRing I) (AssociatedGradedModule F) where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry




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
