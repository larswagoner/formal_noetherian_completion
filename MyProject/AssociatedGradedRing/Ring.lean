import MyProject.AssociatedGradedRing.Basic

open DirectSum

variable {A : Type u} [CommRing A] (I : Ideal A)

/--
  `CanonicalFiltration I` is an abbreviation for `I.stableFiltration (⊤ : Submodule A A)` and is thus given by the filtration `n ↦ Iⁿ`.
-/
abbrev CanonicalFiltration := I.stableFiltration (⊤ : Submodule A A)

lemma canonicalFiltration_eval (m : ℕ) :
    (CanonicalFiltration I).N m = I ^ m := by simp

lemma mem_filtration_iff_mem_Im (m : ℕ) (x : A) :
    x ∈ (CanonicalFiltration I).N m ↔ x ∈ I^m := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

lemma canonicalFiltration_mul_deg {I : Ideal A} {m n : ℕ} {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    x * y ∈ (CanonicalFiltration I).N (m + n) := by
  rw [mem_filtration_iff_mem_Im] at *
  exact SetLike.GradedMul.mul_mem hx hy


/--
  `GradedRingPiece I m` is an abbreviation for `GradedPiece (CanonicalFiltration I) m` and thus informally reduces to `Iᵐ/Iᵐ⁺¹`.
-/
abbrev GradedRingPiece (m : ℕ) :=
  GradedPiece (CanonicalFiltration I) m

/--
  Let `A` be a ring and `I` be an ideal. Then for `m n : ℕ` we obtain a multiplication map
  `I^m → I^n → I^(m+n)`
-/
def ideal_mul {m n : ℕ} :
    (CanonicalFiltration I).N m →ₗ[A]
      (CanonicalFiltration I).N n →ₗ[A]
        (CanonicalFiltration I).N (m + n) where
  toFun := fun x ↦ {
    toFun := fun y ↦ ⟨x.1 * y.1, canonicalFiltration_mul_deg x.2 y.2⟩
    map_add' := fun y z ↦ by
      simp
      ring
    map_smul' := fun y z ↦ by
      simp
      ring
  }
  map_add' := fun x y ↦ by
    ext z
    simp
    ring
  map_smul' := fun x y ↦ by
    ext z
    simp
    ring

lemma ideal_mul_eval {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    ↑(ideal_mul I ⟨x, hx⟩ ⟨y, hy⟩ : A) = ↑(x * y) := rfl

lemma ideal_mul_zero {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) (x : (CanonicalFiltration I).N m) :
    ideal_mul I x (0 : (CanonicalFiltration I).N n) = 0 := by
  unfold ideal_mul
  simp

lemma ideal_zero_mul {A : Type u} [CommRing A] {I : Ideal A} (m n : ℕ) (x : (CanonicalFiltration I).N n) :
    ideal_mul I (0 : (CanonicalFiltration I).N m) x = 0 := by
  unfold ideal_mul
  simp

lemma ideal_add_mul {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (x y : (CanonicalFiltration I).N m) (z : (CanonicalFiltration I).N n) :
    ideal_mul I (x + y) z = (ideal_mul I x z) + (ideal_mul I y z) :=
  LinearMap.map_add₂ (ideal_mul I) x y z

lemma ideal_mul_add {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (x : (CanonicalFiltration I).N m) (y z : (CanonicalFiltration I).N n) :
    ideal_mul I x (y + z) = (ideal_mul I x y) + (ideal_mul I x z) :=
  LinearMap.map_add (ideal_mul I x) y z

lemma ideal_smul_mul {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    ideal_mul I (a • x) y = a • (ideal_mul I x y) :=
  LinearMap.map_smul₂ (ideal_mul I) a x y

lemma ideal_mul_smul {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    ideal_mul I x (a • y) = a • (ideal_mul I x y) :=
  LinearMap.map_smul (ideal_mul I x) a y

abbrev one_cf {A : Type u} [CommRing A] {I : Ideal A} : (CanonicalFiltration I).N 0 := ⟨(1 : A), by simp⟩

lemma ideal_one_mul {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul I one_cf x = ⟨↑x, by rw [zero_add]; exact x.2⟩ := by
  unfold ideal_mul
  simp

lemma ideal_mul_one {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul I x one_cf = x := by
  unfold ideal_mul
  simp

lemma ideal_mul_comm_coe {A : Type u} [CommRing A] {I : Ideal A} {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    (↑(ideal_mul I x y) : A) = (↑(ideal_mul I y x) : A) := by
  rw [ideal_mul_eval]
  rw [ideal_mul_eval]
  apply mul_comm





def graded_mul_left {A : Type u} [CommRing A] (I : Ideal A) (m n : ℕ) :
    (CanonicalFiltration I).N m →ₗ[A] (GradedRingPiece I n) →ₗ[A] (GradedRingPiece I (m+n)) where
  toFun := fun x ↦ Submodule.mapQ _ _ (ideal_mul I x) (by
      intro y h
      convert (canonicalFiltration_mul_deg x.2 h)
    )
  map_add' := by
    intro x y
    ext ⟨t⟩
    show ⟦ideal_mul I (x + y) t⟧ₘ = _
    rw [ideal_add_mul]
    rfl
  map_smul' := by
    intro a x
    ext ⟨t⟩
    show ⟦ideal_mul I (a • x) t⟧ₘ = _
    rw [ideal_smul_mul]
    rfl

def graded_mul_hom {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} :
    (GradedRingPiece I m) →ₗ[A] (GradedRingPiece I n) →ₗ[A] (GradedRingPiece I (m+n)) :=
  Submodule.liftQ _ (graded_mul_left I m n) (by
    intro x h
    ext ⟨y⟩
    show ⟦ideal_mul I x y⟧ₘ = 0
    rw [←GradedPiece_mk_zero_iff]
    convert canonicalFiltration_mul_deg h y.2 using 2
    abel
  )

def graded_mul {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} :
    (GradedRingPiece I m) → (GradedRingPiece I n) → (GradedRingPiece I (m+n)) :=
  fun x y ↦ graded_mul_hom I x y

lemma graded_mul_of_mk {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    graded_mul I ⟦x⟧ₘ ⟦y⟧ₘ = ⟦ideal_mul I x y⟧ₘ := by
  rfl

lemma graded_mul_to_mk {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (x : GradedRingPiece I m) (y : GradedRingPiece I n) :
    graded_mul_hom I x y = ⟦ideal_mul I x.out y.out⟧ₘ := by
  nth_rw 1 [←GradedPiece_mk_out x]
  nth_rw 1 [←GradedPiece_mk_out y]
  rfl

lemma GradedRingPiece_zero {A : Type u} [CommRing A] {I : Ideal A} (m : ℕ) :
    ↑(0 : GradedRingPiece I m).out ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedPiece_eq_zero_iff.mp rfl

abbrev one_gp {A : Type u} [CommRing A] {I : Ideal A} : GradedRingPiece I 0 := ⟦one_cf⟧

lemma graded_one_mul {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    graded_mul I one_gp ⟦x⟧ₘ =
      ⟦(⟨(↑x : A), by rw [zero_add]; exact x.2⟩ : (CanonicalFiltration I).N (0 + n))⟧ₘ := by
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
instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMul (GradedRingPiece I) where
  mul := graded_mul I

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GOne (GradedRingPiece I) where
  one := one_gp

instance {A : Type u} [CommRing A] (I : Ideal A) : GNonUnitalNonAssocSemiring (GradedRingPiece I) where
  mul_zero := fun a ↦ LinearMap.map_zero ((graded_mul_hom I) a)
  zero_mul := fun a ↦ LinearMap.map_zero₂ (graded_mul_hom I) a
  mul_add := fun a b c ↦ LinearMap.map_add ((graded_mul_hom I) a) b c
  add_mul := fun a b c ↦ LinearMap.map_add₂ (graded_mul_hom I) a b c

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMonoid (GradedRingPiece I) where
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
      graded_mul I a one_gp = graded_mul I ⟦a.out⟧ₘ one_gp := by rw [GradedPiece_mk_out]
        _ = graded_mul I ⟦a.out⟧ₘ ⟦one_cf⟧ₘ := rfl
        _ = ⟦ideal_mul I a.out one_cf⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦a.out⟧ₘ := by rw [ideal_mul_one]; rfl
        _ = (a : GradedRingPiece I n) := by rw [GradedPiece_mk_out]
  mul_assoc := sorry

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GCommMonoid (GradedRingPiece I) where
  mul_comm := by
    rintro ⟨m, x⟩ ⟨n, y⟩
    apply Sigma.ext
    · show (m + n) = (n + m)
      exact add_comm m n
    · simp
      show HEq (graded_mul I _ _) (graded_mul I _ _)
      unfold graded_mul
      rw [graded_mul_to_mk]
      rw [graded_mul_to_mk]
      apply aux₁
      · exact ideal_mul_comm_coe _ _
      · exact add_comm _ _

instance {A : Type u} [CommRing A] (I : Ideal A) : GSemiring (GradedRingPiece I) where
  natCast := fun n => ⟦⟨n, by simp⟩⟧ₘ
  natCast_zero := by
    simp
    rfl
  natCast_succ := by
    intro n
    show _ = _ + one_gp
    rw [←GradedPiece_mk_add]
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
    rw [←GradedPiece_mk_neg]
    congr
    simp

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommSemiring (GradedRingPiece I) where

noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : GCommRing (GradedRingPiece I) where

/-
  It follows that `G(A)` is a commutative ring.
-/
noncomputable instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) :=
  DirectSum.commRing _
