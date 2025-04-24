import MyProject.AssociatedGradedRing.Basic

open DirectSum

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
    ideal_mul I m n (0 : (CanonicalFiltration I).N m) x = 0 := by
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
  apply GradedPiece_mk_eq_iff.mp
  rw [ideal_mul_eval, ideal_mul_eval]
  have : (↑(⟦x⟧ : GradedRingPiece I m).out : A) * ↑(⟦y⟧ : GradedRingPiece I n).out - ↑x * ↑y =
      ((⟦x⟧ : GradedRingPiece I m).out - x) * (⟦y⟧ : GradedRingPiece I n).out + x * ((⟦y⟧ : GradedRingPiece I n).out - y) := by ring
  rw [this]
  apply Submodule.add_mem
  · have := canonicalFiltration_mul_deg (GradedPiece_out_mk_sub x) (⟦y⟧ : GradedRingPiece I n).out.2
    convert this using 2
    ring
  · have := canonicalFiltration_mul_deg x.2 (GradedPiece_out_mk_sub y)
    exact this

lemma GradedRingPiece_zero {A : Type u} [CommRing A] {I : Ideal A} (m : ℕ) :
    ↑(0 : GradedRingPiece I m).out ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedPiece_eq_zero_iff.mp rfl

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
    calc graded_mul I a 0 = graded_mul I ⟦a.out⟧ₘ 0 := by rw [GradedPiece_mk_out]
        _ = graded_mul I ⟦a.out⟧ₘ ⟦0⟧ₘ := by rw [←GradedPiece_mk_zero]
        _ = ⟦ideal_mul I m n a.out 0⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦0⟧ₘ := by rw [ideal_mul_zero]
  zero_mul := by
    intro m n b
    calc graded_mul I 0 b = graded_mul I  0 ⟦b.out⟧ₘ := by rw [GradedPiece_mk_out]
        _ = graded_mul I ⟦0⟧ₘ ⟦b.out⟧ₘ := by rw [←GradedPiece_mk_zero]
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
      graded_mul I a one_gp = graded_mul I ⟦a.out⟧ₘ one_gp := by rw [GradedPiece_mk_out]
        _ = graded_mul I ⟦a.out⟧ₘ ⟦one_cf⟧ₘ := rfl
        _ = ⟦ideal_mul I n 0 a.out one_cf⟧ₘ := by rw [graded_mul_of_mk]
        _ = ⟦a.out⟧ₘ := by rw [ideal_mul_one]; rfl
        _ = (a : GradedRingPiece I n) := by rw [GradedPiece_mk_out]
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
