import MyProject.AssociatedGradedRing.GradedSMul

open DirectSum

variable {A : Type u} [CommRing A] {I : Ideal A}

lemma canonicalFiltration_mul_deg {m n : ℕ} {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    x * y ∈ (CanonicalFiltration I).N (m + n) := by
  rw [mem_filtration_iff_mem_Im] at *
  exact SetLike.GradedMul.mul_mem hx hy

/--
  Let `A` be a ring and `I` be an ideal. Then for `m n : ℕ` we obtain a multiplication map
  `I^m → I^n → I^(m+n)`
-/
def ideal_mul {m n : ℕ} :
    (CanonicalFiltration I).N m →ₗ[A]
      (CanonicalFiltration I).N n →ₗ[A]
        (CanonicalFiltration I).N (m + n) :=
  filtration_smul

lemma ideal_mul_eval {m n : ℕ} {x y : A} (hx : x ∈ (CanonicalFiltration I).N m) (hy : y ∈ (CanonicalFiltration I).N n) :
    ↑(ideal_mul ⟨x, hx⟩ ⟨y, hy⟩ : A) = ↑(x * y) := rfl

lemma ideal_mul_zero {m : ℕ} (n : ℕ) (x : (CanonicalFiltration I).N m) :
    ideal_mul x (0 : (CanonicalFiltration I).N n) = 0 :=
  LinearMap.map_zero (ideal_mul x)

lemma ideal_zero_mul (m : ℕ) {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul (0 : (CanonicalFiltration I).N m) x = 0 :=
  LinearMap.map_zero₂ ideal_mul x

lemma ideal_add_mul {m n : ℕ} (x y : (CanonicalFiltration I).N m) (z : (CanonicalFiltration I).N n) :
    ideal_mul (x + y) z = ideal_mul x z + ideal_mul y z :=
  LinearMap.map_add₂ ideal_mul x y z

lemma ideal_mul_add {m n : ℕ} (x : (CanonicalFiltration I).N m) (y z : (CanonicalFiltration I).N n) :
    ideal_mul x (y + z) = ideal_mul x y + ideal_mul x z :=
  LinearMap.map_add (ideal_mul x) y z

lemma ideal_smul_mul {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    ideal_mul (a • x) y = a • (ideal_mul x y) :=
  LinearMap.map_smul₂ ideal_mul a x y

lemma ideal_mul_smul {m n : ℕ} (a : A) (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    ideal_mul x (a • y) = a • (ideal_mul x y) :=
  LinearMap.map_smul (ideal_mul x) a y

abbrev one_cf : (CanonicalFiltration I).N 0 := ⟨(1 : A), by simp⟩

lemma ideal_one_mul {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul one_cf x = ⟨↑x, by rw [zero_add]; exact x.2⟩ :=
  filtration_one_fsmul x

lemma ideal_mul_one {n : ℕ} (x : (CanonicalFiltration I).N n) :
    ideal_mul x one_cf = x := by
  unfold ideal_mul
  unfold filtration_smul
  simp

lemma ideal_mul_comm_coe {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    (↑(ideal_mul x y) : A) = (↑(ideal_mul y x) : A) := by
  rw [ideal_mul_eval, ideal_mul_eval]
  exact mul_comm _ _

lemma ideal_mul_assoc_coe {k m n : ℕ} (x : (CanonicalFiltration I).N k) (y : (CanonicalFiltration I).N m) (z : (CanonicalFiltration I).N n) :
    (↑(ideal_mul (ideal_mul x y) z) : A) = (↑(ideal_mul x (ideal_mul y z)) : A) :=
  filtration_mul_smul_coe x y z

def graded_mul_hom {m n : ℕ} :
    (GradedRingPiece I m) →ₗ[A] (GradedRingPiece I n) →ₗ[A] (GradedRingPiece I (m+n)) :=
  graded_smul_hom

def graded_mul {m n : ℕ} :
    (GradedRingPiece I m) → (GradedRingPiece I n) → (GradedRingPiece I (m+n)) :=
  graded_smul

lemma graded_mul_of_mk {m n : ℕ} (x : (CanonicalFiltration I).N m) (y : (CanonicalFiltration I).N n) :
    graded_mul ⟦x⟧ₘ ⟦y⟧ₘ = ⟦ideal_mul x y⟧ₘ := by
  rfl

lemma graded_mul_to_mk {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (x : GradedRingPiece I m) (y : GradedRingPiece I n) :
    graded_mul x y = ⟦ideal_mul x.out y.out⟧ₘ := by
  nth_rw 1 [←GradedPiece_mk_out x]
  nth_rw 1 [←GradedPiece_mk_out y]
  rfl

lemma GradedRingPiece_zero {A : Type u} [CommRing A] {I : Ideal A} (m : ℕ) :
    ↑(0 : GradedRingPiece I m).out ∈ (CanonicalFiltration I).N (m+1) := by
  apply GradedPiece_eq_zero_iff.mp rfl

abbrev one_gp {A : Type u} [CommRing A] {I : Ideal A} : GradedRingPiece I 0 := ⟦one_cf⟧

lemma graded_one_mul {A : Type u} [CommRing A] {I : Ideal A} {n : ℕ} (x : (CanonicalFiltration I).N n) :
    graded_mul one_gp ⟦x⟧ₘ =
      ⟦(⟨(↑x : A), by rw [zero_add]; exact x.2⟩ : (CanonicalFiltration I).N (0 + n))⟧ₘ := by
  rw [graded_mul_of_mk]
  rw [ideal_one_mul]

/--
  The map `ℕ → Type` given by `GradedRingPiece I` defines a
  graded ring structure.
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMul (GradedRingPiece I) where
  mul := graded_mul

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GOne (GradedRingPiece I) where
  one := one_gp

instance {A : Type u} [CommRing A] (I : Ideal A) : GNonUnitalNonAssocSemiring (GradedRingPiece I) where
  mul_zero := fun a ↦ LinearMap.map_zero (graded_mul_hom a)
  zero_mul := fun a ↦ LinearMap.map_zero₂ graded_mul_hom a
  mul_add := fun a b c ↦ LinearMap.map_add (graded_mul_hom a) b c
  add_mul := fun a b c ↦ LinearMap.map_add₂ graded_mul_hom a b c

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GMonoid (GradedRingPiece I) where
  one_mul := by
    intro ⟨n, a⟩
    show (⟨0 + n, graded_mul ⟦one_cf⟧ₘ a⟩ : GradedMonoid (GradedRingPiece I)) = ⟨n, a⟩
    rw [←Quotient.out_eq a]
    apply AssociatedGradedModule.ext
    · exact zero_add n
    rw [filtration_one_fsmul a.out]
  mul_one := by
    intro ⟨n, a⟩
    show (⟨n + 0, graded_mul a ⟦one_cf⟧ₘ⟩ : GradedMonoid (GradedRingPiece I)) = ⟨n, a⟩
    rw [←Quotient.out_eq a]
    apply AssociatedGradedModule.ext rfl
    exact Subtype.eq_iff.mp (ideal_mul_one a.out)
  mul_assoc := by
    intro ⟨k, a⟩ ⟨m, b⟩ ⟨n, c⟩
    show (⟨k + m + n, graded_mul (graded_mul a b) c⟩ : GradedMonoid (GradedRingPiece I)) =
        ⟨k + (m + n), graded_mul a (graded_mul b c)⟩
    rw [←Quotient.out_eq a]
    rw [←Quotient.out_eq b]
    rw [←Quotient.out_eq c]
    apply AssociatedGradedModule.ext
    · exact add_assoc k m n
    exact ideal_mul_assoc_coe _ _ _

instance {A : Type u} [CommRing A] (I : Ideal A) : GradedMonoid.GCommMonoid (GradedRingPiece I) where
  mul_comm := by
    rintro ⟨m, x⟩ ⟨n, y⟩
    show (⟨m + n, graded_mul x y⟩ : GradedMonoid (GradedRingPiece I)) = ⟨n + m, graded_mul y x⟩
    rw [←Quotient.out_eq x]
    rw [←Quotient.out_eq y]
    apply AssociatedGradedModule.ext
    · exact add_comm m n
    exact ideal_mul_comm_coe x.out y.out

instance {A : Type u} [CommRing A] (I : Ideal A) : GSemiring (GradedRingPiece I) where
  natCast := fun n => ⟦⟨n, by simp⟩⟧ₘ
  natCast_zero := by simp; rfl
  natCast_succ := by
    intro n
    show _ = _ + one_gp
    rw [←GradedPiece_mk_add]
    simp

instance {A : Type u} [CommRing A] (I : Ideal A) : GRing (GradedRingPiece I) where
  intCast := fun n => ⟦⟨n, by simp⟩⟧ₘ
  intCast_ofNat := by intro n; simp; rfl
  intCast_negSucc_ofNat := by
    intro n
    show ⟦_⟧ₘ = -⟦_⟧ₘ
    rw [←GradedPiece_mk_neg]
    congr
    simp

instance {A : Type u} [CommRing A] (I : Ideal A) : GCommSemiring (GradedRingPiece I) where

instance {A : Type u} [CommRing A] (I : Ideal A) : GCommRing (GradedRingPiece I) where

/-
  It follows that `G(A)` is a commutative ring.
-/
instance {A : Type u} [CommRing A] (I : Ideal A) : CommRing (AssociatedGradedRing I) :=
  DirectSum.commRing _
