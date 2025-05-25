import MyProject.AssociatedGradedRing.Ring

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

section GradedStarRing

variable {A : Type*} [CommRing A]

def GradedStarRing (I : Ideal A) : Type _ :=
  ⨁ n : ℕ, ↥(I^n)

def GradedStarRing.of {I : Ideal A} {n : ℕ} (x : ↥(I^n)) :
  GradedStarRing I := DirectSum.of _ n x

instance (I : Ideal A) : AddCommGroup (GradedStarRing I) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, ↥(I^n)))

instance (I : Ideal A) :
    DFunLike (GradedStarRing I) _ fun n : ℕ => ↥(I^n) :=
  inferInstanceAs (DFunLike (Π₀ n, ↥(I^n)) _ _)

instance (I : Ideal A) :
    CoeFun (GradedStarRing I) fun _ => ∀ n : ℕ, ↥(I^n) :=
  inferInstanceAs (CoeFun (Π₀ n, ↥(I^n)) fun _ => ∀ n : ℕ, ↥(I^n))

instance (I : Ideal A) : Module A (GradedStarRing I) := by
  unfold GradedStarRing
  infer_instance

end GradedStarRing

section

variable {A : Type*} [CommRing A] {I : Ideal A}

-- SetLike.GradedMul.mul_mem

/--
  Let `A` be a ring and `I` be an ideal. Then for `m n : ℕ` we obtain a multiplication map
  `I^m → I^n → I^(m+n)`
-/
def star_ideal_mul {m n : ℕ} :
    ↥(I^m) →ₗ[A] ↥(I^n) →ₗ[A] ↥(I^(m + n)) where
  toFun := fun x ↦ {
    toFun := fun y ↦ ⟨x.1 * y.1, SetLike.GradedMul.mul_mem x.2 y.2⟩
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

@[simp]
lemma star_ideal_mul_eval {m n : ℕ} {x y : A} (hx : x ∈ I^m) (hy : y ∈ I^n) :
    ↑(star_ideal_mul ⟨x, hx⟩ ⟨y, hy⟩ : A) = ↑(x * y) := rfl

lemma star_ideal_mul_zero {m : ℕ} (n : ℕ) (x : ↥(I^m)) :
    star_ideal_mul x (0 : ↥(I^n)) = 0 :=
  LinearMap.map_zero (star_ideal_mul x)

lemma star_ideal_zero_mul (m : ℕ) {n : ℕ} (x : ↥(I^n)) :
    star_ideal_mul (0 : ↥(I^m)) x = 0 :=
  LinearMap.map_zero₂ star_ideal_mul x

lemma star_ideal_add_mul {m n : ℕ} (x y : ↥(I^m)) (z : ↥(I^n)) :
    star_ideal_mul (x + y) z = star_ideal_mul x z + star_ideal_mul y z :=
  LinearMap.map_add₂ star_ideal_mul x y z

lemma star_ideal_mul_add {m n : ℕ} (x : ↥(I^m)) (y z : ↥(I^n)) :
    star_ideal_mul x (y + z) = star_ideal_mul x y + star_ideal_mul x z :=
  LinearMap.map_add (star_ideal_mul x) y z

lemma star_ideal_smul_mul {m n : ℕ} (a : A) (x : ↥(I^m)) (y : ↥(I^n)) :
    star_ideal_mul (a • x) y = a • (star_ideal_mul x y) :=
  LinearMap.map_smul₂ star_ideal_mul a x y

lemma star_ideal_mul_smul {m n : ℕ} (a : A) (x : ↥(I^m)) (y : ↥(I^n)) :
    star_ideal_mul x (a • y) = a • (star_ideal_mul x y) :=
  LinearMap.map_smul (star_ideal_mul x) a y

abbrev one_star_ideal : ↥(I^0) := ⟨(1 : A), by simp⟩

lemma star_ideal_one_mul {n : ℕ} (x : ↥(I^n)) :
    star_ideal_mul one_star_ideal x = ⟨↑x, by rw [zero_add]; exact x.2⟩ := by
  unfold star_ideal_mul
  simp

lemma star_ideal_mul_one {n : ℕ} (x : ↥(I^n)) :
    star_ideal_mul x one_star_ideal = x := by
  unfold star_ideal_mul
  simp

lemma star_ideal_mul_comm_coe {m n : ℕ} (x : ↥(I^m)) (y : ↥(I^n)) :
    (↑(star_ideal_mul x y) : A) = (↑(star_ideal_mul y x) : A) := by
  rw [star_ideal_mul_eval, star_ideal_mul_eval]
  exact mul_comm _ _

lemma star_ideal_mul_assoc_coe {k m n : ℕ}(x : ↥(I^k)) (y : ↥(I^m)) (z : ↥(I^n)) :
    (↑(star_ideal_mul (star_ideal_mul x y) z) : A) = (↑(star_ideal_mul x (star_ideal_mul y z)) : A) := by
  rw [star_ideal_mul_eval, star_ideal_mul_eval, star_ideal_mul_eval, star_ideal_mul_eval]
  ring

lemma GradedStarRing.ext {m n : ℕ} (x : ↥(I^m)) (y : ↥(I^n)) (h : m = n) (hxy : x.1 = y.1):
    (⟨m, x⟩ : GradedMonoid (fun n ↦ ↥(I^n))) = ⟨n, y⟩ := by
  subst h
  simp
  exact SetLike.coe_eq_coe.mp hxy

/--
  The map `ℕ → Type` given by `GradedRingPiece I` defines a
  graded ring structure.
-/
instance (I : Ideal A) : GradedMonoid.GMul (fun n ↦ ↥(I^n)) where
  mul := fun x y ↦ ⟨x.1 * y.1, SetLike.GradedMul.mul_mem x.2 y.2⟩

instance (I : Ideal A) : GradedMonoid.GOne (fun n ↦ ↥(I^n)) where
  one := one_star_ideal

instance (I : Ideal A) : GNonUnitalNonAssocSemiring (fun n ↦ ↥(I^n)) where
  mul_zero := fun a ↦ LinearMap.map_zero (star_ideal_mul a)
  zero_mul := fun a ↦ LinearMap.map_zero₂ star_ideal_mul a
  mul_add := fun a b c ↦ LinearMap.map_add (star_ideal_mul a) b c
  add_mul := fun a b c ↦ LinearMap.map_add₂ star_ideal_mul a b c

instance (I : Ideal A) : GradedMonoid.GMonoid (fun n ↦ ↥(I^n)) where
  one_mul := by
    rintro ⟨n, a⟩
    simp
  mul_one := by
    rintro ⟨n, a⟩
    simp
  mul_assoc := by
    rintro ⟨k, a⟩ ⟨m, b⟩ ⟨n, c⟩
    apply GradedStarRing.ext
    · exact add_assoc k m n
    exact star_ideal_mul_assoc_coe _ _ _

instance (I : Ideal A) : GradedMonoid.GCommMonoid (fun n ↦ ↥(I^n)) where
  mul_comm := by
    rintro ⟨m, x⟩ ⟨n, y⟩
    apply GradedStarRing.ext
    · exact (add_comm m n)
    exact (star_ideal_mul_comm_coe x y)

instance (I : Ideal A) : GSemiring (fun n ↦ ↥(I^n)) where
  natCast := fun n => ⟨n, by simp⟩
  natCast_zero := by simp
  natCast_succ := by
    intro n
    show _ = _ + one_star_ideal
    simp

instance (I : Ideal A) : GRing (fun n ↦ ↥(I^n)) where
  intCast := fun n => ⟨n, by simp⟩
  intCast_ofNat := by intro n; simp; rfl
  intCast_negSucc_ofNat := by
    intro n
    show _ = -_
    congr
    simp
    have : -(1 : A) + -↑n = -↑(n + 1) := by simp
    rw [this]
    rfl

instance (I : Ideal A) : GCommSemiring (fun n ↦ ↥(I^n)) where

instance (I : Ideal A) : GCommRing (fun n ↦ ↥(I^n)) where

/-
  It follows that `G(A)` is a commutative ring.
-/
instance (I : Ideal A) : CommRing (GradedStarRing I) :=
  DirectSum.commRing (fun n ↦ ↥(I^n))

end

section

variable {A : Type*} [CommRing A] {I : Ideal A}

@[simp]
lemma GradedStarRing_add (x y : GradedStarRing I) (n : ℕ) : (x + y) n = x n + y n := rfl

def GradedStarRing_mk {n : ℕ} (y : ↥(I^n)) : GradedStarRing I := DirectSum.of _ n y

lemma gradedStarRing_mul_0 (x : GradedStarRing I) (y : ↥(I^1)) :
    (x * GradedStarRing_mk y) 0 = 0 := by
  induction' x using DirectSum.induction_on with n hx x y hx hy
  · simp
  · unfold GradedStarRing_mk
    rw [DirectSum.of_mul_of]
    rfl
  · rw [add_mul]
    simp [hx, hy]


lemma gradedStarRing_mul_succ (y : ↥(I^1)) (x : GradedStarRing I) (n : ℕ) :
    (x * GradedStarRing_mk y) (n+1) = ⟨(x n) * y, SetLike.GradedMul.mul_mem (x n).2 y.2⟩ := by
  induction' x using DirectSum.induction_on with i hx x x' hx hx'
  · simp
    rfl
  · unfold GradedStarRing_mk
    apply Subtype.coe_inj.mp
    rw [DirectSum.of_mul_of]
    simp
    by_cases h : i = n
    · rw [←h]
      rw [DirectSum.of_eq_same]
      rw [DirectSum.of_eq_same]
      rfl
    · rw [DirectSum.of_eq_of_ne]
      rw [DirectSum.of_eq_of_ne]
      simp
      exact h
      exact (Nat.succ_ne_succ).mpr h
  · rw [add_mul]
    simp [hx, hx']
    rw [add_mul]
