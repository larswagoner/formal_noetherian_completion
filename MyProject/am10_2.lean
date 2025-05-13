import Mathlib.Order.DirectedInverseSystem
import Mathlib.Algebra.Module.SnakeLemma
import MyProject.Completion.NaiveInverseLimit


/-
  # Proposition 10.2
  Let `0 ⟶ {Aₙ} ⟶ {Bₙ} ⟶ {Cₙ} ⟶ 0` be an exact sequence of inverse systems, then
  i) `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ` is exact
  ii) If `{Aₙ}` is a surjective system, then `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ ⟶ 0` is exact.
-/

variable {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AddInverseSystem f]

@[simp]
lemma derivedKernelIsCoherent (a : (DerivedMap f).ker) ⦃n m : ℕ⦄ (h : n ≤ m) : (f h) (a.1 m) = a.1 n := by
  induction h using Nat.leRec with
  | refl =>
    simp
  | le_succ_of_le h ih =>
    rw [<- ih]
    expose_names
    have hh : (DerivedMap f) a = 0 := a.2
    have h₃ : a.1 k - f (Nat.le_succ k) (a.1 (k+1)) = 0 := by
      unfold DerivedMap at hh
      simp at hh
      exact congrFun hh k
    rw [eq_of_sub_eq_zero h₃]
    simp

theorem kernelDerivedEqNaiveInverseLimit : (DerivedMap f).ker = NaiveAddInverseLimit f := by
  ext x
  constructor
  · intro hx n m h
    exact derivedKernelIsCoherent ⟨x, hx⟩ h
  · intro hx
    simp
    ext n
    unfold DerivedMap
    simp [hx]



lemma am10_2_i : true := sorry
lemma am10_2_ii : true := sorry
