import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.SModEq

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M] (F : I.Filtration M)

lemma IFiltration_I_pow_sub_smul_le (m n : ℕ) :
    I^(m - n) • F.N n ≤ F.N m := by
  by_cases h : m < n
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h)]
    simp
    exact Ideal.Filtration.antitone F (le_of_lt h)
  · have := Ideal.Filtration.pow_smul_le F (m - n) n
    convert this
    push_neg at h
    exact (Nat.sub_eq_iff_eq_add h).mp rfl

/--
  Let `M` be a module with a filtration `{Mₙ}ₙ`. Then for any `m : ℕ` we can form the filtration
  given by `{Mₙ₋ₘ}ₙ`.
-/
def OffsetFiltration (m : ℕ) : I.Filtration M where
  N := fun n ↦ F.N (n - m)
  mono := by
    intro i
    by_cases h : i < m
    · rw [Nat.sub_eq_zero_of_le h]
      rw [Nat.sub_eq_zero_of_le (le_of_lt h)]
    · push_neg at h
      rw [Nat.sub_add_comm h]
      exact F.mono (i - m)
  smul_le := by
    intro i
    by_cases h : i < m
    · rw [Nat.sub_eq_zero_of_le h]
      rw [Nat.sub_eq_zero_of_le (le_of_lt h)]
      exact Submodule.smul_le_right
    · push_neg at h
      rw [Nat.sub_add_comm h]
      exact F.smul_le (i - m)

@[simp]
lemma offsetFiltration_eval_add (m n : ℕ) :
    (OffsetFiltration F m).N (n + m) = F.N n := by
  unfold OffsetFiltration
  simp

@[simp]
lemma offsetFiltration_eval_le {m n : ℕ} (h : n ≤ m) :
    (OffsetFiltration F m).N n = F.N 0 := by
  unfold OffsetFiltration
  simp
  rw [Nat.sub_eq_zero_of_le h]

end

section

variable {R : Type*} {ι : Type*} [CommSemiring R] {φ : ι → Type*} [(i : ι) → AddCommGroup (φ i)]
variable [(i : ι) → Module R (φ i)]

/--
  For any direct product `∏ₙ Mₙ` of `A`-modules and ideal `I` of `A`, we have an inclusion
  `I • ∏ₙ Mₙ ⊆ ∏ₙ (I • Mₙ)`
-/
lemma Submodule.pi_smul (I : Set ι) (p : (i : ι) → Submodule R (φ i)) (A : Ideal R) :
    A • (Submodule.pi I p) ≤ Submodule.pi I (fun i ↦ A • (p i)) := by
  intro x h i iI
  simp
  rw [(span_eq (pi I p)).symm, ←Ideal.span_eq A, span_smul_span] at h
  revert h x
  apply Submodule.span_induction
  · intro x hx
    simp at hx
    rcases hx with ⟨_, ha, _, hy, rfl⟩
    exact smul_mem_smul ha (hy i iI)
  · simp
  · intro _ _ _ _ p q
    simp
    exact Submodule.add_mem _ p q
  · intro a _ _ hxj
    simp
    exact Submodule.smul_mem _ a hxj

end

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable (ι : Type*) (β : ι → Type*) [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)]

/--
  Given a collection `{Mᵢ}` of modules and an `I`-filtration `Fᵢ` on each module `Mᵢ`, we can form
  the product filtration `F` given by `F(n) = ∏ᵢ Fᵢ(n) ⊆ ∏ᵢ Mᵢ`.
-/
def DirectProductFiltration (F : ∀ i, I.Filtration (β i)) : I.Filtration (∀ i, β i) where
  N := fun n ↦ (Submodule.pi Set.univ (fun i ↦ (F i).N n))
  mono := fun n x hx i _ ↦ by
    simp at hx
    exact (F i).mono n (hx i)
  smul_le := fun n x hx i _ ↦ by
    apply (F i).smul_le n
    have := Submodule.pi_smul _ _ _ hx
    simp at this
    exact (this i)

lemma DirectProductFiltration_mem_iff {F : ∀ i, I.Filtration (β i)} (n : ℕ) {x : (∀ i, β i)} :
    x ∈ (DirectProductFiltration ι β F).N n ↔ ∀ i, x i ∈ (F i).N n := by
  exact { mp := fun a i ↦ a i trivial, mpr := fun a i a_1 ↦ a i }

lemma DirectProductFiltration_mod_iff {F : ∀ i, I.Filtration (β i)} (n : ℕ) {x y : (∀ i, β i)} :
    x ≡ y [SMOD (DirectProductFiltration ι β F).N n] ↔ ∀ i, x i ≡ y i [SMOD (F i).N n] := by
  rw [SModEq.sub_mem]
  rw [DirectProductFiltration_mem_iff]
  rw [forall_congr']
  intro a
  rw [SModEq.sub_mem]
  rfl

end
