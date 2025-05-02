import MyProject.am10_23
import MyProject.adic_completion
import Mathlib

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)

def OffSetFiltration (m : ℕ) : I.Filtration M where
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

end

section
variable {A : Type u} [Semiring A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

lemma Submodule.smul_mem_to_exist {N : Submodule A M} {x : M} (h : x ∈ I • N) :
    ∃ a : I, ∃ n : N, x = a • n := by
  sorry

end

section

variable {R : Type u} {ι : Type x} [Semiring R] {φ : ι → Type i} [(i : ι) → AddCommGroup (φ i)]
variable [(i : ι) → Module R (φ i)]

lemma Submodule.pi_smul (I : Set ι) (p : (i : ι) → Submodule R (φ i)) (A : Ideal R) :
    A • (Submodule.pi I p) ≤ Submodule.pi I (fun i ↦ A • (p i)) := by
  intro x h i iI
  rcases Submodule.smul_mem_to_exist h with ⟨a, ⟨y, hy⟩, hay⟩
  simp
  rw [hay]
  simp
  apply Submodule.smul_mem_smul
  exact coe_mem a
  exact hy i iI

end

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {ι : Type u} {β : ι → Type u} [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)]
variable (F : ∀ i, I.Filtration (β i))

def DirectProductFiltration : I.Filtration (∀ i, β i) where
  N := fun n ↦ (Submodule.pi Set.univ (fun i ↦ (F i).N n))
  mono := fun n x hx i _ ↦ by
    simp at hx
    exact (F i).mono n (hx i)
  smul_le := fun n x hx i _ ↦ by
    apply (F i).smul_le n
    have := Submodule.pi_smul _ _ _ hx
    simp at this
    exact (this i)

end

/-
  # Proposition 10.24
  Let `A` be a ring, `I` an ideal of `A`, `M` an `A`-module, `(Mₙ)` an
  `I`-filtration of `M`. Suppose `A` is complete in the `I`-topology
  and that `M` is Hausdorff in its filtration topology (i.e. `⋂ₙ Mₙ = 0`).
  Suppose also that `G(M)` is a finitely generated `G(A)`-module.
  Then `M` is finitely-generated `A`-module.
-/

-- Will probably use Function.Surjective.of_comp_left

lemma am10_24 {A : Type u} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)
    (hF :  ⨅ n, F.N n = (⊥ : Submodule A M))  -- Best way to add `⋂ₙ Mₙ = 0`?
    [hFin : Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F)] : Module.Finite A M := by

  -- Let `s : Fin n → G(M)` map onto a set of generators of `G(M)`, say `i ↦ xᵢ`
  rcases @Module.Finite.exists_fin _ _ _ _ _ hFin with ⟨n, s, hs⟩

  -- Define `R := ⊕ (i : Fin n), A`
  set β : Fin n → Type u := (fun i ↦ A)
  set R : Type u := DirectSum (Fin n) β

  -- Then `R` is a finite `A`-module
  have : Module.Finite A R := by
    set R' : Type u := ∀ i : Fin n, (β i)
    set ψ : R ≃ₗ[A] R' := DirectSum.linearEquivFunOnFintype A (Fin n) β
    exact Module.Finite.equiv (id ψ.symm)

  -- Define a map `R → M` by sending `(aᵢ)ᵢ ↦ ∑ᵢ aᵢ ⬝ xᵢ`.
  set φ : R →ₗ[A] M := by
    apply DirectSum.toModule
    intro i
    sorry

  set F' : I.Filtration R := sorry
  have : ∀ n, (F'.N n) ≤ (F.N n).comap φ  := sorry
  have Gφ : AssociatedGradedModule F' → AssociatedGradedModule F := sorry
  have : Function.Surjective Gφ := sorry
  have : Function.Surjective φ := sorry
  sorry
