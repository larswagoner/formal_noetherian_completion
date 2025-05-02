import MyProject.am10_23
import MyProject.adic_completion
import MyProject.AssociatedGradedRing.Map
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

variable {R : Type u} {ι : Type x} [CommSemiring R] {φ : ι → Type i} [(i : ι) → AddCommGroup (φ i)]
variable [(i : ι) → Module R (φ i)]

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

variable {A : Type u} [CommRing A] {I : Ideal A}
variable (ι : Type v) (β : ι → Type u) [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)]

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

end

section

variable (A : Type u) [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M]

lemma list_sum_mem_span (s : List M) :
    s.sum ∈ Submodule.span A {x | x ∈ s} := by
  refine Submodule.mem_span_set'.mpr ?_
  use s.length
  use (fun n ↦ 1)
  use (fun n ↦ ⟨s.get n, by simp⟩)
  simp

lemma multiset_sum_mem_span (s : Multiset M) :
    s.sum ∈ Submodule.span A {x | x ∈ s} := by
  rw [(Multiset.sum_toList s).symm]
  convert list_sum_mem_span A s.toList using 2
  simp

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)

/- NOTE: I used multiset here because with Finset, I ran in DecidableEq-problems
  If `x ∈ G(M)`, then there exists a finite decomposition `x = ∑ᵢ yᵢ`, where each
  `yᵢ` is homogeneous of degree `nᵢ
-/
lemma AssociatedGradedModule.split (x : AssociatedGradedModule F) :
   ∃ s : Multiset (AssociatedGradedModule F),
    x = s.sum ∧ ∀ y ∈ s, ∃ n : ℕ, ∃ y' : F.N n, y = DirectSum.of _ n ⟦y'⟧ₘ := by
  apply @DirectSum.induction_on ℕ (GradedPiece F) _ _ _ x
  · use ∅
    simp
  · intro i y
    use {DirectSum.of _ i y}
    simp
    use i
    use y.out
    simp
  · rintro x y ⟨sx, hx_sum, hx_deg⟩ ⟨sy, hy_sum, hy_deg⟩
    use sx + sy
    constructor
    · simp
      rw [hx_sum, hy_sum]
    · intro z hz
      rcases Multiset.mem_add.mp hz with hzx | hzy
      · exact hx_deg z hzx
      · exact hy_deg z hzy


/-
  If `G(M)` is finitely generated as a `G(A)`-module, then there exists a finite generating set
  `{x₁, …, xₙ}`, such that for each `1 ≤ i ≤ n`, `xᵢ = ⟦y⟧ₘ` for some `y : F.N nᵢ`, i.e. each
  `xᵢ` is homogeneous of degree `nᵢ`.
-/
lemma AssociatedGradedModule.exists_generators_of_fg
  [hFin : Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F)] :
   ∃ s : Multiset (AssociatedGradedModule F),
    (Submodule.span (AssociatedGradedRing I) {x | x ∈ s} : Submodule (AssociatedGradedRing I) (AssociatedGradedModule F)) = ⊤ ∧
    ∀ x ∈ s, ∃ n : ℕ, ∃ y : F.N n, x = DirectSum.of _ n ⟦y⟧ₘ:= by
  rcases hFin with ⟨s, hs⟩
  let β : s → Multiset (AssociatedGradedModule F) := by
    intro x
    exact (AssociatedGradedModule.split F x).choose

  have β_spec : ∀ x : s, x = (β x).sum ∧ ∀ y ∈ (β x), ∃ n : ℕ, ∃ y' : F.N n, y = DirectSum.of _ n ⟦y'⟧ₘ := by
    intro x
    exact (AssociatedGradedModule.split F x).choose_spec

  use Finset.univ.sum β
  constructor
  · apply le_antisymm
    · exact le_top
    rw [←hs]
    apply Submodule.span_le.mpr
    intro x hx
    have := (β_spec ⟨x, hx⟩).1
    simp at this
    rw [this]
    have : {z | z ∈ β ⟨x, hx⟩} ⊆ {z | z ∈ Finset.univ.sum β} := by
      intro z hz
      simp
      exact ⟨x, hx, hz⟩
    apply Submodule.span_mono this
    apply multiset_sum_mem_span
  · intro x hx
    rw [Multiset.mem_sum] at hx
    rcases hx with ⟨i, i_univ, hx⟩
    exact (β_spec i).2 x hx

/-
  If `G(M)` is finitely generated as a `G(A)`-module, then there exists a finite generating list
  `[x₁, …, xₙ]`, such that for each `1 ≤ i ≤ n`, `xᵢ = ⟦y⟧ₘ` for some `y : F.N nᵢ`, i.e. each
  `xᵢ` is homogeneous of degree `nᵢ`.
-/
lemma AssociatedGradedModule.exists_generators_as_list_of_fg
  [hFin : Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F)] :
   ∃ s : List (AssociatedGradedModule F),
    (Submodule.span (AssociatedGradedRing I) {x | x ∈ s} : Submodule (AssociatedGradedRing I) (AssociatedGradedModule F)) = ⊤ ∧
    ∀ x ∈ s, ∃ n : ℕ, ∃ y : F.N n, x = DirectSum.of _ n ⟦y⟧ₘ:= by
  rcases hFin with ⟨s, hs⟩
  let β : s → Multiset (AssociatedGradedModule F) := by
    intro x
    exact (AssociatedGradedModule.split F x).choose

  have β_spec : ∀ x : s, x = (β x).sum ∧ ∀ y ∈ (β x), ∃ n : ℕ, ∃ y' : F.N n, y = DirectSum.of _ n ⟦y'⟧ₘ := by
    intro x
    exact (AssociatedGradedModule.split F x).choose_spec

  set γ := Finset.univ.sum β
  use γ.toList
  constructor
  · apply le_antisymm
    · exact le_top
    rw [←hs]
    apply Submodule.span_le.mpr
    intro x hx
    have := (β_spec ⟨x, hx⟩).1
    simp at this
    rw [this]
    have h₁ : {z | z ∈ β ⟨x, hx⟩} ⊆ {z | z ∈ Finset.univ.sum β} := by
      intro z hz
      simp
      exact ⟨x, hx, hz⟩
    have : {x | x ∈ γ} = {x | x ∈ γ.toList} := by simp
    rw [←this]
    apply Submodule.span_mono h₁
    apply multiset_sum_mem_span
  · intro x hx
    rw [Multiset.mem_toList] at hx
    rw [Multiset.mem_sum] at hx
    rcases hx with ⟨i, i_univ, hx⟩
    exact (β_spec i).2 x hx



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

  -- Let `s : Multiset (AssociatedGradedModule F)` consist of homogeneous elements that generate `G(M)`.
  rcases AssociatedGradedModule.exists_generators_of_fg F with ⟨s, s_gen, s_hom⟩

  -- Define `R := ⊕ (i : Fin n), A`
  set ι := Fin s.card
  set β : ι → Type u := (fun i ↦ A)
  set R : Type u := ∀ i : ι, (β i)
  set incl_ι : ι → (AssociatedGradedModule F) := by
    sorry

  set F' : I.Filtration R := DirectProductFiltration ι β (fun i ↦ (OffSetFiltration (CanonicalFiltration I) 2))

  -- Define a map `R → M` by sending `(aᵢ)ᵢ ↦ ∑ᵢ aᵢ ⬝ xᵢ`.
  set φ : R →ₗ[A] M := by
    set R' : Type u := DirectSum ι β
    set ψ : R' →ₗ[A] M :=
      DirectSum.toModule A ι M (by
        intro i
        sorry
      )
    set ψ' : R ≃ₗ[A] R' := (DirectSum.linearEquivFunOnFintype A ι β).symm
    sorry

  have : ∀ n, (F'.N n) ≤ (F.N n).comap φ := sorry
  have Gφ : AssociatedGradedModule F' → AssociatedGradedModule F := GradedModuleHom this
  have : Function.Surjective Gφ := sorry

  have φ_hat : True → True := sorry
  have : Function.Surjective φ_hat := sorry
  have : Function.Surjective φ := sorry

  exact Module.Finite.of_surjective φ this
