import MyProject.am10_23
import MyProject.adic_completion
import MyProject.AssociatedGradedRing.Map
import Mathlib

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)

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

lemma DirectProductFiltration_mem_iff {F : ∀ i, I.Filtration (β i)} (n : ℕ) {x : (∀ i, β i)} :
    x ∈ (DirectProductFiltration ι β F).N n ↔ ∀ i, x i ∈ (F i).N n := by
  exact { mp := fun a i ↦ a i trivial, mpr := fun a i a_1 ↦ a i }

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
   ∃ s : Multiset ((AssociatedGradedModule F) × (n : ℕ) × (F.N n)),
    x = (s.map Prod.fst).sum ∧ ∀ x ∈ s, x.1 = DirectSum.of _ x.2.1 ⟦x.2.2⟧ₘ := by
  apply @DirectSum.induction_on ℕ (GradedPiece F) _ _ _ x
  · use ∅
    simp
  · intro i y
    use {(DirectSum.of _ i y, Sigma.mk i y.out)}
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
  If `G(M)` is finitely generated as a `G(A)`-module, then there exists a finite generating list
  `[(x₁, n₁, y₁), …, (xₖ, nₖ, yₖ)]`, such that for each `1 ≤ i ≤ k`, `xᵢ = ⟦yᵢ⟧ₘ` where `yᵢ : F.N nᵢ`, i.e. each
  `xᵢ` is homogeneous of degree `nᵢ`.
-/
lemma AssociatedGradedModule.exists_generators_as_list_of_fg
  [hFin : Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule F)] :
   ∃ s : List ((AssociatedGradedModule F) × (n : ℕ) × (F.N n)),
    (Submodule.span (AssociatedGradedRing I) (Prod.fst '' {x | x ∈ s}) : Submodule (AssociatedGradedRing I) (AssociatedGradedModule F)) = ⊤ ∧
    ∀ x ∈ s, x.1 = DirectSum.of _ x.2.1 ⟦x.2.2⟧ₘ:= by
  -- Fix a basis `s` of `G(M)`
  rcases hFin with ⟨s, hs⟩

  -- For each `x : s`, split `x` into homogeneous parts
  let β : s → Multiset ((AssociatedGradedModule F) × (n : ℕ) × (F.N n)) := by
    intro x
    exact (AssociatedGradedModule.split F x).choose
  have β_spec : ∀ x : s,
      x = ((β x).map Prod.fst).sum ∧ ∀ y ∈ (β x), y.1 = DirectSum.of _ y.2.1 ⟦y.2.2⟧ₘ := by
    intro x
    exact (AssociatedGradedModule.split F x).choose_spec

  -- Now unite all elements of `β` into one multiset
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
    have : {x | x ∈ γ} = {x | x ∈ γ.toList} := by simp
    rw [←this]
    have h₁ : Prod.fst '' {z | z ∈ β ⟨x, hx⟩} ⊆ Prod.fst '' {z | z ∈ Finset.univ.sum β} := by
      apply Set.image_mono ?_
      intro z hz
      simp
      exact ⟨x, hx, hz⟩
    apply Submodule.span_mono h₁
    have := multiset_sum_mem_span (AssociatedGradedRing I) ((β ⟨x, hx⟩).map Prod.fst)
    convert this
    ext x
    simp
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
  rcases AssociatedGradedModule.exists_generators_as_list_of_fg F with ⟨s, s_gen, s_hg⟩

  -- Define `R := ⊕ (i : Fin n), A`
  set ι := Fin s.length
  set β : ι → Type u := (fun i ↦ A)
  set R : Type u := ∀ i : ι, (β i)

  set d : ι → ℕ := fun i ↦ (s.get i).2.1
  set y : ι → M := fun i ↦ (s.get i).2.2

  set F' : I.Filtration R := DirectProductFiltration ι β (fun i ↦ (OffSetFiltration (CanonicalFiltration I) (d i)))

  -- Define a map `R → M` by sending `(xᵢ)ᵢ ↦ ∑ᵢ xᵢ ⬝ yᵢ`.
  set φ : R →ₗ[A] M := {
    toFun := fun x ↦ ∑ i, x i • y i
    map_add' := by
      intro a b
      rw [←Finset.sum_add_distrib]
      congr
      ext i
      rw [←add_smul]
      rfl
    map_smul' := by
      intro a b
      rw [Finset.smul_sum]
      congr
      ext i
      rw [smul_smul]
      rfl
  }
  have φ_apply : ∀ x : R, φ x = ∑ i, x i • y i := fun x ↦ rfl

  -- `φ` satisfies `F'.N n ⊆ φ⁻¹(F.N n)` for all n
  have : ∀ n, (F'.N n) ≤ (F.N n).comap φ := by
    intro n x hx
    show ∑ i, x i • y i ∈ F.N n
    suffices : ∀ i, x i • y i ∈ F.N n
    · exact Submodule.sum_mem (F.N n) fun c a ↦ this c
    intro i
    apply IFiltration_I_pow_sub_smul_le F n (d i)
    apply Submodule.smul_mem_smul
    · rw [←canonicalFiltration_eval]
      exact (DirectProductFiltration_mem_iff ι β n).mp hx i
    · exact Submodule.coe_mem (s.get i).2.2

  -- `φ` induces a map `Gφ : G(R) → G(M)`
  set Gφ : AssociatedGradedModule F' →ₗ[AssociatedGradedRing I] AssociatedGradedModule F := GradedModuleHom this

  -- `Gφ` is surjective
  have : Function.Surjective Gφ := by
    rw [←LinearMap.range_eq_top]
    apply le_antisymm (le_top)
    rw [←s_gen]
    apply Submodule.span_le.mpr
    rintro x ⟨p, h₁, rfl⟩
    simp at h₁
    have : ∃ i : Fin s.length, s.get i = p := List.mem_iff_get.mp h₁
    rcases this with ⟨i, rfl⟩
    simp
    use (DirectSum.of _ (d i) ⟦⟨fun j ↦ if i = j then 1 else 0, by
      rw [DirectProductFiltration_mem_iff]
      intro j
      by_cases hij : i = j
      · subst hij
        simp
        show 1 ∈ (I^((d i) - (d i)) • ⊤)
        simp
      · simp [hij]
    ⟩⟧ₘ)
    apply DirectSum.ext
    intro m
    rw [s_hg _]
    rw [GradedModuleHom_apply]
    by_cases hm : m = d i
    case neg
    · push_neg at hm
      show _ = DirectSum.of (GradedPiece F) (d i) ⟦(s.get i).2.2⟧ₘ m
      rw [DirectSum.of_eq_of_ne _ _ _ hm.symm]
      rw [DirectSum.of_eq_of_ne _ _ _ hm.symm]
      simp
    subst hm
    show _ = DirectSum.of (GradedPiece F) (d i) ⟦(s.get i).2.2⟧ₘ (d i)
    rw [DirectSum.of_eq_same]
    rw [DirectSum.of_eq_same]
    show ⟦_⟧ₘ = ⟦_⟧ₘ
    congr
    apply Subtype.coe_inj.mp
    show φ _ = y i
    simp
    rw [φ_apply]
    simp
    exact h₁

  have φ_hat : True → True := sorry
  have : Function.Surjective φ_hat := sorry
  have : Function.Surjective φ := sorry

  exact Module.Finite.of_surjective φ this
