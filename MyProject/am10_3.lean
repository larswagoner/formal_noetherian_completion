import MyProject.am10_2
import MyProject.Filtration.FConstructions
import MyProject.Completion.OurFiltrationCompletion
import Mathlib.Algebra.Exact

/-
  # Corollary 10.3
  Let `0 ⟶ G' ⟶p G ⟶q G'' ⟶ 0` be an exact sequence of groups.
  Let `G` have the topology defined by a sequence `{Gₙ}` of subgroups and
  give `G', G''` the induced topologies, i.e. by `{p⁻¹Gₙ}, {qGₙ}`.
  Then `0 ⟶ Ĝ' ⟶ Ĝ ⟶ Ĝ'' ⟶ 0` is exact.
-/

section aux

section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {N' : AddSubgroup H}
/--
  For map `φ : G →+ H`, and `N' ⊆ H`, the map `G'/φ⁻¹N' → H/N'` is injective.
  NOTE: This should probably be a standard result somewhere, but I could not find it.
-/
lemma QutoientAddGroup.map_injective_of_comap (φ : G →+ H) :
  Function.Injective
    (QuotientAddGroup.map (N'.comap φ) N' φ (by rfl)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a⟩ ha
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact (QuotientAddGroup.eq_zero_iff (φ a)).mp ha

variable {N : AddSubgroup G} {φ : G →+ H} (hφ : N ≤ N'.comap φ)

/--
  Let `φ : G →+ H` be surjective. Then for any `N ⊆ G, N' ⊆ H` with `N ⊆ φ⁻¹ N'`, the induced map
  `G/N →+ H/N'` is surjective.
  NOTE: This should probably be a standard result, but I could not find it.
-/
lemma QuotientAddGroup.map_surjective_of_surjective (φ_surj : Function.Surjective φ) :
  Function.Surjective
    (QuotientAddGroup.map N N' φ hφ) := by
  let q₂ := QuotientAddGroup.mk' N
  let q₃ := QuotientAddGroup.map N N' φ hφ
  suffices : Function.Surjective (q₃ ∘ q₂)
  exact Function.Surjective.of_comp this
  have : q₃ ∘ q₂ = (QuotientAddGroup.mk' N') ∘ φ := by ext x; rfl
  rw [this]
  apply Function.Surjective.comp
  exact QuotientAddGroup.mk'_surjective N'
  exact φ_surj

end


variable {G₁ G₂ G₃ : Type*} [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃] {N : AddSubgroup G₂}
variable {f : G₁ →+ G₂} {g : G₂ →+ G₃}

/--
  If `f` and `g` are exact, then the image of the map `G₁/f⁻¹N → G₂/N` coincides with the kernel of `G₂/N → G₃/gN`.
  NOTE: This might also be a standard result, which I could not find.
-/
lemma QuotientAddGroup.map_exact_of_exact (h : Function.Exact f g) :
    (QuotientAddGroup.map (N.comap f) N f (by rfl)).range =
      (QuotientAddGroup.map N (N.map g) g (N.le_comap_map g)).ker
       := by
  ext x
  constructor
  · rintro ⟨⟨y⟩, rfl⟩
    show _ = 0
    rw [QuotientAddGroup.map_map]
    show ⟦ g (f y) ⟧ = _
    rw [Function.Exact.apply_apply_eq_zero h y]
    rfl
  · rintro hx
    rcases x with ⟨x⟩
    show ⟦ _ ⟧ ∈ _
    have : g x ∈ (N.map g) := (QuotientAddGroup.eq_zero_iff _).mp hx
    rcases this with ⟨y, hy, g_eq⟩
    let z := x - y
    have : z ∈ Set.range f := by
      rw [←h z]
      simp [z, g_eq]
    rcases this with ⟨z', hz'⟩
    use ⟦z'⟧
    simp
    rw [hz']
    unfold z
    simp
    exact hy

end aux

variable {G₁ G₂ G₃ : Type u} [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
variable (p : G₁ →+ G₂) (q : G₂ →+ G₃)
variable (F : OurFiltration G₂)

def am10_3AddInverseSystemSES (h₂ : Function.Exact p q) (h₃ : Function.Surjective q) :
  AddInverseSystemSES
    (OFISTransitionMap (PullbackOurFiltration p F))
    (OFISTransitionMap F)
    (OFISTransitionMap (PushforwardOurFiltration q F)) where
  ψ := OFISystemHom.of_comap_le (PullbackOurFiltration p F) F p (fun n ↦ by rfl)
  ϕ := OFISystemHom.of_comap_le F (PushforwardOurFiltration q F) q (fun _ ↦ AddSubgroup.le_comap_map q _)
  inj := fun n ↦ QutoientAddGroup.map_injective_of_comap p
  mid := fun n ↦ QuotientAddGroup.map_exact_of_exact h₂
  surj := fun n ↦ QuotientAddGroup.map_surjective_of_surjective (AddSubgroup.le_comap_map q _) h₃

lemma am10_3_inj (h₂ : Function.Exact p q) (h₃ : Function.Surjective q) :
    Function.Injective (OurFiltrationCompletionHom.of_comap_le (PullbackOurFiltration p F) F p (fun n ↦ by rfl)) :=
  am10_2_i_inj (am10_3AddInverseSystemSES p q F h₂ h₃)

lemma am10_3_exact (h₂ : Function.Exact p q) (h₃ : Function.Surjective q) :
    Function.Exact
      (OurFiltrationCompletionHom.of_comap_le (PullbackOurFiltration p F) F p (fun n ↦ by rfl))
      (OurFiltrationCompletionHom.of_comap_le F (PushforwardOurFiltration q F) q (fun _ ↦ AddSubgroup.le_comap_map q _)) :=
  am10_2_i_exactMiddle (am10_3AddInverseSystemSES p q F h₂ h₃)

lemma am10_3_surj (h₂ : Function.Exact p q) (h₃ : Function.Surjective q) :
    Function.Surjective
      (OurFiltrationCompletionHom.of_comap_le F (PushforwardOurFiltration q F) q (fun _ ↦ AddSubgroup.le_comap_map q _)) := by
  apply am10_2_ii (am10_3AddInverseSystemSES p q F h₂ h₃)
  unfold SurjectiveSystem
  intro n m h
  apply QuotientAddGroup.map_surjective_of_surjective
  exact Function.RightInverse.surjective (congrFun rfl)
