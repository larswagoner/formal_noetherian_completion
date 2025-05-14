import MyProject.am10_3
import MyProject.Completion.GroupCompletion

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/


section

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

def am10_4 (n : ℕ) :
    (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) ≃+ G ⧸ F.N n := by
  let G₁ := F.N n
  let G₂ := G
  let G₃ := G ⧸ F.N n
  let q : G₁ →+ G₂ := (F.N n).subtype
  let p : G₂ →+ G₃ := QuotientAddGroup.mk' (F.N n)
  have h₁ : Function.Injective q := AddSubgroup.subtype_injective (F.N n)
  have h₂ : Function.Exact q p := by
    unfold Function.Exact
    intro y
    constructor
    · intro h
      have : y ∈ F.N n := (QuotientAddGroup.eq_zero_iff y).mp h
      use ⟨y, this⟩
      rfl
    · rintro ⟨⟨x, hx⟩, rfl⟩
      show p x = 0
      exact (QuotientAddGroup.eq_zero_iff x).mpr hx
  have h₃ : Function.Surjective p := QuotientAddGroup.mk'_surjective (F.N n)
  have c₁ := am10_3_inj q F
  have c₂ := am10_3_exact q p F
  have c₃ := am10_3_surj p F
  let G₃_c := (OurFiltrationCompletion (PushforwardOurFiltration p F))
  have : OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+
            OurFiltrationCompletion F ⧸ (map₂ p F).ker := by sorry
  have : OurFiltrationCompletion F ⧸ (map₂ p F).ker ≃+ G₃_c :=
    QuotientAddGroup.quotientKerEquivOfSurjective (map₂ p F) c₃

  show OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+ G ⧸ F.N n
  sorry



end
