import MyProject.am10_3
import MyProject.Completion.GroupCompletion

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/


section

variable {G : Type u} [AddCommGroup G]
-- variable {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] (F : OurFiltration G σ)
variable (F : OurFiltration G (AddSubgroup G))

/--
  If `G/Gₙ` is given a filtration by pushing `{Gₙ}ₙ` forwards along `q : G → G/Gₙ`, then it has a
  discrete topology so that its completion is isomorphic to `G/Gₙ`.
-/
def am10_4_aux (n : ℕ) :
  G ⧸ (AddSubgroup.ofClass (F.N n)) ≃+
    (OurFiltrationCompletion (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F))
  where
    __ := OurFiltrationCompletion.of (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F)
    invFun := by
      intro x
      -- exact QuotientAddGroup.quotientQuotientEquivQuotient
      --   (F.N n)
      --   (AddSubgroup.ofClass (F.N n))
      --   (le_refl _)
      --   x
      apply (QuotientAddGroup.quotientBot).toFun
      have y := x.1 n
      dsimp [OurFiltrationIS, PushforwardOurFiltration ] at y
      have := QuotientAddGroup.quotientQuotientEquivQuotient
        (F.N n)
        (AddSubgroup.ofClass (F.N n))
        (le_refl _)
      sorry
    left_inv := by
      simp
      sorry
    right_inv := sorry


def am10_4 (n : ℕ) :
    (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) ≃+
      G ⧸ (AddSubgroup.ofClass (F.N n)) := by
  let G₁ := F.N n
  let G₂ := G
  let G₃ := G ⧸ (AddSubgroup.ofClass (F.N n))
  let q : G₁ →+ G₂ := (AddSubgroupClass.subtype (F.N n))
  let p : G₂ →+ G₃ := QuotientAddGroup.mk' (AddSubgroup.ofClass (F.N n))
  have h₁ : Function.Injective q := AddSubgroupClass.subtype_injective (F.N n)
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
  have h₃ : Function.Surjective p := QuotientAddGroup.mk'_surjective (AddSubgroup.ofClass (F.N n))
  have c₁ := am10_3_inj q F
  have c₂ := am10_3_exact q p F
  have c₃ := am10_3_surj p F
  let G₃_c := (OurFiltrationCompletion (PushforwardOurFiltration p F))
  have : OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+
            OurFiltrationCompletion F ⧸ (map₂ p F).ker := by sorry
  have : OurFiltrationCompletion F ⧸ (map₂ p F).ker ≃+ G₃_c :=
    QuotientAddGroup.quotientKerEquivOfSurjective (map₂ p F) c₃

  show OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+ G ⧸ (AddSubgroup.ofClass (F.N n))
  sorry


end
