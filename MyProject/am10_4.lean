import MyProject.am10_3
import MyProject.Completion.GroupCompletion

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/


section

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

/--
  If `G/Gₙ` is given a filtration by pushing `{Gₙ}ₙ` forwards along `q : G → G/Gₙ`, then it has a
  discrete topology so that its completion is isomorphic to `G/Gₙ`.
-/
def am10_4_aux (n : ℕ) :
  G ⧸ (F.N n) ≃+
    OurFiltrationCompletion (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F)
  where
    __ := OurFiltrationCompletion.of (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F)
    invFun := fun x ↦ QuotientAddGroup.quotientQuotientEquivQuotient (F.N n) (F.N n) (le_refl _) (x.1 n)
    left_inv := by
      rintro ⟨x⟩
      rfl
    right_inv := by
      intro x
      ext i
      show ⟦ _ ⟧ = _
      simp
      by_cases h : i ≤ n
      · rw [←x.2 h]
        rw [←Quotient.out_eq (x.1 n)]
        rw [←Quotient.out_eq (x.1 n).out]
        rfl
      · have hni : n ≤ i := by linarith
        let F' := (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F)
        suffices : Function.Injective (OFISTransitionMap F' hni)
        · apply (Function.Injective.eq_iff this).mp
          simp
          rw [←Quotient.out_eq (x.1 n)]
          rw [←Quotient.out_eq (x.1 n).out]
          rfl
        rintro ⟨x⟩ ⟨y⟩ hxy
        let f : OurFiltrationIS F' n → OurFiltrationIS F' i :=
          QuotientAddGroup.map _ _ (AddMonoidHom.id (G ⧸ F.N n)) (by
            simp [F', PushforwardOurFiltration]
          )
        have := congrArg f hxy
        exact this

/--
  The map `G/Gₙ → G^/(Gₙ)^`. This map will be shown to be an isomorphism.
-/
def am10_4_aux₂ (n : ℕ) :
    G ⧸ (F.N n) →+ (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) :=
  QuotientAddGroup.map (F.N n) (AddSubgroupCompletion (F.N n) F)
    (OurFiltrationCompletion.of F) (AddSubgroupCompletion_le_comap (F.N n) F)

/--
  The map `G^/(Gₙ)^ → (G/Gₙ)^`. By lemma 10.3, we know that this map is bijective.
-/
def am10_4_aux₃ (n : ℕ) :
  (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) →
    OurFiltrationCompletion (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F) :=
  QuotientAddGroup.lift (AddSubgroupCompletion (F.N n) F)
    (@OurFiltrationCompletionHom.of_comap_le G (G ⧸ F.N n) _ _ F (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F) (QuotientAddGroup.mk' (F.N n)) (fun _ ↦ AddSubgroup.le_comap_map (QuotientAddGroup.mk' (F.N n)) _))
    (by
      intro x hx
      simp
      ext i
      show _ = 0
      rw [OurFiltrationCompletionHom.of_comap_le_apply]
      unfold PushforwardOurFiltration
      simp
      have := am10_3_exact (F.N n).subtype (QuotientAddGroup.mk' (F.N n)) F
      rcases (x.1 i) with ⟨y⟩
      show ⟦ _ ⟧ = _
      sorry
      -- show ⟦ _ ⟧ = 0
    )

lemma am10_4_aux₂_bijective (n : ℕ) :
  Function.Bijective (am10_4_aux₂ F n) := sorry

noncomputable def am10_4 (n : ℕ) :
  G ⧸ (F.N n) ≃+
    (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) :=
  AddEquiv.ofBijective (am10_4_aux₂ F n) (am10_4_aux₂_bijective F n)
  -- by
  -- let G₁ := F.N n
  -- let G₂ := G
  -- let G₃ := G ⧸ (F.N n)
  -- let q : G₁ →+ G₂ := (F.N n).subtype
  -- let p : G₂ →+ G₃ := QuotientAddGroup.mk' (F.N n)
  -- have h₁ : Function.Injective q := AddSubgroup.subtype_injective (F.N n)
  -- have h₂ : Function.Exact q p := by
  --   unfold Function.Exact
  --   intro y
  --   constructor
  --   · intro h
  --     have : y ∈ F.N n := (QuotientAddGroup.eq_zero_iff y).mp h
  --     use ⟨y, this⟩
  --     rfl
  --   · rintro ⟨⟨x, hx⟩, rfl⟩
  --     show p x = 0
  --     exact (QuotientAddGroup.eq_zero_iff x).mpr hx
  -- have h₃ : Function.Surjective p := QuotientAddGroup.mk'_surjective (F.N n)
  -- have c₁ := am10_3_inj q F
  -- have c₂ := am10_3_exact q p F
  -- have c₃ := am10_3_surj p F
  -- let G₃_c := (OurFiltrationCompletion (PushforwardOurFiltration p F))
  -- have f₁ : OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+
  --           OurFiltrationCompletion F ⧸ (map₂ p F).ker := by sorry
  -- have f₂ : OurFiltrationCompletion F ⧸ (map₂ p F).ker ≃+ G₃_c :=
  --   QuotientAddGroup.quotientKerEquivOfSurjective (map₂ p F) c₃

  -- show OurFiltrationCompletion F ⧸ (map₁ q F).range ≃+ G ⧸ (F.N n)
  -- exact (f₁.trans f₂).trans (am10_4_aux F n).symm

end
