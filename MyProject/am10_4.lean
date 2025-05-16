import MyProject.am10_3
import MyProject.Completion.GroupCompletion

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/



section aux

variable {G : Type u} [AddCommGroup G] (H : AddSubgroup G)

lemma am10_4_aux_subtype_injective :
  Function.Injective H.subtype := AddSubgroup.subtype_injective H

lemma am10_4_aux_subtype_quotient_exact :
    Function.Exact H.subtype (QuotientAddGroup.mk' H) := by
  intro y
  constructor
  · intro h
    have : y ∈ H := (QuotientAddGroup.eq_zero_iff y).mp h
    use ⟨y, this⟩
    rfl
  · rintro ⟨⟨x, hx⟩, rfl⟩
    show QuotientAddGroup.mk' H x = 0
    exact (QuotientAddGroup.eq_zero_iff x).mpr hx

lemma am10_4_aux_quotient_mk_surjective :
  Function.Surjective (QuotientAddGroup.mk' H) := QuotientAddGroup.mk'_surjective H

variable (F : OurFiltration G)

/-
  Given a subgroup `H ⊆ G`, there are different (definitionally) ways to define its completion in `G^`.
  (1) Define `H^` to be the image along the map `H^ -> G^`
  (2) Define `H^` to be the kernel of the map `G^ -> (G/H)^`
  (3) In the case that `H = Gₙ`, define `H^` to be the kernel of the (projection) map `G^ → G/Gₙ`.
  There definitions are provable equal.
-/

/-
  Proof of (1) = (2)
-/

def AddSubgroupCompletion_ker_def :
  AddSubgroup (OurFiltrationCompletion F) :=
    (OurFiltrationCompletionHom.of_comap_le F (PushforwardOurFiltration (QuotientAddGroup.mk' H) F) (QuotientAddGroup.mk' H)
    (fun _ ↦ AddSubgroup.le_comap_map _ _)).ker

lemma AddSubgroupCompletion_ker_def_eq_range_def :
    AddSubgroupCompletion_ker_def H F = AddSubgroupCompletion H F :=
  AddMonoidHom.exact_iff.mp <| am10_3_exact F (am10_4_aux_subtype_quotient_exact H) (am10_4_aux_quotient_mk_surjective H)

/-
  Proof of (2) = (3)
-/

/--
  If `G/Gₙ` is given a filtration by pushing `{Gₙ}ₙ` forwards along `q : G → G/Gₙ`, then it has a
  discrete topology so that its completion is isomorphic to `G/Gₙ`.
-/
def FiltrationCompletion_of_discrete_iso (n : ℕ) :
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

def AddSubgroupCompletion_filtration_ker_def_map (n : ℕ) : (OurFiltrationCompletion F) →+ G ⧸ (F.N n) where
  toFun := fun x ↦ x.1 n
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

def AddSubgroupCompletion_filtration_ker_def (n : ℕ) :
  AddSubgroup (OurFiltrationCompletion F) :=
    (AddSubgroupCompletion_filtration_ker_def_map F n).ker

lemma AddSubgroupCompletion_ker_def_eq_filtration_ker_def (n : ℕ) :
    AddSubgroupCompletion_ker_def (F.N n) F = AddSubgroupCompletion_filtration_ker_def F n := by
  let f := AddSubgroupCompletion_filtration_ker_def_map F n
  let g := OurFiltrationCompletionHom.of_comap_le F (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F) (QuotientAddGroup.mk' (F.N n))
    (fun _ ↦ AddSubgroup.le_comap_map _ _)
  let h := (FiltrationCompletion_of_discrete_iso F n).symm
  show g.ker = f.ker
  have : f = AddMonoidHom.comp h g := by
    ext x
    show x.1 n = _
    unfold g h FiltrationCompletion_of_discrete_iso
    simp
    rw [OurFiltrationCompletionHom.of_comap_le_apply]
    rcases x.1 n with ⟨y⟩
    rfl
  rw [this]
  rw [← @AddMonoidHom.comap_ker]
  rw [show g.ker = AddSubgroup.comap g ⊥ by rfl]
  congr
  ext x
  simp

end aux

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

/--
  The map `G/Gₙ → G^/(Gₙ)^`. This map will be shown to be an isomorphism.
-/
def am10_4_map (n : ℕ) :
    G ⧸ (F.N n) →+ (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) :=
  QuotientAddGroup.map (F.N n) (AddSubgroupCompletion (F.N n) F)
    (OurFiltrationCompletion.of F) (AddSubgroupCompletion_le_comap (F.N n) F)

/--
  The map `G^/(Gₙ)^ → (G/Gₙ)^`. By lemma 10.3, we know that this map is bijective.
-/
def am10_4_aux_map₂ (n : ℕ) :
  (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) →
    OurFiltrationCompletion (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F) :=
  QuotientAddGroup.lift (AddSubgroupCompletion (F.N n) F)
    (@OurFiltrationCompletionHom.of_comap_le G (G ⧸ F.N n) _ _ F (PushforwardOurFiltration (QuotientAddGroup.mk' (F.N n)) F) (QuotientAddGroup.mk' (F.N n)) (fun _ ↦ AddSubgroup.le_comap_map (QuotientAddGroup.mk' (F.N n)) _))
    (by
      have := am10_3_exact F (am10_4_aux_subtype_quotient_exact (F.N n)) (am10_4_aux_quotient_mk_surjective (F.N n))
      rw [AddMonoidHom.exact_iff] at this
      rw [this]
      rfl
    )

lemma am10_4_aux_map₂_bijective (n : ℕ) :
  Function.Bijective (am10_4_aux_map₂ F n) := sorry

lemma am10_4_aux₂_bijective (n : ℕ) :
    Function.Bijective (am10_4_map F n) := by
  have eq : (am10_4_aux_map₂ F n).comp (am10_4_map F n) = FiltrationCompletion_of_discrete_iso F n := by ext ⟨x⟩; rfl
  have h₁ : Function.Bijective (FiltrationCompletion_of_discrete_iso F n) := (FiltrationCompletion_of_discrete_iso F n).bijective
  rw [←eq] at h₁
  exact (Function.Bijective.of_comp_iff' (am10_4_aux_map₂_bijective F n) _).mp h₁

/--
  The isomorphism `G/Gₙ ≃ G^/(Gₙ)^`. Note that the map `f : G/Gₙ → G^/(Gₙ)^` is computable (and given by)
  the apply below, while the map in the other direction is non-computable, as we only use the fact that
  `f` is bijective. TODO: perhaps we should make the other direction computable.
-/
noncomputable def am10_4 (n : ℕ) :
  G ⧸ (F.N n) ≃+
    (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) :=
  AddEquiv.ofBijective (am10_4_map F n) (am10_4_aux₂_bijective F n)

lemma am10_4_apply (n : ℕ) (x : G) :
  am10_4 F n ⟦x⟧ = ⟦OurFiltrationCompletion.of F x⟧ := rfl

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
