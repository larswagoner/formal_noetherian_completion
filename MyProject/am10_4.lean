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

lemma am10_4_aux (n : ℕ) (x : OurFiltrationCompletion F) :
  QuotientAddGroup.map (F.N n) (AddSubgroupCompletion (F.N n) F)
        (OurFiltrationCompletion.of F) (AddSubgroupCompletion_le_comap (F.N n) F) (x.1 n) =
    ⟦x⟧ := by
  rw [show x.1 n = ⟦ (x.1 n).out ⟧ by rw [Quotient.out_eq]]
  show ⟦ _ ⟧ = _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rw [←AddSubgroupCompletion_ker_def_eq_range_def]
  rw [AddSubgroupCompletion_ker_def_eq_filtration_ker_def]
  unfold AddSubgroupCompletion_filtration_ker_def AddSubgroupCompletion_filtration_ker_def_map
  show _ - x.1 n = 0
  suffices : ((OurFiltrationCompletion.of F) (x.1 n).out).1 n = x.1 n
  exact sub_eq_zero_of_eq this
  rw [OurFiltrationCompletion.of_apply]
  exact Quotient.out_eq (x.1 n)


/--
  The isomorphism `G/Gₙ ≃ G^/(Gₙ)^`.
-/
def am10_4 (n : ℕ) :
    G ⧸ (F.N n) ≃+
      (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) where
  __ := QuotientAddGroup.map (F.N n) (AddSubgroupCompletion (F.N n) F)
        (OurFiltrationCompletion.of F) (AddSubgroupCompletion_le_comap (F.N n) F)
  invFun := QuotientAddGroup.lift (AddSubgroupCompletion (F.N n) F)
    (AddSubgroupCompletion_filtration_ker_def_map F n) (by
      show _ ≤ AddSubgroupCompletion_filtration_ker_def F n
      rw [←AddSubgroupCompletion_ker_def_eq_filtration_ker_def]
      rw [AddSubgroupCompletion_ker_def_eq_range_def]
    )
  left_inv := by
    rintro ⟨x⟩
    rfl
  right_inv := by
    rintro ⟨x⟩
    simp [AddSubgroupCompletion_filtration_ker_def_map]
    show _ = ⟦ _ ⟧
    exact am10_4_aux F n x

lemma am10_4_apply (n : ℕ) (x : G) :
  am10_4 F n ⟦x⟧ = ⟦OurFiltrationCompletion.of F x⟧ := rfl

lemma am10_4_of_n_eq_self (n : ℕ) (x : OurFiltrationCompletion F) :
  am10_4 F n (x.1 n) = ⟦x⟧ := am10_4_aux F n x

lemma am10_4_inv_apply (n : ℕ) (x : OurFiltrationCompletion F) :
  (am10_4 F n).symm ⟦x⟧ = x.1 n := rfl
