import MyProject.Completion.OurFiltrationCompletion
import MyProject.Completion.BoundedDifference
import MyProject.Filtration.FConstructions
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-
  In this file, we define and prove:
  · Given a subgroup `H ⊆ G` and a filtration `F` on `G`, we define the completion of `H` as a
      subgroup of `OurFiltrationCompletion F`, which we denote by `AddSubgroupCompletion H F`.
  · Given an inclusion `H ⊆ H' ⊆ G`, there is an inclusion `AddSubgroupCompletion H F ⊆ AddSubgroupCompletion H' F`.
  · Given a group `G` and a filtration `F`, we define a filtration on the completion of `G` by
      taking `AddSubgroupCompletion (F.N n) F` to be the `n`-th subgroup.
  · Given two ideals `I, J ⊆ A`, the completed subgroup of `J` in `AdicCompletion I A` is equal to
      the image of the map `AdicCompletion I J → AdicCompletion I A`.
-/


section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (F : OurFiltration G)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (OurFiltrationCompletionHom.of_comap_le (PullbackOurFiltration H.subtype F) F H.subtype (fun n ↦ by rfl)).range

lemma AddSubgroupCompletion_of_le {H H': AddSubgroup G} (h : H ≤ H') :
    AddSubgroupCompletion H F ≤ AddSubgroupCompletion H' F := by
  let HF := PullbackOurFiltration H.subtype F
  let H'F := PullbackOurFiltration H'.subtype F

  let g₁ := OurFiltrationCompletionHom.of_comap_le HF H'F (AddSubgroup.inclusion h) (fun n ↦ by rfl)
  let g₂ := OurFiltrationCompletionHom.of_comap_le H'F F H'.subtype (fun n ↦ by rfl)
  let g₃ := OurFiltrationCompletionHom.of_comap_le HF F H.subtype (fun n ↦ by rfl)

  have h₁ : g₃ = g₂.comp g₁ := OurFiltrationCompletionHom.of_comap_le_comp_eq
    (PullbackOurFiltration H.subtype F) (PullbackOurFiltration H'.subtype F) F (AddSubgroup.inclusion h) H'.subtype (fun n ↦ by rfl) (fun n ↦ by rfl)

  show g₃.range ≤ g₂.range
  rw [h₁]
  exact Set.range_comp_subset_range g₁ g₂

lemma AddSubgroupCompletion_le_comap :
    H ≤ (AddSubgroupCompletion H F).comap (OurFiltrationCompletion.of F) := by
  intro g hg
  use (OurFiltrationCompletion.of (PullbackOurFiltration H.subtype F) ⟨g, hg⟩)
  rfl

end

section

variable {G : Type*} [AddCommGroup G] (F : OurFiltration G)
variable (F : OurFiltration G)

def CompletedFiltration : OurFiltration (OurFiltrationCompletion F) where
  N := fun n ↦ AddSubgroupCompletion (F.N n) F
  mono := fun n ↦ AddSubgroupCompletion_of_le F (F.mono n)

end

section

variable {A : Type*} [CommRing A] (I J : Ideal A)

/-
  Given an ideal `J`, the two filtrations on `J` given by
  (1) Iⁿ • J                (2) Iⁿ ∩ J
  have a bounded difference. This uses the Artin-Rees lemma.
-/
lemma CanonicalFiltration_ideal_subtype_bounded₁ (n : ℕ) : (I.stableFiltration (⊤ : Submodule A J)).toOurFiltration.N n ≤
      (PullbackOurFiltration J.toAddSubgroup.subtype (CanonicalOurFiltration I)).N n := by
  simp [PullbackOurFiltration, CanonicalOurFiltration, CanonicalFiltration, Ideal.Filtration.toOurFiltration]
  intro ⟨x, hxJ⟩ hx
  rw [AddSubgroup.mem_addSubgroupOf]
  simp at *
  rw [Submodule.mem_smul_top_iff] at hx
  exact Ideal.mul_le_right hx

variable [IsNoetherianRing A]

lemma CanonicalFiltration_ideal_subtype_bounded₂ : ∃ m : ℕ, ∀ n : ℕ,
    (PullbackOurFiltration J.toAddSubgroup.subtype (CanonicalOurFiltration I)).N (n + m) ≤
      (I.stableFiltration (⊤ : Submodule A J)).toOurFiltration.N n := by
  simp [PullbackOurFiltration, CanonicalOurFiltration, CanonicalFiltration, Ideal.Filtration.toOurFiltration]
  rcases Ideal.exists_pow_inf_eq_pow_smul I J with ⟨m, hm⟩
  use m
  intro n ⟨x, hxJ⟩ hx
  rw [AddSubgroup.mem_addSubgroupOf] at hx
  simp at hx
  simp
  rw [Submodule.mem_smul_top_iff]
  simp
  have := hm (n + m) (by linarith)
  simp at this
  suffices : x ∈ (I^n * I^m) ⊓ (I^n * J)
  · exact this.2
  apply le_inf (Ideal.mul_mono_right inf_le_left) (Ideal.mul_mono_right inf_le_right)
  rw [←this]
  refine Submodule.mem_inf.mpr ?_
  exact ⟨hx, hxJ⟩

noncomputable def AdicCompletion_OurFiltrationPullback_iso :
    AdicCompletion I J ≃+ OurFiltrationCompletion (PullbackOurFiltration J.toAddSubgroup.subtype (CanonicalOurFiltration I)) := by
  have : _ ≃+ OurFiltrationCompletion (PullbackOurFiltration J.toAddSubgroup.subtype (CanonicalOurFiltration I)) :=
    OurFiltrationCompletionIso_of_bounded_difference 0 (CanonicalFiltration_ideal_subtype_bounded₂ I J).choose
      (CanonicalFiltration_ideal_subtype_bounded₁ I J) (CanonicalFiltration_ideal_subtype_bounded₂ I J).choose_spec
  exact this

lemma AdicCompletion_OurFiltrationPullback_iso_apply (x : AdicCompletion I J) (n : ℕ) :
    (AdicCompletion_OurFiltrationPullback_iso I J x).1 n =
      QuotientAddGroup.map _ _ (AddMonoidHom.id J) (CanonicalFiltration_ideal_subtype_bounded₁ I J n) (x.1 n) := rfl

lemma AddSubgroupCompletionOfCanonical_eq_map_range :
  AddSubgroupCompletion J.toAddSubgroup (CanonicalOurFiltration I) =
    (AdicCompletion.map I (J.subtype)).toAddMonoidHom.range := by
  let J₁ := AdicCompletion I J
  let J₂ := OurFiltrationCompletion (PullbackOurFiltration J.toAddSubgroup.subtype (CanonicalOurFiltration I))
  let Ac := AdicCompletion I A

  let f₁ : J₁ →+ Ac := AdicCompletion.map I J.subtype
  let f₂ : J₁ ≃+ J₂ := AdicCompletion_OurFiltrationPullback_iso I J
  let f₃ : J₂ →+ Ac :=
    OurFiltrationCompletionHom.of_comap_le _ (CanonicalOurFiltration I) J.toAddSubgroup.subtype (fun n ↦ by rfl)

  have : f₁ = f₃.comp f₂ := by
    ext x n
    show (f₁ x).1 n = QuotientAddGroup.map _ _ (J.toAddSubgroup.subtype) (by rfl) (((AdicCompletion_OurFiltrationPullback_iso I J) x).1 n)
    rw [AdicCompletion_OurFiltrationPullback_iso_apply]
    unfold f₁
    simp
    rw [AdicCompletion.map_val_apply]
    rcases x.1 n with ⟨y, hy⟩
    rfl

  show f₃.range = f₁.range
  rw [this]
  rw [AddMonoidHom.range_comp]
  rw [AddMonoidHom.range_eq_map f₃]
  congr
  exact (AddMonoidHom.range_eq_top.mpr f₂.surjective).symm

end
