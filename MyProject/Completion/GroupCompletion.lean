import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G]
variable {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G]
variable (H : σ) (F : OurFiltration G σ)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (@OurFiltrationCompletionHom.of_comap_le H G _ _ (AddSubgroup H) σ _ _ _ _
      (PullbackOurFiltration (AddSubgroupClass.subtype H) F) F
      (AddSubgroupClass.subtype H) (fun n ↦ by rfl)).range


lemma AddSubgroupCompletion_of_le {H H': σ} (h : H ≤ H') :
    AddSubgroupCompletion H F ≤ AddSubgroupCompletion H' F := by
  let Hc := OurFiltrationCompletion (PullbackOurFiltration (AddSubgroupClass.subtype H) F)
  let H'c := OurFiltrationCompletion (PullbackOurFiltration (AddSubgroupClass.subtype H') F)
  let Gc := OurFiltrationCompletion F

  let f₁ : H →+ H' := AddSubgroupClass.inclusion h
  let f₂ : H' →+ G := (AddSubgroupClass.subtype H')

  let c₁ : H →+ Hc := OurFiltrationCompletion.of (PullbackOurFiltration (AddSubgroupClass.subtype H) F)
  let c₂ : H' →+ H'c := OurFiltrationCompletion.of (PullbackOurFiltration (AddSubgroupClass.subtype H') F)
  let c₃ : G →+ Gc := OurFiltrationCompletion.of F

  let g₁ : Hc →+ H'c := OurFiltrationCompletionHom.of_comap_le f₁ (fun n ↦ by rfl)
  let g₂ : H'c →+ Gc := OurFiltrationCompletionHom.of_comap_le f₂ (fun n ↦ by rfl)
  let g₃ : Hc →+ Gc := OurFiltrationCompletionHom.of_comap_le (AddSubgroupClass.subtype H) (fun n ↦ by rfl)

  have : g₃ = g₂.comp g₁ := by
    ext x n
    unfold g₃
    unfold OurFiltrationCompletionHom.of_comap_le
    sorry

  show g₃.range ≤ g₂.range
  rw [this]
  exact Set.range_comp_subset_range g₁ g₂
end

section

variable {G : Type*} [AddCommGroup G] (F : OurFiltration G (AddSubgroup G))
variable {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] (F : OurFiltration G σ)

def CompletedFiltration : OurFiltration (OurFiltrationCompletion F) (AddSubgroup (OurFiltrationCompletion F)) where
  N := fun n ↦ AddSubgroupCompletion (F.N n) F
  mono := fun n ↦ AddSubgroupCompletion_of_le F (F.mono n)

end
