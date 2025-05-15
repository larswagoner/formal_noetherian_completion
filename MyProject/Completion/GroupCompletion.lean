import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
variable {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] (F : OurFiltration G σ)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (@OurFiltrationCompletionHom.of_comap_le H G _ _ (AddSubgroup H) σ _ _ _ _ (PullbackOurFiltration H.subtype F) F (H.subtype) (fun n ↦ by rfl)).range


lemma AddSubgroupCompletion_of_le {H H': AddSubgroup G} (h : H ≤ H') :
    AddSubgroupCompletion H F ≤ AddSubgroupCompletion H' F := by
  let Hc := OurFiltrationCompletion (PullbackOurFiltration H.subtype F)
  let H'c := OurFiltrationCompletion (PullbackOurFiltration H'.subtype F)
  let Gc := OurFiltrationCompletion F

  let f₁ : H →+ H' := AddSubgroup.inclusion h
  let f₂ : H' →+ G := H'.subtype

  let c₁ : H →+ Hc := OurFiltrationCompletion.of (PullbackOurFiltration H.subtype F)
  let c₂ : H' →+ H'c := OurFiltrationCompletion.of (PullbackOurFiltration H'.subtype F)
  let c₃ : G →+ Gc := OurFiltrationCompletion.of F

  let g₁ : Hc →+ H'c := OurFiltrationCompletionHom.of_comap_le f₁ (fun n ↦ by rfl)
  let g₂ : H'c →+ Gc := OurFiltrationCompletionHom.of_comap_le f₂ (fun n ↦ by rfl)
  let g₃ : Hc →+ Gc := OurFiltrationCompletionHom.of_comap_le H.subtype (fun n ↦ by rfl)

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
  N := fun n ↦ AddSubgroupCompletion (AddSubgroup.ofClass (F.N n)) F
  mono := fun n ↦ AddSubgroupCompletion_of_le F (F.mono n)

end
