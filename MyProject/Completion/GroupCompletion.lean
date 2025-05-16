import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (F : OurFiltration G)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (@OurFiltrationCompletionHom.of_comap_le H G _ _
      (PullbackOurFiltration H.subtype F) F H.subtype (fun n ↦ by rfl)).range

lemma AddSubgroupCompletion_of_le {H H': AddSubgroup G} (h : H ≤ H') :
    AddSubgroupCompletion H F ≤ AddSubgroupCompletion H' F := by
  let Hc := OurFiltrationCompletion (PullbackOurFiltration H.subtype F)
  let H'c := OurFiltrationCompletion (PullbackOurFiltration H'.subtype F)
  let Gc := OurFiltrationCompletion F

  let g₁ : Hc →+ H'c := OurFiltrationCompletionHom.of_comap_le (AddSubgroup.inclusion h) (fun n ↦ by rfl)
  let g₂ : H'c →+ Gc := OurFiltrationCompletionHom.of_comap_le H'.subtype (fun n ↦ by rfl)
  let g₃ : Hc →+ Gc := OurFiltrationCompletionHom.of_comap_le H.subtype (fun n ↦ by rfl)

  have : g₃ = g₂.comp g₁ := by
    ext x n
    unfold g₃
    unfold OurFiltrationCompletionHom.of_comap_le
    sorry

  show g₃.range ≤ g₂.range
  rw [this]
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
