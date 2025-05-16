import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

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
