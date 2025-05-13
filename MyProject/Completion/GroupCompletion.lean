import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (F : OurFiltration G)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (@OurFiltrationCompletionHom.of_comap_le H G _ _ (PullbackOurFiltration H.subtype F) F (H.subtype) (fun n ↦ by rfl)).range


lemma AddSubgroupCompletion_of_le {H H': AddSubgroup G} (h : H ≤ H') :
    AddSubgroupCompletion H F ≤ AddSubgroupCompletion H' F := by
  sorry

end

section

variable {G : Type*} [AddCommGroup G] (F : OurFiltration G)

def CompletedFiltration : OurFiltration (OurFiltrationCompletion F) where
  N := fun n ↦ AddSubgroupCompletion (F.N n) F
  mono := fun n ↦ AddSubgroupCompletion_of_le F (F.mono n)

end
