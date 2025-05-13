import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (F : OurFiltration G)

def AddSubgroupCompletion :
  AddSubgroup (OurFiltrationCompletion F) :=
    (@OurFiltrationCompletionHom.of_comap_le H G _ _ (PullbackOurFiltration H.subtype F) F (H.subtype) (fun n ↦ by rfl)).range

end
