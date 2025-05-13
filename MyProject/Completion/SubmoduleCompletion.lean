import MyProject.Completion.FiltrationCompletion

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M]
variable (N : Submodule A M) (F : I.Filtration M)

def Submodule.FiltrationCompletion :
  Submodule (FiltrationCompletion F) := sorry


end
