import MyProject.am10_4
import MyProject.Completion.IsFiltrationComplete
import MyProject.adic_completion

/-
  # Proposition 10.5
  Let `G` be a topological abelian group.
  Then `Ĝ̂ ≅ Ĝ`.
-/

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M] (F : I.Filtration M)

lemma am10_5 : Function.Bijective
  (FiltrationCompletion.of
    (PushforwardFiltration (FiltrationCompletion.of F) F)) := sorry

lemma am10_5' : IsFiltrationComplete (PushforwardFiltration (FiltrationCompletion.of F) F) := by
  rw [IsFiltrationComplete_iff_Bijective]
  exact am10_5 F

end

section

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M]

instance : IsAdicComplete (I.adicCompletion I) (AdicCompletion I M) := by
  rw [isComplete_iff_isCanonicalComplete]
  sorry



end
