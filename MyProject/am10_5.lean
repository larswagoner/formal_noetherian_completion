import MyProject.am10_4
import MyProject.Completion.IsOurFiltrationComplete
import MyProject.Completion.IdealCompletion

/-
  # Proposition 10.5
  Let `G` be a topological abelian group.
  Then `Ĝ̂ ≅ Ĝ`.
-/

section

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

lemma am10_5 : Function.Bijective
  (OurFiltrationCompletion.of (CompletedFiltration F)) := sorry

lemma am10_5' : IsOurFiltrationComplete (CompletedFiltration F) := by
  rw [IsOurFiltrationComplete_iff_Bijective]
  exact am10_5 F

end
