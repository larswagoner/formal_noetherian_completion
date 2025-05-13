import MyProject.am10_4
import MyProject.Completion.IsOurFiltrationComplete
import MyProject.adic_completion

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

section

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M]

instance : IsAdicComplete (I.adicCompletion I) (AdicCompletion I M) := by
  rw [isComplete_iff_isCanonicalOurComplete]
  have := am10_5' (I.stableFiltration (⊤ : Submodule A M)).toOurFiltration
  convert this
  sorry

end
