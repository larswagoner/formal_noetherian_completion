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

def am10_5 :
  (OurFiltrationCompletion F) ≃+
    (OurFiltrationCompletion (CompletedFiltration F)) :=
  InducedNaiveInverseLimitIso_of_AddInverseSystemIso <| AddInverseSystemIso_of_iso _ _ (fun n ↦ am10_4 F n)
    (by rintro n m hnm ⟨x⟩; rfl)

lemma am10_5_apply (x : OurFiltrationCompletion F) (n : ℕ) :
    (am10_5 F x).1 n = ⟦x⟧ :=
  am10_4_of_n_eq_self F n x

lemma am10_5₁ : Function.Bijective
  (OurFiltrationCompletion.of (CompletedFiltration F)) := by
  convert (am10_5 F).bijective
  ext x i
  rw [am10_5_apply]
  rfl

lemma am10_5₂ : IsOurFiltrationComplete (CompletedFiltration F) := by
  rw [IsOurFiltrationComplete_iff_Bijective]
  exact am10_5₁ F

end
