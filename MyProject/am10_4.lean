import MyProject.am10_3
import MyProject.Completion.GroupCompletion

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/


section

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

def am10_4 (n : ℕ) :
  (OurFiltrationCompletion F) ⧸ (AddSubgroupCompletion (F.N n) F) ≃+ G ⧸ F.N n := sorry

end
