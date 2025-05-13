import MyProject.am10_3

/-
  # Proposition 10.4
  Let `G` be a abelian group with a topology defined by a sequence `{Gₙ}`.
  Then `Ĝ/Ĝₙ ≅ G/Gₙ`.
-/


section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M] (F : I.Filtration M)

variable (n : ℕ)

def am10_4 (n : ℕ) :
  (FiltrationCompletion F) ⧸ ((PushforwardFiltration (FiltrationCompletion.of F) F).N n) ≃+ M ⧸ F.N n := sorry

end
