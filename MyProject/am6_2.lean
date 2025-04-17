import Mathlib.RingTheory.Noetherian.Defs

/-
  # Proposition 6.2
  Let `A` be a ring and `M` and `A`-module.
  Then `M` is a Noetherian `A`-module if and only if every submodule of `M` is finitely generated.
-/
variable {A : Type u} [CommRing A]
variable (M : Type u) [AddCommGroup M] [Module A M]

lemma am6_2 : IsNoetherian A M ↔ ∀ s : Submodule A M, s.FG :=
  isNoetherian_def
