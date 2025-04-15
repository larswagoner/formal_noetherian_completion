import MyProject.am6_2
import MyProject.am10_24

/-
  # Corollary 10.25
  Let `A` be a ring, `I` an ideal of `A`, `M` an `A`-module, `(Mₙ)` an
  `I`-filtration of `M`. Suppose `A` is complete in the `I`-topology
  and that `M` is Hausdorff in its filtration topology (i.e. `⋂ₙ Mₙ = 0`).
  Suppose also that `G(M)` is a Noetherian `G(A)`-module.
  Then `M` is Noetherian `A`-module.
-/



lemma am10_25 {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
  {M : Type u} [AddCommGroup M] [Module A M] (F : I.Filtration M)
  (h :  ⨅ n, F.N n = (⊥ : Submodule A M))  -- Best way to add `⋂ₙ Mₙ = 0`?
  (hiN : IsNoetherian (AssociatedGradedRing I) (AssociatedGradedModule F)) :
    IsNoetherian A M := sorry
