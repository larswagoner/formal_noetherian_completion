import MyProject.am6_2
import MyProject.am10_24
import MyProject.AssociatedGradedRing.Submodule

/-
  # Corollary 10.25
  Let `A` be a ring, `I` an ideal of `A`, `M` an `A`-module, `(Mₙ)` an
  `I`-filtration of `M`. Suppose `A` is complete in the `I`-topology
  and that `M` is Hausdorff in its filtration topology (i.e. `⋂ₙ Mₙ = 0`).
  Suppose also that `G(M)` is a Noetherian `G(A)`-module.
  Then `M` is Noetherian `A`-module.
-/

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M]

def SubmoduleFiltrationHausdorff_of {F : I.Filtration M} (M' : Submodule A M) (h : ⨅ n, F.N n = (⊥ : Submodule A M)) :
    ⨅ n, (SubmoduleFiltration F M').N n = ⊥ := by
  show ⨅ n, Submodule.comap M'.subtype (F.N n) = ⊥
  rw [←Submodule.comap_iInf]
  rw [h]
  simp

lemma am10_25 [IsAdicComplete I A] (F : I.Filtration M)
  (Ftop : F.N 0 = ⊤)
  (hF : ⨅ n, F.N n = (⊥ : Submodule A M))
  (hiN : IsNoetherian (AssociatedGradedRing I) (AssociatedGradedModule F)) :
    IsNoetherian A M where
  noetherian := by
    intro M'
    apply Module.Finite.iff_fg.mp
    have : Module.Finite (AssociatedGradedRing I) (AssociatedGradedModule (SubmoduleFiltration F M')) :=
      Module.Finite.of_injective (SubmoduleGradedModuleHom F M') (SubmoduleGradedModuleMap_injective F M')
    have : IsFiltrationHausdorff (SubmoduleFiltration F M') := by
      rw [isFiltrationHausdorff_iff]
      intro x h
      show x ∈ (⊥ : Submodule A M')
      rw [←SubmoduleFiltrationHausdorff_of M' hF]
      rw [Submodule.mem_iInf]
      intro n
      rw [←SModEq.zero]
      exact h n
    have : (SubmoduleFiltration F M').N 0 = ⊤ := by
      unfold SubmoduleFiltration
      simp [Ftop]
    apply am10_24 (SubmoduleFiltration F M') this
