import MyProject.AssociatedGradedRing.Map

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type u} [AddCommGroup M] [Module A M]

/--
  Given an `A`-module `M`, a submodule `M' ⊆ M` and an `I`-filtration `F` on `M`, we can define
  a filtration `F'` on `M'` by `F'.N n = M' ∩ F.N m`.
-/
def SubmoduleFiltration (F : I.Filtration M) (M' : Submodule A M) :
    I.Filtration M' where
  N := fun m ↦ Submodule.comap M'.subtype (F.N m)
  mono := fun m n h ↦ F.mono m h
  smul_le := fun n ↦ by
    apply Submodule.smul_le.mpr
    intro a ha x hx
    apply F.smul_le n
    exact Submodule.smul_mem_smul ha hx

lemma SubmoduleFiltration_le_comap (F : I.Filtration M) (M' : Submodule A M) :
  ∀ n, (SubmoduleFiltration F M').N n ≤ (F.N n).comap (M'.subtype) := fun _ _ a ↦ a

/--
  For every `n`, we have a natural `A`-homomorphism from `(SubmoduleFiltration F M').N n` to
  `F.N n`.
-/
def SubmoduleFiltrationHom (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) :
    (SubmoduleFiltration F M').N n →ₗ[A] F.N n :=
  FiltrationHom (SubmoduleFiltration_le_comap F M' n)

def SubmoduleFiltrationHom_mem_succ_n (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) (x : (SubmoduleFiltration F M').N n) :
    ↑x ∈ (SubmoduleFiltration F M').N (n + 1) ↔ ↑(SubmoduleFiltrationHom F M' n x) ∈ F.N (n + 1) := by
  rfl

/--
  For every `n`, the natural `A`-homomorphism from `(SubmoduleFiltration F M').N n` to
  `F.N n` induces an `A`-homomorphism map from `GradedPiece (SubmoduleFiltration F M') n`
  to `GradedPiece F n`.
-/
def SubmoduleGradedPieceHom (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) :
    GradedPiece (SubmoduleFiltration F M') n →ₗ[A] GradedPiece F n :=
  GradedPieceHom (SubmoduleFiltration_le_comap F M') n

lemma SubmoduleGradedPieceHom_apply (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) (x : (SubmoduleFiltration F M').N n) :
    SubmoduleGradedPieceHom F M' n ⟦x⟧ = ⟦SubmoduleFiltrationHom F M' n x⟧ := rfl

lemma SubmoduleGradedPieceHom_injective (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) :
    Function.Injective (SubmoduleGradedPieceHom F M' n) := by
  apply LinearMap.ker_eq_bot.mp
  refine LinearMap.ker_eq_bot'.mpr ?_
  intro x h
  rw [←Quotient.out_eq x] at *
  rw [←GradedPiece_mk_zero_iff]
  rw [SubmoduleFiltrationHom_mem_succ_n]
  rw [GradedPiece_mk_zero_iff]
  exact h

/--
  Given an `A`-module `M`, a submodule `M'` and an `I`-filtration `F`, there is a natural
  homomorphism from `G(M')` to `G(M)`, where `G(M')` is given using the filtration induced by `F`.
-/
def SubmoduleGradedModuleHom (F : I.Filtration M) (M' : Submodule A M) :
    AssociatedGradedModule (SubmoduleFiltration F M') →ₗ[AssociatedGradedRing I] AssociatedGradedModule F :=
  GradedModuleHom (SubmoduleFiltration_le_comap F M')

lemma SubmoduleGradedModuleHom_apply (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) (x : AssociatedGradedModule (SubmoduleFiltration F M')) :
    (SubmoduleGradedModuleHom F M' x) n = (SubmoduleGradedPieceHom F M' n (x n)) := rfl

lemma SubmoduleGradedModuleMap_injective (F : I.Filtration M) (M' : Submodule A M) :
    Function.Injective (SubmoduleGradedModuleHom F M') := by
  refine LinearMap.ker_eq_bot.mp ?_
  refine LinearMap.ker_eq_bot'.mpr ?_
  intro x h
  apply DirectSum.ext
  intro n
  apply SubmoduleGradedPieceHom_injective
  rw [DirectSum.ext_iff] at h
  rw [←SubmoduleGradedModuleHom_apply]
  exact h n
