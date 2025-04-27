import MyProject.AssociatedGradedRing.Module

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

/--
  For every `n`, we have a natural `A`-homomorphism from `(SubmoduleFiltration F M').N n` to
  `F.N n`.
-/
def SubmoduleFiltrationHom (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) :
    (SubmoduleFiltration F M').N n →ₗ[A] F.N n where
  toFun := fun ⟨n, n_mem⟩ ↦ ⟨↑n, n_mem⟩
  map_add' := by
    intro x y
    simp
    rfl
  map_smul' := by
    intro x y
    simp
    rfl

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
  Submodule.mapQ _ _ (SubmoduleFiltrationHom F M' n) (fun _ h ↦ h)

def SubmoduleGradedPieceHom_additive (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) :
    GradedPiece (SubmoduleFiltration F M') n →+ GradedPiece F n :=
  ↑(SubmoduleGradedPieceHom F M' n)

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

lemma SubmoduleGradedPieceHom_smul (F : I.Filtration M) (M' : Submodule A M) {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece (SubmoduleFiltration F M') n) :
  SubmoduleGradedPieceHom F M' (m + n) (graded_smul (SubmoduleFiltration F M') s x) =
    graded_smul F s (SubmoduleGradedPieceHom F M' n x) := by
  rw [←GradedPiece_mk_out x]
  rw [←GradedPiece_mk_out s]
  rw [graded_smul_of_mk]
  rw [SubmoduleGradedPieceHom_apply]
  rw [SubmoduleGradedPieceHom_apply]
  rw [graded_smul_of_mk]
  rfl

/--
  Given an `A`-module `M`, a submodule `M'` and an `I`-filtration `F`, there is a natural
  homomorphism from `G(M')` to `G(M)`, where `G(M')` is given using the filtration induced by `F`.
-/
def SubmoduleGradedModuleMap (F : I.Filtration M) (M' : Submodule A M) :
    AssociatedGradedModule (SubmoduleFiltration F M') →+ AssociatedGradedModule F :=
  DirectSum.map (SubmoduleGradedPieceHom_additive F M')

lemma SubmoduleGradedModuleMap_apply (F : I.Filtration M) (M' : Submodule A M) (n : ℕ) (x : AssociatedGradedModule (SubmoduleFiltration F M')) :
    (SubmoduleGradedModuleMap F M' x) n = (SubmoduleGradedPieceHom F M' n (x n)) := rfl

lemma SubmoduleGradedModuleMap_of (F : I.Filtration M) (M' : Submodule A M) {m : ℕ} (x : GradedPiece (SubmoduleFiltration F M') m) :
    SubmoduleGradedModuleMap F M' (AssociatedGradedModule.of x) =
      AssociatedGradedModule.of (SubmoduleGradedPieceHom F M' m x):= by
  apply DirectSum.ext
  intro n
  rw [SubmoduleGradedModuleMap_apply]
  unfold AssociatedGradedModule.of
  by_cases h : m = n
  · rw [←h]
    rw [DirectSum.of_eq_same]
    rw [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    rw [DirectSum.of_eq_of_ne _ _ _ h]
    rfl

lemma SubmoduleGradedModuleMap_of_smul_of (F : I.Filtration M) (M' : Submodule A M) {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece (SubmoduleFiltration F M') n) :
    SubmoduleGradedModuleMap F M' (
      (AssociatedGradedRing.of s)
        • (AssociatedGradedModule.of x)) =
      (AssociatedGradedRing.of s)
      • (SubmoduleGradedModuleMap F M' (AssociatedGradedModule.of x)) := by
  rw [AssociatedGradedModule.of_smul_of]
  rw [SubmoduleGradedModuleMap_of]
  rw [SubmoduleGradedModuleMap_of]
  rw [AssociatedGradedModule.of_smul_of]
  rw [SubmoduleGradedPieceHom_smul F M' s x]

def SubmoduleGradedRingHom (F : I.Filtration M) (M' : Submodule A M) :
    AssociatedGradedModule (SubmoduleFiltration F M') →ₗ[AssociatedGradedRing I] AssociatedGradedModule F where
  toFun := SubmoduleGradedModuleMap F M'
  map_add' := (SubmoduleGradedModuleMap F M').map_add
  map_smul' := by
    intros s x
    apply @DirectSum.induction_on ℕ (GradedPiece (SubmoduleFiltration F M')) _ _ (fun x ↦       (SubmoduleGradedModuleMap F M') (s • ↑x) = s • (SubmoduleGradedModuleMap F M') x) x
    · simp
    · intro n x
      apply @DirectSum.induction_on ℕ (GradedRingPiece I) _ _ _ s
      · simp
      · intro m s
        exact SubmoduleGradedModuleMap_of_smul_of F M' s x
      · intro s t h₁ h₂
        rw [add_smul]
        rw [add_smul]
        rw [←h₁, ←h₂]
        rw [AddMonoidHom.map_add]
    · intro x y h₁ h₂
      simp
      rw [h₁, h₂]

lemma SubmoduleGradedModuleMap_injective (F : I.Filtration M) (M' : Submodule A M) :
    Function.Injective (SubmoduleGradedModuleMap F M') := by
  refine (AddMonoidHom.ker_eq_bot_iff (SubmoduleGradedModuleMap F M')).mp ?_
  refine (AddSubgroup.eq_bot_iff_forall (SubmoduleGradedModuleMap F M').ker).mpr ?_
  intro x h
  apply DirectSum.ext
  intro n
  apply SubmoduleGradedPieceHom_injective
  simp at h
  rw [DirectSum.ext_iff] at h
  rw [←SubmoduleGradedModuleMap_apply]
  exact h n
