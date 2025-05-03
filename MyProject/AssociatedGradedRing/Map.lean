import MyProject.AssociatedGradedRing.Module

/-
  Given two `A`-modules `M₁, M₂` with `I`-filtrations `F₁` on `M₁` and `F₂` on `M₂`,
  and a map  `φ : M₁ →ₗ[A] N₂` such that `φ(F₁.N n) ⊆ F₂.N n` for all `n : ℕ`,
  there is an induced map `G(φ) : G(M₁) →ₗ[G(A)] G(M₂)`.
-/

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module A M₁]
variable [AddCommGroup M₂] [Module A M₂]
variable {φ : M₁ →ₗ[A] M₂}
variable {F₁ : I.Filtration M₁} {F₂ : I.Filtration M₂}

/--
  For every `n`, we have a natural `A`-homomorphism from `F₁.N n` to `F₂.N n`.
-/
def FiltrationHom {n : ℕ} (hφ_n : F₁.N n ≤ (F₂.N n).comap φ) :
    F₁.N n →ₗ[A] F₂.N n :=
  φ.restrict hφ_n

@[simp]
lemma FiltrationHom_apply {n : ℕ} (hφ_n : F₁.N n ≤ (F₂.N n).comap φ) {x : F₁.N n} :
    FiltrationHom hφ_n x = φ x := rfl

def FiltrationHom_smul (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) {m n : ℕ} (s : (CanonicalFiltration I).N m)
  (x : F₁.N n) :
  FiltrationHom (hφ (m + n)) (filtration_smul s x) =
   filtration_smul s (FiltrationHom (hφ n) x) := by
  unfold filtration_smul
  refine Subtype.coe_eq_of_eq_mk ?_
  simp


/--
  For every `n`, the natural `A`-homomorphism from `(SubmoduleFiltration F M').N n` to
  `F.N n` induces an `A`-homomorphism map from `GradedPiece (SubmoduleFiltration F M') n`
  to `GradedPiece F n`.
-/
def GradedPieceHom (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) (n : ℕ) :
    GradedPiece F₁ n →ₗ[A] GradedPiece F₂ n :=
  Submodule.mapQ _ _ (FiltrationHom (hφ n)) (fun _ x ↦ hφ (n + 1) x)

def GradedPieceHom_additive (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) (n : ℕ) :
    GradedPiece F₁ n →+ GradedPiece F₂ n :=
  ↑(GradedPieceHom hφ n)

lemma GradedPieceHom_apply (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) (n : ℕ) (x : F₁.N n) :
    GradedPieceHom hφ n ⟦x⟧ = ⟦FiltrationHom (hφ n) x⟧ := rfl

lemma GradedPieceHom_smul (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece F₁ n) :
    GradedPieceHom hφ (m + n) (graded_smul s x) = graded_smul s (GradedPieceHom hφ n x) := by
  rw [←GradedPiece_mk_out x]
  rw [←GradedPiece_mk_out s]
  rw [graded_smul_of_mk]
  rw [GradedPieceHom_apply]
  rw [GradedPieceHom_apply]
  rw [graded_smul_of_mk]
  rw [FiltrationHom_smul]

/--
  Given an `A`-module `M`, a  `M'` and an `I`-filtration `F`, there is a natural
  homomorphism from `G(M')` to `G(M)`, where `G(M')` is given using the filtration induced by `F`.
-/
def GradedModuleMap (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) :
    AssociatedGradedModule F₁ →+ AssociatedGradedModule F₂ :=
  DirectSum.map (GradedPieceHom_additive hφ)

lemma GradedModuleMap_apply (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ)  (n : ℕ) (x : AssociatedGradedModule F₁) :
    (GradedModuleMap hφ x) n = (GradedPieceHom hφ n (x n)) := rfl

lemma GradedModuleMap_of (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) {m : ℕ} (x : GradedPiece F₁ m) :
    GradedModuleMap hφ (AssociatedGradedModule.of x) =
      AssociatedGradedModule.of (GradedPieceHom hφ m x):= by
  apply DirectSum.ext
  intro n
  rw [GradedModuleMap_apply]
  unfold AssociatedGradedModule.of
  by_cases h : m = n
  · rw [←h]
    rw [DirectSum.of_eq_same]
    rw [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    rw [DirectSum.of_eq_of_ne _ _ _ h]
    simp

lemma GradedModuleMap_of_smul_of (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) {m n : ℕ} (s : GradedRingPiece I m) (x : GradedPiece F₁ n) :
    GradedModuleMap hφ (
      (AssociatedGradedRing.of s)
        • (AssociatedGradedModule.of x)) =
      (AssociatedGradedRing.of s)
      • (GradedModuleMap hφ (AssociatedGradedModule.of x)) := by
  rw [AssociatedGradedModule.of_smul_of]
  rw [GradedModuleMap_of]
  rw [GradedModuleMap_of]
  rw [AssociatedGradedModule.of_smul_of]
  rw [GradedPieceHom_smul hφ s x]

def GradedModuleHom (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) :
    AssociatedGradedModule F₁ →ₗ[AssociatedGradedRing I] AssociatedGradedModule F₂ where
  __ := GradedModuleMap hφ
  map_smul' := by
    intros s x
    apply @DirectSum.induction_on ℕ (GradedPiece F₁) _ _ (fun x ↦       (GradedModuleMap hφ) (s • ↑x) = s • (GradedModuleMap hφ) x) x
    · simp
    · intro n x
      apply @DirectSum.induction_on ℕ (GradedRingPiece I) _ _ _ s
      · simp
      · intro m s
        exact GradedModuleMap_of_smul_of hφ s x
      · intro s t h₁ h₂
        rw [add_smul]
        rw [add_smul]
        rw [←h₁, ←h₂]
        rw [AddMonoidHom.map_add]
    · intro x y h₁ h₂
      simp
      rw [h₁, h₂]

lemma GradedModuleHom_apply (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) (n : ℕ) (x : AssociatedGradedModule F₁) :
    (GradedModuleHom hφ x) n = (GradedPieceHom hφ n (x n)) := rfl
