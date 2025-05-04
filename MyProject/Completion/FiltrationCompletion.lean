import MyProject.Completion.NaiveInverseLimit
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Algebra

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]
variable (F : I.Filtration M)

def FiltrationIS : ℕ → Type v := fun n ↦ M ⧸ (F.N n)

instance (i : ℕ) : AddCommGroup (FiltrationIS F i) := by
  unfold FiltrationIS
  infer_instance

instance (i : ℕ) : Module A (FiltrationIS F i) := by
  unfold FiltrationIS
  infer_instance

def FISTransitionMap :
    ∀ ⦃n m⦄, n ≤ m → FiltrationIS F m →+ FiltrationIS F n :=
  fun n m h ↦ (Submodule.mapQ (F.N m) (F.N n) (LinearMap.id) (Ideal.Filtration.antitone F h)).toAddMonoidHom

lemma FISTransitionMap_smul {n m : ℕ} (h : n ≤ m) (a : A) (x : FiltrationIS F m) :
    FISTransitionMap F h (a • x) = a • FISTransitionMap F h x :=
  (Submodule.mapQ (F.N m) (F.N n) (LinearMap.id) (Ideal.Filtration.antitone F h)).map_smul a x

instance : AddInverseSystem (FISTransitionMap F) where
  map_self := by
    rintro n ⟨x⟩
    rfl
  map_map := by
    rintro k j i hkj hji ⟨x⟩
    rfl

def FiltrationCompletion : Type v :=
  NaiveAddInverseLimit (FISTransitionMap F)

@[ext]
lemma FiltrationCompletion_ext (x y : FiltrationCompletion F) (h : ∀ n, x.1 n = y.1 n) :
    x = y := by
  apply Subtype.coe_inj.mp
  ext n
  exact h n

instance : AddCommGroup (FiltrationCompletion F) :=
  instAddCommGroupElemForallNaiveAddInverseLimit (FISTransitionMap F)

instance : Module A (FiltrationCompletion F) where
  smul := fun a m ↦ ⟨fun n ↦ a • (m.1 n), by
      intro j k hjk
      rw [FISTransitionMap_smul]
      simp
    ⟩
  one_smul := by
    intro m
    ext n
    show 1 • (m.1 n) = m.1 n
    module
  mul_smul := by
    intro a b m
    ext n
    show (a * b) • (m.1 n) = a • b • m.1 n
    module
  smul_zero := by
    intro a
    ext n
    show a • 0 = 0
    module
  smul_add := by
    intro a m m'
    ext n
    show a • (m.1 n + m'.1 n) = a • m.1 n + a • m'.1 n
    module
  add_smul := by
    intro a b m
    ext n
    show (a + b) • m.1 n = a • m.1 n + b • m.1 n
    module
  zero_smul := by
    intro m
    ext n
    show 0 • m.1 n = 0
    module

def FiltrationCompletion.of (F : I.Filtration M) :
    M →ₗ[A] (FiltrationCompletion F) where
  toFun := fun m ↦ ⟨fun _ ↦ ⟦m⟧, fun _ _ _ ↦ rfl⟩
  map_smul' := fun _ _ ↦ rfl
  map_add' := fun _ _ ↦ rfl

lemma AdicCompletion_eq_FiltrationCompletion :
  AdicCompletion I M = FiltrationCompletion (I.stableFiltration (⊤ : Submodule A M)) := rfl

end

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
variable {F₁ : I.Filtration M₁} {F₂ : I.Filtration M₂} {φ : M₁ →ₗ[A] M₂}

def FISystemHom.of_comap_le (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) :
    AddInverseSystemHom (FISTransitionMap F₁) (FISTransitionMap F₂) where
  maps := fun n ↦ (Submodule.mapQ _ _ φ (hφ n)).toAddMonoidHom
  compatible := by
    rintro _ _ _ ⟨x⟩
    rfl

def FiltrationCompletionHom.of_comap_le (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) :
  FiltrationCompletion F₁ →ₗ[A] FiltrationCompletion F₂ := {
    __ := InverseLimitHom (FISystemHom.of_comap_le hφ)
    map_smul' := by
      intro a m
      simp
      ext n
      show _ = a • _
      rw [InverseLimitHom_apply]
      show (Submodule.mapQ _ _ φ (hφ n)) (a • m.1 n) = _
      rw [(Submodule.mapQ _ _ φ (hφ n)).map_smul]
      rfl
  }

def FiltrationCompletionHom.comm (hφ : ∀ n, F₁.N n ≤ (F₂.N n).comap φ) :
  (FiltrationCompletion.of F₂).comp φ =
    (FiltrationCompletionHom.of_comap_le hφ).comp (FiltrationCompletion.of F₁) := rfl
