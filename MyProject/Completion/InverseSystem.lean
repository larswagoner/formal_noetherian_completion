import Mathlib.Tactic
import Mathlib.Order.DirectedInverseSystem
import MyProject.Completion.ExactSequences


class AddInverseSystem {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) extends
  InverseSystem (fun _ _ h ↦ f h)

@[simp]
lemma fSelf {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AIS : AddInverseSystem f] : ∀ n : ℕ, ∀ x : F n, (f (le_refl n)) x = x := by
  apply AIS.map_self

@[simp]
lemma fCompatible {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AIS : AddInverseSystem f] : ∀ ⦃n m k : ℕ⦄ (hnm : n ≤ m) (hmk : m ≤ k), ∀ x, f hnm (f hmk x) = f (le_trans hnm hmk) x := by
  apply AIS.map_map

/- Related to Mathlib inverse limits, not used in final result -------------------------------/
def ExtendedF (F : ℕ → Type u) : ENat → Type u :=
  ENat.recTopCoe PUnit F

instance (F : ℕ → Type*) [h : ∀ i, AddCommGroup (F i)] : ∀ i, AddCommGroup (ExtendedF F i) := by
  apply ENat.recTopCoe
  · exact PUnit.addCommGroup
  · exact h

def Extendedf {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) :
    ∀ ⦃n m⦄, (n ≤ m) → (ExtendedF F m) →+ (ExtendedF F n) := by
  apply ENat.recTopCoe
  · intro m h
    show ExtendedF F m →+ PUnit
    exact 0
  · intro a
    apply ENat.recTopCoe
    · intro h
      exact 0
    · intro b
      intro h
      exact f (ENat.coe_le_coe.mp h)

@[simp]
lemma Extendedf_top (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) :
    ∀ j, ∀ x : ExtendedF F ⊤ , Extendedf f (@le_top _ _ _ j) x = 0 := by
  apply ENat.recTopCoe
  · intro x
    rfl
  · intro a x
    rfl

instance {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [h : AddInverseSystem f] :
    InverseSystem (fun _ _ x ↦ Extendedf f x) where
  map_self := by
    apply ENat.recTopCoe
    · intro x
      rfl
    · exact h.map_self
  map_map := by
    apply ENat.recTopCoe
    · intro _ _ _ _ _
      rfl
    · intro a
      apply ENat.recTopCoe
      · intro i haj hji x
        show 0 = _
        have : i = ⊤ := eq_top_iff.mpr hji
        subst this
        simp
      · intro b
        apply ENat.recTopCoe
        · intro hab hjt x
          simp
        · intro c hab hbc x
          exact h.map_map (ENat.coe_le_coe.mp hab) (ENat.coe_le_coe.mp hbc) x
/- --------------------------------------------------------------------------------------------/


def SurjectiveSystem {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] : Prop :=
  ∀ ⦃n m⦄ (h : n ≤ m), Function.Surjective (f h)

def DerivedMap {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] : (∀ i, F i) →+ (∀ i, F i) where
  toFun := by
    intro a n
    have h : n ≤ n+1 := by linarith
    use (a n) - f h (a (n+1))
  map_zero' := by
    simp
    ext n
    rfl
  map_add' := by
    intro x y
    ext n
    simp
    abel


section ExactnessProperties

variable {F G : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]

/-- A morphism of inverse systems consists of a group homomorphism at each entry, compatible with the maps of the inverse system. -/
structure AddInverseSystemHom (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)) [AddInverseSystem f] [AddInverseSystem g] where
  protected maps : ∀ n, F n →+ G n
  protected compatible : ∀ ⦃n m⦄, (h : n ≤ m) → (∀ x : F m , maps n (f h x) = g h (maps m x))

infixr:25 " →ₛ+ " => AddInverseSystemHom

variable {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} {g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)} [AddInverseSystem f] [AddInverseSystem g]

@[simp]
lemma AddInverseSystemHom_compatible (ψ : f →ₛ+ g) ⦃n m : ℕ⦄ (h : n ≤ m) (x : F m) : ψ.maps n (f h x) = g h (ψ.maps m x) := ψ.compatible h x

theorem derivedMapCommutes {ψ : f →ₛ+ g} : (productMap ψ.maps).comp (DerivedMap f) = (DerivedMap g).comp (productMap ψ.maps) := by
  ext x n
  simp only [productMap, DerivedMap, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, map_sub,
    AddInverseSystemHom_compatible]


def InjectiveSystemHom (ψ : f →ₛ+ g) : Prop :=
  ∀ n, (ψ.maps n).toFun.Injective

def SurjectiveSystemHom (ψ : f →ₛ+ g) : Prop :=
  ∀ n, (ψ.maps n).toFun.Surjective

variable {H : ℕ → Type*} [∀ i, AddCommGroup (H i)] {h : ∀ ⦃n m⦄, (n ≤ m) → (H m) →+ (H n)} [AddInverseSystem h]

def SystemHomComposition (ϕ : g →ₛ+ h) (ψ : f →ₛ+ g) : f →ₛ+ h where
  maps := fun n ↦ AddMonoidHom.comp (ϕ.maps n) (ψ.maps n)
  compatible := by
    intro n m h x
    simp


infixr:25 " ∘ₛ " => SystemHomComposition


def ExactAtMiddleSystem (ψ : f →ₛ+ g) (ϕ : g →ₛ+ h) : Prop :=
  ∀ n, AddMonoidHom.range (ψ.maps n) = AddMonoidHom.ker (ϕ.maps n)

end ExactnessProperties

variable {F G H : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)]

variable (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n))  [AddInverseSystem f]
variable (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)) [AddInverseSystem g]
variable (h : ∀ ⦃n m⦄, (n ≤ m) → (H m) →+ (H n)) [AddInverseSystem h]

structure AddInverseSystemSES where
  ψ : f →ₛ+ g
  ϕ : g →ₛ+ h
  inj : InjectiveSystemHom ψ
  mid : ExactAtMiddleSystem ψ ϕ
  surj : SurjectiveSystemHom ϕ

structure AddInverseSystemIso (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)) [AddInverseSystem f] [AddInverseSystem g] where
  protected toHom : f →ₛ+ g
  protected invHom : g →ₛ+ f
  protected left_inv : ∀ n, Function.LeftInverse (invHom.maps n) (toHom.maps n)
  protected right_inv : ∀ n, Function.RightInverse (invHom.maps n) (toHom.maps n)

def AddInverseSystemIso_of_iso (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)) [AddInverseSystem f] [AddInverseSystem g]
  (ψ : ∀ n, F n ≃+ G n) (ψ_comp : ∀ ⦃n m⦄, (h : n ≤ m) → (∀ x : F m , ψ n (f h x) = g h (ψ m x))) :
    AddInverseSystemIso f g where
  toHom := {
    maps := fun n ↦ ψ n
    compatible := ψ_comp
  }
  invHom := {
    maps := fun n ↦ (ψ n).symm
    compatible := by
      intro n m hnm x
      have := ψ_comp hnm ((ψ m).symm x)
      calc
        (ψ n).symm (g hnm x) = (ψ n).symm (g hnm (ψ m ((ψ m).symm x))) := by simp
        _ =  (ψ n).symm (ψ n (f hnm ((ψ m).symm x))) := by rw [ψ_comp hnm ((ψ m).symm x)]
        _ = f hnm ((ψ m).symm x) := by simp
  }
  left_inv := fun n ↦ by simp [Function.LeftInverse]
  right_inv := fun n ↦ by simp [Function.RightInverse, Function.LeftInverse]
