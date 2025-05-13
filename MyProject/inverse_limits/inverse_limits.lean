import Mathlib.Tactic
import Mathlib.Order.DirectedInverseSystem

class AddInverseSystem {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄,
(n ≤ m) → (F m) →+ (F n)) extends InverseSystem (fun _ _ h ↦ f h)

/-- Since inverse limits have been implemented for cardinals, a wrapper is needed to take inverse limits in the naive sense. -/
def ExtendedF (F : ℕ → Type) : ENat → Type := ENat.recTopCoe Unit F

instance (F : ℕ → Type) [h : ∀ i, AddCommGroup (F i)] : ∀ i, AddCommGroup (ExtendedF F i) := by
  apply ENat.recTopCoe
  · exact PUnit.addCommGroup
  · exact h

/-- Since inverse limits have been implemented for cardinals, a wrapper is needed to take inverse limits in the naive sense. -/
def Extendedf {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) : ∀ ⦃n m⦄, (n ≤ m) → (ExtendedF F m) →+ (ExtendedF F n) := by
  apply ENat.recTopCoe
  · intro m h
    show ExtendedF F m →+ Unit
    exact 0
  · intro a
    apply ENat.recTopCoe
    · intro h
      exact 0
    · intro b
      intro h
      exact f (ENat.coe_le_coe.mp h)

@[simp]
lemma Extendedf_top (F : ℕ → Type) [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) : ∀ j, ∀ x : ExtendedF F ⊤ , Extendedf f (@le_top _ _ _ j) x = 0 := by
  apply ENat.recTopCoe
  · intro x
    rfl
  · intro a x
    rfl

/-- Given an additive inverse system, give an instance of an InverseSystem in the Mathlib sense that can be used to take an inverse limit in the naive sense. -/
instance {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [h : AddInverseSystem f] : InverseSystem (fun _ _ x ↦ Extendedf f x) where
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

/-- The naive inverse limit of an additive invserse system. -/
def AddInverseLimit {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] := InverseSystem.limit (fun _ _ x ↦ Extendedf f x) ⊤

@[simp]
lemma compatible_entries {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] (x : AddInverseLimit f) {n m : Set.Iio (⊤ : ENat)} (h : n ≤ m) : (Extendedf f h) (x.1 m) = x.1 n := by apply x.2

@[simp]
lemma compatible_entries₂ {F : ℕ → Type} [∀ i, AddCommGroup (F i)] {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AddInverseSystem f] (x : (n : ↑(Set.Iio (⊤ : ENat))) → ExtendedF F ↑n ) (hx : x ∈ AddInverseLimit f) {n m : Set.Iio (⊤ : ENat)} (h : n ≤ m) : (Extendedf f h) (x m) = x n := by apply hx

def AddInverseLimitSubgroup {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] : AddSubgroup (∀ n : Set.Iio (⊤ : ENat), ExtendedF F n) where
  carrier := AddInverseLimit f
  add_mem' := by
    rintro a b ha hb n m hnm
    simp [ha, hb]
  zero_mem' := by
    intro _ _ _
    simp
  neg_mem' := by
    intro a ha n m hnm
    simp [ha]


instance {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] : AddCommGroup (AddInverseLimit f) :=
  AddSubgroup.toAddCommGroup (AddInverseLimitSubgroup f)

variable {F G : ℕ → Type} [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]

/-- A morphism of inverse systems consists of a group homomorphism at each entry, compatible with the maps of the inverse system. -/
structure AddInverseSystemHom (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)) [AddInverseSystem f] [AddInverseSystem g] where
  protected maps : ∀ n, F n →+ G n
  protected compatible : ∀ ⦃n m⦄, (h : n ≤ m) → (∀ x : F m , maps n (f h x) = g h (maps m x))

infixr:25 " →ₛ+ " => AddInverseSystemHom


