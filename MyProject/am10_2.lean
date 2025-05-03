import MyProject.am2_10
import Mathlib.Order.DirectedInverseSystem

/-
  # Proposition 10.2
  Let `0 ⟶ {Aₙ} ⟶ {Bₙ} ⟶ {Cₙ} ⟶ 0` be an exact sequence of inverse systems, then
  i) `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ` is exact
  ii) If `{Aₙ}` is a surjective system, then `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ ⟶ 0` is exact.
-/

class AddInverseSystem {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) extends InverseSystem (fun _ _ h ↦ f h)

def ExtendedF (F : ℕ → Type) : ENat → Type := ENat.recTopCoe Unit F

instance (F : ℕ → Type) [h : ∀ i, AddCommGroup (F i)] : ∀ i, AddCommGroup (ExtendedF F i) := by
  apply ENat.recTopCoe
  · exact PUnit.addCommGroup
  · exact h

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
    intro a k h
    simp
  neg_mem' := by
    intro a ha n m hnm
    simp [ha]


instance {F : ℕ → Type} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) [AddInverseSystem f] : AddCommGroup (AddInverseLimit f) :=
  AddSubgroup.toAddCommGroup (AddInverseLimitSubgroup f)

variable (F G : ℕ → Type) [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
variable (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)) (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n))



/-
def InverseLimit {F : ℕ → Type} [entry_is_group : ∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) → (F n)) (𝒜 : AddInverseSystem F) : Set (∀ n : ℕ, ι n) :=
  { f : (∀(n : ℕ), (ι n)) | ∀ n, (𝒜.transition_morphisms n) (f (n+1)) = f n }


instance (ι : ℕ → Type) [entry_is_group : ∀ i, AddCommGroup (ι i)] : AddCommGroup (∀ n : ℕ, ι n) := by
  have h : ∀ n, AddCommGroup (ι n) := by
    intro n
    apply entry_is_group n
  apply inferInstanceAs (AddCommGroup (Π n : ℕ, ι n))

variable (ι : ℕ → Type) [entry_is_group : ∀ i, AddCommGroup (ι i)]
variable (𝒜 : AddInverseSystem ι)


def InverseLimitSubgroup {ι : ℕ → Type} [entry_is_group : ∀ i, AddCommGroup (ι i)] (𝒜 : AddInverseSystem ι) : AddSubgroup (∀ n : ℕ, ι n) where
  carrier := InverseLimit 𝒜
  add_mem' := by
    rintro a b ha hb n
    simp
    rw [ha, hb]
  zero_mem' := by
    intro n
    simp
  neg_mem' := by
    intro a ha n
    rw [Pi.neg_apply, Pi.neg_apply]
    nth_rewrite 2 [<- ha]
    rw [map_neg]

instance (ι : ℕ → Type) [entry_is_group : ∀ i, AddCommGroup (ι i)]  (𝒜 : AddInverseSystem ι) : AddCommGroup (InverseLimit 𝒜) :=
    AddSubgroup.toAddCommGroup (InverseLimitSubgroup 𝒜)
-/




lemma am10_2_i : true := sorry
lemma am10_2_ii : true := sorry
