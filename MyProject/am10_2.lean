import Mathlib
import MyProject.am2_10

/-
  # Proposition 10.2
  Let `0 ⟶ {Aₙ} ⟶ {Bₙ} ⟶ {Cₙ} ⟶ 0` be an exact sequence of inverse systems, then
  i) `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ` is exact
  ii) If `{Aₙ}` is a surjective system, then `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ ⟶ 0` is exact.
-/


class AddInverseSystem where
  ι : ℕ → Type
  entry_is_group : ∀ i, AddCommGroup (ι i)
  transition_morphisms : ∀ i, (ι (i+1)) →+ (ι i)


class AddInverseSystem₂ (ι : ℕ → Type) [(i : ℕ) → AddCommGroup (ι i)] where
  transition_morphisms : ∀ i, (ι (i+1)) →+ (ι i)


instance alwaysZ : (ℕ → Type) := (fun _ ↦ ℤ)

instance example_of_inverse_system : AddInverseSystem where
  ι := alwaysZ
  entry_is_group := by
    intro i
    unfold alwaysZ
    infer_instance
  transition_morphisms := by
    intro i
    unfold alwaysZ
    apply (AddMonoidHom.id ℤ)


def InverseLimit (𝒜 : AddInverseSystem) : Type _ :=
  { f : (∀(n : ℕ), (𝒜.ι n)) | ∀ n, (𝒜.transition_morphisms n) (f (n+1)) = f n }

#check example_of_inverse_system
#check InverseLimit example_of_inverse_system

#check DirectLimit
/-
instance d (𝒜 : AddInverseSystem) : AddCommMonoid (∀ n : ℕ, 𝒜.ι n) where
  add := by
    intro h k n
    have _ : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    apply (h n) + (k n)
  add_assoc := by
    intro a b c
    ext n
    simp
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    abel
  zero := by
    intro n
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    apply x.zero
  zero_add := by
    intro a
    ext n
    simp
    apply (𝒜.entry_is_group n).zero_add
  add_zero := by
    intro a
    ext n
    simp
    apply (𝒜.entry_is_group n).add_zero
  nsmul := by sorry
  add_comm := by
    intro a b
    ext n
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    simp
    abel
-/
/-
instance d₂ (ι : ℕ → Type) [h : (i : ℕ) → AddCommGroup (ι i)] (𝒜 : (AddInverseSystem₂ ι ((i : ℕ) → AddCommGroup (ι i)))) : AddCommMonoid (∀ n : ℕ, 𝒜.ι n) where
  add := by
    intro h k n
    have _ : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    apply (h n) + (k n)
  add_assoc := by
    intro a b c
    ext n
    simp
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    abel
  zero := by
    intro n
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    apply x.zero
  zero_add := by
    intro a
    ext n
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    simp
    -- help
    sorry
  add_zero := by sorry
  nsmul := sorry --nsmulRec
  add_comm := by
    intro a b
    ext n
    have x : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    simp
    abel



instance subgroup (𝒜 : AddInverseSystem) : AddSubgroup (∀ n : ℕ, 𝒜.ι n) where sorry

instance M : LE ℕ where
  le := fun x y ↦ y ≤ x

instance K : LT ℕ where
  lt := fun x y ↦ y < x

instance N : Preorder ℕ where
  le := fun x y ↦ y ≤ x
  lt := fun x y ↦ y < x
  lit_iff_le_not_le := by sorry
  le_refl := by sorry
  le_trans := by sorry

-/

lemma am10_2_i : true := sorry
lemma am10_2_ii : true := sorry
