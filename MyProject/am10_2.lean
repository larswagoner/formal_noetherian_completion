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


instance (𝒜 : AddInverseSystem) : AddCommGroup (∀ n : ℕ, 𝒜.ι n) := by
  have h : ∀ n, AddCommGroup (𝒜.ι n) := by
    intro n
    apply 𝒜.entry_is_group n
  apply inferInstanceAs (AddCommGroup (Π n : ℕ, 𝒜.ι n))

variable (𝒜 : AddInverseSystem)

instance (X : InverseLimit 𝒜) : AddSubgroup (∀ n : ℕ, 𝒜.ι n) where
  carrier := {f : (∀ n : ℕ, 𝒜.ι n) | ∀ n, (𝒜.transition_morphisms n) (f (n+1)) = f n }
  add_mem' := by
    rintro a b ha hb n
    simp
    rw [ha, hb]
  zero_mem' := by
    intro n
    simp
  neg_mem' := by
    intro a ha n
    have h₀ : AddCommGroup (𝒜.ι n) := 𝒜.entry_is_group n
    have h₁ : AddCommGroup (𝒜.ι (n+1)) := 𝒜.entry_is_group (n+1)
    have h : 𝒜.ι (n+1) →+ 𝒜.ι n := 𝒜.transition_morphisms n
    rw [Pi.neg_apply, Pi.neg_apply]
    nth_rewrite 2 [<- ha]
    simp
    rw [map_neg]
    sorry



lemma am10_2_i : true := sorry
lemma am10_2_ii : true := sorry
