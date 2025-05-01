import MyProject.am2_10

/-
  # Proposition 10.2
  Let `0 ⟶ {Aₙ} ⟶ {Bₙ} ⟶ {Cₙ} ⟶ 0` be an exact sequence of inverse systems, then
  i) `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ` is exact
  ii) If `{Aₙ}` is a surjective system, then `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ ⟶ 0` is exact.
-/


class AddInverseSystem (ι : ℕ → Type) [entry_is_group : ∀ i, AddCommGroup (ι i)] where
  transition_morphisms : ∀ i, (ι (i+1)) →+ (ι i)


def InverseLimit {ι : ℕ → Type} [entry_is_group : ∀ i, AddCommGroup (ι i)] (𝒜 : AddInverseSystem ι) : Set (∀ n : ℕ, ι n) :=
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





lemma am10_2_i : true := sorry
lemma am10_2_ii : true := sorry
