import MyProject.Completion.InverseSystem

variable {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n))

def AddInverseLimit [AddInverseSystem f] :=
  InverseSystem.limit (fun _ _ x ↦ Extendedf f x) ⊤

@[simp]
lemma compatible_entries [AddInverseSystem f] (x : AddInverseLimit f) {n m : Set.Iio (⊤ : ENat)} (h : n ≤ m) :
  (Extendedf f h) (x.1 m) = x.1 n := by apply x.2

@[simp]
lemma compatible_entries₂ [AddInverseSystem f] (x : (n : ↑(Set.Iio (⊤ : ENat))) → ExtendedF F ↑n ) (hx : x ∈ AddInverseLimit f) {n m : Set.Iio (⊤ : ENat)} (h : n ≤ m) :
  (Extendedf f h) (x m) = x n := by apply hx

def AddInverseLimitSubgroup [AddInverseSystem f] : AddSubgroup (∀ n : Set.Iio (⊤ : ENat), ExtendedF F n) where
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

instance [AddInverseSystem f] : AddCommGroup (AddInverseLimit f) :=
  AddSubgroup.toAddCommGroup (AddInverseLimitSubgroup f)



variable {G : ℕ → Type*} [∀ i, AddCommGroup (G i)] (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n))

def InverseLimitHom [AddInverseSystem f] [AddInverseSystem g] (ψ : f →ₛ+ g) : AddInverseLimit f →+ AddInverseLimit g where
  toFun := sorry
  map_zero' := sorry
  map_add' := sorry
