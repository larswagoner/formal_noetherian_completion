import MyProject.Completion.InverseSystem

variable {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] (f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n))

def NaiveAddInverseLimit [AddInverseSystem f] : Set (∀ n, F n) :=
  {a | ∀ ⦃n m⦄ (h : n ≤ m), f h (a m) = a n}

@[simp]
lemma naive_compatible_entries [AddInverseSystem f] (x : NaiveAddInverseLimit f) {n m : ℕ} (h : n ≤ m) :
  f h (x.1 m) = x.1 n := by apply x.2

@[simp]
lemma naive_compatible_entries₂ [AddInverseSystem f] (x : ∀ n, F n) (hx : x ∈ NaiveAddInverseLimit f) {n m : ℕ} (h : n ≤ m) :
  f h (x m) = x n := by apply hx



variable {G : ℕ → Type*} [∀ i, AddCommGroup (G i)] (g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n))

@[simp]
lemma NaiveAddInverseLimit_compatible [AddInverseSystem f] [AddInverseSystem g] {ψ : f →ₛ+ g} ⦃n m : ℕ⦄ {h : n ≤ m} {x : NaiveAddInverseLimit f} : (g h) ((ψ.maps m) (x.1 m)) = (ψ.maps n) (x.1 n) := by
  rw [<- ψ.compatible h]
  simp

lemma NaiveAddInverseLimit_compatible₂ [AddInverseSystem f] [AddInverseSystem g] {ψ : f →ₛ+ g} {n : ℕ} {x y : NaiveAddInverseLimit f} : ψ.maps n (x.1 n) + ψ.maps n (y.1 n) = ψ.maps n (x.1 n + y.1 n) := by
  rw [(ψ.maps n).map_add]


def NaiveAddInverseLimitSubgroup [AddInverseSystem f] : AddSubgroup (∀ n, F n) where
  carrier := NaiveAddInverseLimit f
  add_mem' := by
    rintro a b ha hb n m hnm
    simp [ha, hb]
  zero_mem' := by
    intro a k h
    simp
  neg_mem' := by
    intro a ha n m hnm
    simp [ha]

instance [AddInverseSystem f] : AddCommGroup (NaiveAddInverseLimit f) :=
  AddSubgroup.toAddCommGroup (NaiveAddInverseLimitSubgroup f)


variable {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} {g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)}
variable [AddInverseSystem f] [AddInverseSystem g]

lemma NaiveAddInverseLimit_compatible₃ (ψ : f →ₛ+ g) (n : ℕ) {x y : NaiveAddInverseLimit f} : (ψ.maps n ((x + y).1 n)) = ψ.maps n (x.1 n + y.1 n) := by
  suffices (x+y).1 n = x.1 n + y.1 n by rfl
  rfl


def InducedNaiveInverseLimitHom (ψ : f →ₛ+ g) : NaiveAddInverseLimit f →+ NaiveAddInverseLimit g where
  toFun := by
    intro x
    use fun n ↦ ψ.maps n (x.1 n)
    intro n m h
    simp
  map_zero' := by
    ext n
    simp
    apply (ψ.maps n).map_zero
  map_add' := by
    simp
    intro a ha b hb
    ext n
    simp
    rw [NaiveAddInverseLimit_compatible₃, <- NaiveAddInverseLimit_compatible₂]
    rfl


@[simp]
lemma NaiveInverseLimitHom_compatible (ψ : f →ₛ+ g) (x : NaiveAddInverseLimit f) (n : ℕ) :
  ((InducedNaiveInverseLimitHom ψ) x).1 n = ψ.maps n (x.1 n) := rfl

@[simp]
lemma NaiveInverseLimitHom_compatible₂ (ψ : f →ₛ+ g) (x : NaiveAddInverseLimit f) ⦃n m : ℕ⦄ (h : n ≤ m) :
  g h (((InducedNaiveInverseLimitHom ψ) x).1 m) = ψ.maps n (x.1 n) := by simp

def InducedNaiveInverseLimitIso_of_AddInverseSystemIso (ψ : AddInverseSystemIso f g) :
    NaiveAddInverseLimit f ≃+ NaiveAddInverseLimit g where
  __ := InducedNaiveInverseLimitHom ψ.toHom
  invFun := InducedNaiveInverseLimitHom ψ.invHom
  left_inv := by
    intro x
    ext n
    exact ψ.left_inv n (x.1 n)
  right_inv := by
    intro x
    ext n
    exact ψ.right_inv n (x.1 n)
