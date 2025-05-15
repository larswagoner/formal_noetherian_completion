import Mathlib.Order.DirectedInverseSystem
import Mathlib.Algebra.Module.SnakeLemma
import MyProject.Completion.NaiveInverseLimit
import MyProject.Completion.InverseSystem
import MyProject.Completion.ExactSequences
import Mathlib.Algebra.Exact


/-
  # Proposition 10.2
  Let `0 ⟶ {Aₙ} ⟶ {Bₙ} ⟶ {Cₙ} ⟶ 0` be an exact sequence of inverse systems, then
  i) `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ` is exact
  ii) If `{Aₙ}` is a surjective system, then `0 ⟶ lim Aₙ ⟶ lim Bₙ ⟶ lim Cₙ ⟶ 0` is exact.
-/


section DerivedMap

variable {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AddInverseSystem f]

@[simp]
lemma derivedKernelIsCoherent (a : (DerivedMap f).ker) ⦃n m : ℕ⦄ (h : n ≤ m) : (f h) (a.1 m) = a.1 n := by
  induction h using Nat.leRec with
  | refl =>
    simp
  | le_succ_of_le h ih =>
    rw [<- ih]
    expose_names
    have hh : (DerivedMap f) a = 0 := a.2
    have h₃ : a.1 k - f (Nat.le_succ k) (a.1 (k+1)) = 0 := by
      unfold DerivedMap at hh
      simp at hh
      exact congrFun hh k
    rw [eq_of_sub_eq_zero h₃]
    simp

theorem kernelDerivedEqNaiveInverseLimit : (DerivedMap f).ker = NaiveAddInverseLimit f := by
  ext x
  constructor
  · intro hx n m h
    exact derivedKernelIsCoherent ⟨x, hx⟩ h
  · intro hx
    simp
    ext n
    unfold DerivedMap
    simp [hx]


lemma lemmathatsomehowworks {M : Type*} {A B : Set M} {x : M} (xx : x ∈ A) (h : A = B) : x ∈ B := by
  rw [<- h]
  exact xx

lemma converter (x : NaiveAddInverseLimit f) : x.1 ∈ (DerivedMap f).ker := by
  have : x.1 ∈ NaiveAddInverseLimit f := x.2
  -- rw [kernelDerivedEqNaiveInverseLimit] Does not work????
  apply lemmathatsomehowworks this kernelDerivedEqNaiveInverseLimit.symm

def NaiveInvLimToKer (x : NaiveAddInverseLimit f) : (DerivedMap f).ker := ⟨x.1, converter x⟩

theorem NaiveInvLimToKerInj : ∀ x y : NaiveAddInverseLimit f, NaiveInvLimToKer x = NaiveInvLimToKer y → x = y := by
  intro x y hxy
  apply SetCoe.ext
  apply SetCoe.ext_iff.mpr hxy


-- variable {G : ℕ → Type*} [∀ i, AddCommGroup (G i)] {g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)} [AddInverseSystem g]

-- @[simp]
-- theorem NaiveInvLimToKerCompatible (x : NaiveAddInverseLimit f) {xx : x.1 ∈ (DerivedMap f).ker} (ϕ : (DerivedMap f).ker →+ (DerivedMap g).ker) : ϕ (NaiveInvLimToKer x) = (ϕ ⟨x.1, xx⟩) := by
--   congr

end DerivedMap


section ExactSequencesOnProduct

variable {F G H : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)]

variable {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AddInverseSystem f]
variable {g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)} [AddInverseSystem g]
variable {h : ∀ ⦃n m⦄, (n ≤ m) → (H m) →+ (H n)} [AddInverseSystem h]

def nthInducedSequence (AIS_SES : AddInverseSystemSES f g h) (n : ℕ) : AddCommGroupSES where
  X₁ := AddCommGrp.of (F n)
  X₂ := AddCommGrp.of (G n)
  X₃ := AddCommGrp.of (H n)
  f := groupHomToGrpHom (AIS_SES.ψ.maps n)
  g := groupHomToGrpHom (AIS_SES.ϕ.maps n)
  zero := by
    simp only [compIsMonoidComp, groupHomCompatible]
    rw [rangeEqKerToCompEqZero (AIS_SES.mid n)]
    exact GrpHomZero
  injective := by
    simp only [groupHomCompatible, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    exact AIS_SES.inj n
  middle := by
    apply le_of_eq
    simp only [groupHomCompatible]
    exact (AIS_SES.mid n).symm
  surjective := by
    simp only [groupHomCompatible, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    exact AIS_SES.surj n


def InducedSequenceOnProduct (AIS_SES : AddInverseSystemSES f g h) : AddCommGroupSES := by
  apply productOfSESisSES (fun n ↦ nthInducedSequence AIS_SES n)

def InducedDiagramOfSES (AIS_SES : AddInverseSystemSES f g h) : CommDiagramOfSES where
  s₁ := InducedSequenceOnProduct AIS_SES
  s₂ := InducedSequenceOnProduct AIS_SES
  v₁ := groupHomToGrpHom (DerivedMap f)
  v₂ := groupHomToGrpHom (DerivedMap g)
  v₃ := groupHomToGrpHom (DerivedMap h)
  commleft := by
    simp only [compIsMonoidComp, groupHomCompatible]
    congr 1
    apply derivedMapCommutes.symm
  commright := by
    simp only [compIsMonoidComp, groupHomCompatible]
    congr 1
    apply derivedMapCommutes.symm


end ExactSequencesOnProduct


variable {F G H : ℕ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)]

variable {f : ∀ ⦃n m⦄, (n ≤ m) → (F m) →+ (F n)} [AddInverseSystem f]
variable {g : ∀ ⦃n m⦄, (n ≤ m) → (G m) →+ (G n)} [AddInverseSystem g]
variable {h : ∀ ⦃n m⦄, (n ≤ m) → (H m) →+ (H n)} [AddInverseSystem h]

lemma am10_2_i_inj (AIS_SES : AddInverseSystemSES f g h) : Function.Injective (InducedNaiveInverseLimitHom AIS_SES.ψ) := by
  let dia := InducedDiagramOfSES AIS_SES
  intro x y hxy
  have eq : NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ψ) x) = NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ψ) y) := by rw [hxy]
  rw [<- kernelDerivedEqNaiveInverseLimit] at x
  rw [<- kernelDerivedEqNaiveInverseLimit] at y
  have : ∀ a, dia.s₁.f.hom' a =  (fun n ↦ AIS_SES.ψ.maps n (a n)) := by
    intro a
    rfl
  have : ∀ w, NaiveInvLimToKer (InducedNaiveInverseLimitHom AIS_SES.ψ w) = inducedMap₁ dia (NaiveInvLimToKer w) := by
    intro w
    simp only [InducedNaiveInverseLimitHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, induced₁Coincide, this]
    rfl
  repeat rw [this] at eq
  apply NaiveInvLimToKerInj
  exact inducedMap₁Injective eq

lemma am10_2_i_exactMiddle (AIS_SES : AddInverseSystemSES f g h) : Function.Exact (InducedNaiveInverseLimitHom AIS_SES.ψ) (InducedNaiveInverseLimitHom AIS_SES.ϕ) := sorry
lemma am10_2_ii (AIS_SES : AddInverseSystemSES f g h) (firstSystemSurj : SurjectiveSystem f) : Function.Surjective (InducedNaiveInverseLimitHom AIS_SES.ϕ) := sorry


def InverseLimitsExact (AIS_SES : AddInverseSystemSES f g h) (firstSystemSurj : SurjectiveSystem f) : AddCommGroupSES where
  X₁ := AddCommGrp.of (NaiveAddInverseLimit f)
  X₂ := AddCommGrp.of (NaiveAddInverseLimit g)
  X₃ := AddCommGrp.of (NaiveAddInverseLimit h)
  f := groupHomToGrpHom (InducedNaiveInverseLimitHom AIS_SES.ψ)
  g := groupHomToGrpHom (InducedNaiveInverseLimitHom AIS_SES.ϕ)
  zero := by
    simp only [compIsMonoidComp, groupHomCompatible]
    have : ((InducedNaiveInverseLimitHom AIS_SES.ϕ).comp (InducedNaiveInverseLimitHom AIS_SES.ψ)) = 0 := by
      exact rangeEqKerToCompEqZero (AddMonoidHom.exact_iff.mp (am10_2_i_exactMiddle AIS_SES)).symm
    rw [this]
    simp only [GrpHomZero]
  injective := am10_2_i_inj AIS_SES
  middle := by
    apply le_of_eq (AddMonoidHom.exact_iff.mp (am10_2_i_exactMiddle AIS_SES))
  surjective := am10_2_ii AIS_SES firstSystemSurj
