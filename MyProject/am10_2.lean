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

noncomputable def recursiveSolution (surj_sys : SurjectiveSystem f) (y : (i : ℕ) → F i) : (i : ℕ) → F i := fun
| 0 => 0
| n+1 => (surj_sys (by norm_num) ((recursiveSolution surj_sys y) n - y n)).choose

theorem recursiveSolutionIsSolution (surj_sys : SurjectiveSystem f) : ∀ y, (DerivedMap f) (recursiveSolution surj_sys y) = y := by
  intro y
  have : ∀ n, (recursiveSolution surj_sys y) n - (f (by norm_num) ((recursiveSolution surj_sys y) (n+1))) = y n := by
    intro n
    /- Only unfolding once is quite hard apparently -/
    change _ - (f (by norm_num)) (surj_sys (by norm_num) ((recursiveSolution surj_sys y) n - y n)).choose = _
    rw [Exists.choose_spec (surj_sys (by norm_num) ((recursiveSolution surj_sys y) n - y n))]
    abel
  ext n
  unfold DerivedMap
  simp
  exact this n

theorem derivedSurjOfSystemSurj (surj_sys : SurjectiveSystem f) : Function.Surjective (DerivedMap f) := by
  intro y
  use recursiveSolution surj_sys y
  exact recursiveSolutionIsSolution surj_sys y


lemma lemmathatsomehowworks {M : Type*} {A B : Set M} {x : M} (xx : x ∈ A) (h : A = B) : x ∈ B := by
  rw [<- h]
  exact xx

lemma converter (x : NaiveAddInverseLimit f) : x.1 ∈ (DerivedMap f).ker := by
  have : x.1 ∈ NaiveAddInverseLimit f := x.2
  -- rw [kernelDerivedEqNaiveInverseLimit] Does not work????
  apply lemmathatsomehowworks this kernelDerivedEqNaiveInverseLimit.symm

def NaiveInvLimToKer : (NaiveAddInverseLimit f) →+ (DerivedMap f).ker where
  toFun := fun x ↦ ⟨x.1, converter x⟩
  map_zero' := rfl
  map_add' := by
    intro x y
    rfl

lemma converter₂ (x : (DerivedMap f).ker) : x.1 ∈ NaiveAddInverseLimit f := by
  have : x.1 ∈ (DerivedMap f).ker := x.2
  -- rw [kernelDerivedEqNaiveInverseLimit] Does not work????
  apply lemmathatsomehowworks this kernelDerivedEqNaiveInverseLimit

def KerToNaiveInvLim : (DerivedMap f).ker →+ (NaiveAddInverseLimit f) where
  toFun := fun x ↦ ⟨x.1, converter₂ x⟩
  map_zero' := rfl
  map_add' := by
    intro x y
    rfl

def NaiveIsomKer : NaiveAddInverseLimit f ≃+ (DerivedMap f).ker where
  toFun := NaiveInvLimToKer
  invFun := KerToNaiveInvLim
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl
  map_add' := NaiveInvLimToKer.map_add'


theorem NaiveInvLimToKerInj : ∀ x y : NaiveAddInverseLimit f, NaiveInvLimToKer x = NaiveInvLimToKer y → x = y := by
  intro x y hxy
  apply SetCoe.ext
  apply SetCoe.ext_iff.mpr hxy


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

lemma am10_2_i_exactMiddle (AIS_SES : AddInverseSystemSES f g h) : Function.Exact (InducedNaiveInverseLimitHom AIS_SES.ψ) (InducedNaiveInverseLimitHom AIS_SES.ϕ) := by
  let dia := InducedDiagramOfSES AIS_SES

  /- The following 4 haves should probably be separate lemmas -/
  have comm₁ : ∀ x, NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ψ) x) = (inducedMap₁ dia) (NaiveInvLimToKer x) := by intro x; rfl
  have comm₂ : ∀ x, NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ϕ) x) = (inducedMap₂ dia) (NaiveInvLimToKer x) := by intro x; rfl
  have ker : ∀ x, x ∈ (InducedNaiveInverseLimitHom AIS_SES.ϕ).ker ↔ NaiveInvLimToKer x ∈ (inducedMap₂ dia).ker := by
    intro x
    constructor
    · intro hx
      simp
      suffices NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ϕ) x) = 0 by
        rw [comm₂] at this
        exact this
      rw [hx]
      simp
    · intro hx
      have : NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ϕ) x) = 0 := by
        rw [comm₂]
        exact hx
      rw [<- map_zero NaiveInvLimToKer] at this
      apply NaiveInvLimToKerInj at this
      exact this

  have range : ∀ x, x ∈ (InducedNaiveInverseLimitHom AIS_SES.ψ).range ↔ NaiveInvLimToKer x ∈ (inducedMap₁ dia).range := by
    intro x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      use NaiveInvLimToKer w
      rw [<- comm₁]
      rw [hw]
    · intro hx
      rcases hx with ⟨w, hw⟩
      use KerToNaiveInvLim w
      have : w = NaiveInvLimToKer (KerToNaiveInvLim w) := rfl
      rw [this, <- comm₁] at hw
      apply NaiveInvLimToKerInj at hw
      exact hw

  apply AddMonoidHom.exact_iff.mpr
  ext x
  rw [ker]
  have : NaiveInvLimToKer x ∈ (inducedMap₂ dia).ker ↔ NaiveInvLimToKer x ∈ (inducedMap₁ dia).range := by
    rw [inducedMap₁RangeEqinducedMap₂Ker]
  rw [this, range]


lemma CokerOfSurjMorphismIsTrivial {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ψ : A →+ B} (ψsurj : Function.Surjective ψ): ∀ x : cokernel ψ, x = 0 := by
  intro x
  unfold cokernel at x
  rcases (QuotientAddGroup.mk'_surjective ψ.range x) with ⟨w, hw⟩
  rw [<- hw]
  apply (QuotientAddGroup.eq_zero_iff w).mpr
  apply ψsurj

lemma kerOfMorphismToCokerOfSurjMorphism {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {ψ : A →+ B} (ψsurj : Function.Surjective ψ) {ϕ : C →+ cokernel ψ} : ∀ x, ϕ x = 0 := by
  intro x
  exact CokerOfSurjMorphismIsTrivial ψsurj (ϕ x)


lemma am10_2_ii (AIS_SES : AddInverseSystemSES f g h) (firstSystemSurj : SurjectiveSystem f) : Function.Surjective (InducedNaiveInverseLimitHom AIS_SES.ϕ) := by
  let dia := InducedDiagramOfSES AIS_SES
  have : Function.Surjective (inducedMap₂ dia) := by
    apply AddMonoidHom.range_eq_top.mp
    rw [<- AddMonoidHom.exact_iff.mp (DeltaExact dia)]
    ext x
    constructor
    · intro hx
      exact AddSubgroup.mem_top x
    · intro hx
      exact kerOfMorphismToCokerOfSurjMorphism (derivedSurjOfSystemSurj firstSystemSurj) x

  /- Two haves (basically) copied from the proof of am10_2_i -/
  have comm₂ : ∀ x, NaiveInvLimToKer ((InducedNaiveInverseLimitHom AIS_SES.ϕ) x) = (inducedMap₂ dia) (NaiveInvLimToKer x) := by intro x; rfl
  have range : ∀ x, x ∈ (InducedNaiveInverseLimitHom AIS_SES.ϕ).range ↔ NaiveInvLimToKer x ∈ (inducedMap₂ dia).range := by
    intro x
    constructor
    · intro hx
      rcases hx with ⟨w, hw⟩
      use NaiveInvLimToKer w
      rw [<- comm₂]
      rw [hw]
    · intro hx
      rcases hx with ⟨w, hw⟩
      use KerToNaiveInvLim w
      have : w = NaiveInvLimToKer (KerToNaiveInvLim w) := rfl
      rw [this, <- comm₂] at hw
      apply NaiveInvLimToKerInj at hw
      exact hw

  apply AddMonoidHom.range_eq_top.mp
  ext x
  rw [range]
  constructor
  all_goals intro hx
  · exact AddSubgroup.mem_top x
  · exact this (NaiveInvLimToKer x)


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
