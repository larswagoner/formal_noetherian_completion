import Mathlib.Tactic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Init


open CategoryTheory

def groupHomToGrpHom {A B : AddCommGrp} (f : A →+ B) : A ⟶ B := by
  use f
  simp

@[simp]
lemma compIsMonoidComp {A B C : AddCommGrp} {f : A ⟶ B} {g : B ⟶ C} : (f ≫ g) = groupHomToGrpHom (AddMonoidHom.comp g.hom' f.hom') := by
  rfl


lemma compIsMonoidComp₂ {A B C : AddCommGrp} {f : A ⟶ B} {g : B ⟶ C} : AddMonoidHom.comp g.hom' f.hom' = (f ≫ g).hom' := by
  rfl

section Complexes

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable {g : B →+ C} {f : A →+ B}

def GroupsToComplex (h : g.comp f = 0) : CategoryTheory.ShortComplex AddCommGrp where
  X₁ := AddCommGrp.of A
  X₂ := AddCommGrp.of B
  X₃ := AddCommGrp.of C
  f := by
    use f
    simp
  g := by
    use g
    simp
  zero := by
    simp
    ext x
    simp
    have MonoidCompisFuncComp : g (f x) = (AddMonoidHom.comp g f) x := by
      rfl
    have compIsZero : g (f x) = 0 := by
      rw [MonoidCompisFuncComp, h]
      rfl
    apply compIsZero


@[simp]
lemma compIsZero (s : CategoryTheory.ShortComplex AddCommGrp) : AddMonoidHom.comp s.g.hom' s.f.hom' = 0 := by
  rw [compIsMonoidComp₂, s.zero]
  rfl

lemma compIsZeroFun (s : CategoryTheory.ShortComplex AddCommGrp) : s.g.hom'.toFun ∘ s.f.hom'.toFun = 0 := by
  have : s.g.hom'.toFun ∘ s.f.hom'.toFun = (AddMonoidHom.comp s.g.hom' s.f.hom').toFun := rfl
  rw [this, compIsZero]
  rfl


structure AddCommGroupSES extends CategoryTheory.ShortComplex AddCommGrp where
  injective : f.hom'.toFun.Injective
  middle : AddMonoidHom.ker g.hom' ≤ AddMonoidHom.range f.hom'
  surjective : g.hom'.toFun.Surjective


lemma rangeEqKerToCompEqZero (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) : g.comp f = 0 := by
  ext x
  simp
  have : f x ∈ f.range := by use x
  rw [range_eq_ker] at this
  apply this

def GroupsToComp₂ (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) : CategoryTheory.ShortComplex AddCommGrp := GroupsToComplex (rangeEqKerToCompEqZero range_eq_ker)

def GroupsToSES (finj : f.toFun.Injective) (range_eq_ker : AddMonoidHom.range f = AddMonoidHom.ker g) (gsurj : g.toFun.Surjective) : AddCommGroupSES where
  __ := GroupsToComp₂ range_eq_ker
  injective := finj
  middle := le_of_eq range_eq_ker.symm
  surjective := gsurj


lemma RangeInKernel (s : AddCommGroupSES) : AddMonoidHom.range s.f.hom' ≤ AddMonoidHom.ker s.g.hom' := by
  rintro x hx
  rcases hx with ⟨w, hw⟩
  have : s.g.hom' (s.f.hom' w) = 0 := by
    apply congrFun (compIsZeroFun s.toShortComplex) w

  rw [hw] at this
  exact this

lemma RangeIsKernel {s : AddCommGroupSES} : s.f.hom'.range = s.g.hom'.ker := le_antisymm (RangeInKernel s) (s.middle)

end Complexes

section Products

variable {I : Type*} {ι₁ ι₂ : I → Type*} [∀ i, AddCommGroup (ι₁ i)] [∀ i, AddCommGroup (ι₂ i)]

def productMap (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) : (∀ i, ι₁ i) →+ (∀ i, ι₂ i) where
  toFun := by
    intro x i
    apply (maps i).toFun (x i)
  map_zero' := by
    simp
    rfl
  map_add' := by
    intro x y
    ext i
    simp

variable {ι₃ : I → Type*} [∀ i, AddCommGroup (ι₃ i)]

@[simp]
lemma ProductMapCompatible (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : (productMap maps₂).comp (productMap maps) = productMap (fun i ↦ (maps₂ i).comp (maps i)) := by
  ext x i
  unfold productMap
  simp

@[simp]
lemma ProductMapCompatibleFun (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ((productMap maps₂).comp (productMap maps)).toFun = (productMap (fun i ↦ (maps₂ i).comp (maps i))).toFun := by
  ext x i
  unfold productMap
  simp

@[simp]
lemma ProductMapCompatibleElt (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ∀ x, (productMap maps₂).comp (productMap maps) x = productMap (fun i ↦ (maps₂ i).comp (maps i)) x := by
  intro x
  apply congrFun (ProductMapCompatibleFun maps maps₂) x

@[simp]
lemma ProductMapCompatibleEltInd (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) (maps₂ : ∀ i, (ι₂ i) →+ (ι₃ i)) : ∀ x, ∀ i, (productMap maps₂).comp (productMap maps) x i = productMap (fun i ↦ (maps₂ i).comp (maps i)) x i := by
  intro x i
  apply congrFun (ProductMapCompatibleElt maps maps₂ x) i


lemma ProductMapKer (maps : ∀ i, (ι₁ i) →+ (ι₂ i)) : ∀ x, x ∈ (productMap maps).ker ↔ ∀ i, x i ∈ (maps i).ker := by
  intro x
  constructor
  · intro hx i
    unfold productMap at hx
    simp at hx
    apply congrFun hx i
  · intro hi
    ext i
    apply hi i

lemma ProductMapRange {maps : ∀ i, (ι₁ i) →+ (ι₂ i)} : ∀ x, x ∈ (productMap maps).range ↔ ∀ i, x i ∈ (maps i).range := by
  intro x
  constructor
  · intro this
    intro i
    unfold productMap at this
    simp at this
    rcases this with ⟨w,hw⟩
    use w i
    exact congrFun hw i
  · intro this
    have h : ∀ i, ∃ w, (maps i) w = x i:= by
      intro i
      apply this i

    use (fun i ↦ (h i).choose)
    ext i

    have : ∀ y, (productMap fun i ↦ maps i) y i = (maps i) (y i) := by
      intro y
      unfold productMap
      simp

    rw [this, Exists.choose_spec (h i)]


variable {I : Type*} (ι : ∀ (_ : I), AddCommGroupSES)

def productOfSESisSES : AddCommGroupSES where
  X₁ := AddCommGrp.of (∀ i, (ι i).X₁)
  X₂ := AddCommGrp.of (∀ i, (ι i).X₂)
  X₃ := AddCommGrp.of (∀ i, (ι i).X₃)
  f := by
    have : (∀ i, (ι i).X₁) →+ (∀ i, (ι i).X₂) := by
      apply productMap (fun i ↦ (ι i).f.hom')
    use this
    intro x y
    simp
  g := by
    have : (∀ i, (ι i).X₂) →+ (∀ i, (ι i).X₃) := by
      apply productMap (fun i ↦ (ι i).g.hom')
    use this
    intro x y
    simp
  zero := by
    simp
    rfl
  injective := by
    intro x y eq
    simp at eq
    ext i
    apply (ι i).injective
    simp
    apply congrFun eq
  middle := by
    simp
    intro x hx
    rw [ProductMapKer] at hx
    have : ∀ i, x i ∈ (ι i).f.hom'.range := by
      intro i
      rw [RangeIsKernel]
      exact hx i

    exact (ProductMapRange x).mpr this
  surjective := by
    simp
    intro x
    have : ∀ i, x i ∈ (ι i).g.hom'.range := by
      intro i
      apply (ι i).surjective

    exact (ProductMapRange x).mpr this
