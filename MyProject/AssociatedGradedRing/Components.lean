import MyProject.AssociatedGradedRing.Ring
import Mathlib.Algebra.Module.Torsion


variable {A : Type u} [CommRing A] (I : Ideal A)

-- goal prove that I^m/I^m+1 ≃+ GRP I m, maybe treat case of m=0 differently since ring structure

open QuotientAddGroup

/-- `A/I` is isomorphic to `GradedRingPiece I 0` as rings-/
def zero_toFun_aux₁ : A →+ (CanonicalFiltration I).N 0 where
  toFun := (fun a => ⟨ a , by simp ⟩)
  map_zero' := rfl
  map_add' := fun _ _ => rfl


def zero_toFun : A ⧸ I →+* (GradedRingPiece I 0) where
  __ := map _ _ (zero_toFun_aux₁ I) fun _ _ ↦ by simpa
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩ 
    rfl

def zero_invFun_aux₁ : (CanonicalFiltration I).N 0 →+ A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

def zero_invFun : (GradedRingPiece I 0) →+* A ⧸ I where
  __ := map _ _ (zero_invFun_aux₁ I) fun _ h ↦ by simpa using h
  map_one' := rfl
  map_mul' := by
    rintro ⟨_⟩ ⟨_⟩
    rfl

def GradedRingPiece_zero_isomorphism (I : Ideal A): A ⧸ I ≃+* (GradedRingPiece I 0) where
  __ := zero_toFun I
  invFun := zero_invFun I
  left_inv := by
    rintro ⟨_⟩ 
    rfl
  right_inv := by
    rintro ⟨_⟩ 
    rfl



/-- `Iᵐ/Iᵐ⁺¹` is isomorphic to `GradedRingPiece I m` as modules -/
def Taux (m : ℕ): ↥(I^m) →+ (CanonicalFiltration I).N m where
  toFun x := ⟨x, by simp⟩
  map_zero' := by simp
  map_add' := by simp

def mToFun (I : Ideal A) (m : ℕ) : ↥(I^m) ⧸ I • (⊤ : Submodule A ↥(I^m)) →+ GradedRingPiece I m :=
  QuotientAddGroup.map _ _ (Taux I m) fun ⟨x, _⟩ p ↦ by 
    simpa [Submodule.mem_smul_top_iff I, ← pow_succ'] using p
  

def Iaux (m : ℕ) : (CanonicalFiltration I).N m →+ ↥(I^m) where
  toFun x := ⟨x, by simpa using x.2⟩ 
  map_zero' := by simp
  map_add' := by simp

def mInvFun (I : Ideal A) (m : ℕ) : GradedRingPiece I m →+ ↥(I^m) ⧸ I • (⊤ : Submodule A ↥(I^m)) := 
  QuotientAddGroup.map _ _ (Iaux I m) fun a ha ↦ by 
    simpa [Submodule.mem_smul_top_iff I, ← pow_succ'] using ha

def GradedRingPiece_m_iso (I : Ideal A) (m : ℕ) : 
    ↥(I^m) ⧸ I • (⊤ : Submodule A ↥(I^m)) ≃+ (GradedRingPiece I m) where
  __ := mToFun I m
  invFun := mInvFun I m
  left_inv := (·.inductionOn fun _ ↦ rfl)
  right_inv x := x.inductionOn fun _ ↦ rfl


lemma GradedRingPiece_m_iso.bijective (I : Ideal A) (m : ℕ) : 
    Function.Bijective (GradedRingPiece_m_iso I m) := AddEquiv.bijective (GradedRingPiece_m_iso I m)



/-- Module structures -/
-- define from A first, then take quotient
--def smul_aux₁ : A → ↥(I / I ^ 2) → ↥(I / I ^ 2)

instance : Module A I := by infer_instance
instance : Module A (I/I^2) := by infer_instance
instance : Module (GradedRingPiece I 0) (GradedRingPiece I 1) := by infer_instance


instance : Module (A ⧸ I) (I ⧸ I • (⊤ : Submodule A I)):=  Module.instQuotientIdealSubmoduleHSMulTop ↥I I

