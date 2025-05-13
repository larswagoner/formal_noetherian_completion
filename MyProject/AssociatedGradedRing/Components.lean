import MyProject.AssociatedGradedRing.Ring
import Mathlib.Algebra.Module.Torsion


variable {A : Type u} [CommRing A] (I : Ideal A)

-- goal prove that I^m/I^m+1 ≃+ GRP I m, maybe treat case of m=0 differently since ring structure

/-- `A/I` is isomorphic to `GradedRingPiece I 0` as rings-/
def zero_toFun_aux₁ : A →+ (CanonicalFiltration I).N 0 where
  toFun := (fun a => ⟨ a , by simp ⟩)
  map_zero' := rfl
  map_add' := fun _ _ => rfl


def zero_toFun_aux₂ : A ⧸ I →+ (GradedRingPiece I 0) := by
  apply QuotientAddGroup.map _ _ (zero_toFun_aux₁ I) _
  · intro x hx
    simp
    exact hx

def zero_toFun : A ⧸ I →+* (GradedRingPiece I 0) where
  __ := zero_toFun_aux₂ I
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩ 
    rfl

def zero_invFun_aux₁: (CanonicalFiltration I).N 0 →+ A where
  toFun := (fun ⟨a, _⟩ => a)
  map_zero' := rfl
  map_add' := fun _ _ => rfl

def zero_invFun_aux₂: GradedRingPiece I 0 →+ A ⧸ I := by
  apply QuotientAddGroup.map _ _ (zero_invFun_aux₁ I) _
  intro x hx
  simp at hx
  exact hx

def zero_invFun : (GradedRingPiece I 0) →+* A ⧸ I where
  __ := zero_invFun_aux₂ I
  map_one' := rfl
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨ y, hy⟩ 
    simp
    rfl

def GradedRingPiece_zero_isomorphism (I : Ideal A): A ⧸ I ≃+* (GradedRingPiece I 0) where
  __ := zero_toFun I
  invFun := zero_invFun I
  left_inv := by 
    simp
    unfold Function.LeftInverse
    rintro ⟨x⟩ 
    rfl
  right_inv := by
    simp
    unfold Function.RightInverse Function.LeftInverse
    rintro ⟨x , hx⟩
    simp
    rfl

/-- `I/I²` is isomorphic to `GradedRingPiece 1`-/  
def one_toFun_aux₁: ↥(I) →+ (CanonicalFiltration I).N 1 where
  toFun := fun a => ⟨a, by simp⟩
  map_zero' := by simp 
  map_add' := by simp


def one_toFun (I : Ideal A) : I/I^2 →+ GradedRingPiece I 1 where
  toFun := sorry
  map_zero' := sorry
  map_add' := sorry
  

def one_invFun_aux₁:(CanonicalFiltration I).N 1 →+ I:= sorry


def one_invFun (I : Ideal A): GradedRingPiece I 1 →+ I/I^2 := sorry

def GradedRingPiece_one_isomorphism (I : Ideal A): I/I^2 ≃+ (GradedRingPiece I 1) where
  __ := one_toFun I 
  invFun := one_invFun I
  left_inv := sorry
  right_inv := sorry


/-- `Iᵐ/Iᵐ⁺¹` is isomorphic to `GradedRingPiece I m` as modules -/
def m_toFun_aux₁: ↥(I^m) →+ (CanonicalFiltration I).N m where
  toFun := by -- do this without rewrite!
    rintro ⟨x, hx⟩
    rw [Ideal.stableFiltration_N, smul_eq_mul, Ideal.mul_top]
    exact ⟨x, hx⟩   
  map_zero' := sorry
  map_add' := sorry

def m_toFun (I : Ideal A) (m : ℕ) : I^m/I^(m+1) →+ GradedRingPiece I m := sorry

def m_invFun_aux₁:(CanonicalFiltration I).N m →+ ↥(I^m):= sorry

def m_invFun (I : Ideal A) (m : ℕ): GradedRingPiece I m →+ I^m/I^(m+1) := sorry

def GradedRingPiece_m_isomorphism (I : Ideal A) (m : ℕ) : I^m/I^(m+1) ≃+ (GradedRingPiece I m) where
  __ := m_toFun I m
  invFun := m_invFun I m
  left_inv := sorry
  right_inv := sorry


/-- Module structures -/
-- define from A first, then take quotient
--def smul_aux₁ : A → ↥(I / I ^ 2) → ↥(I / I ^ 2)

instance : Module A I := by infer_instance
instance : Module A (I/I^2) := by infer_instance
instance : Module (GradedRingPiece I 0) (GradedRingPiece I 1) := by infer_instance
instance : Module (GradedRingPiece I 0) (I/I^2) := sorry


instance : Module (A ⧸ I) (I  ⧸  I • (⊤ : Submodule A I) ):=  Module.instQuotientIdealSubmoduleHSMulTop (↥I) I

