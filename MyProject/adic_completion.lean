import Mathlib.RingTheory.AdicCompletion.Algebra

variable {A : Type*} [CommRing A] (I : Ideal A)

/--
  I adic completion of J = I.adicCompletion J.  Extension of J into I-adic completion via induced algebra map.
-/
def Ideal.adicCompletion (J : Ideal A): Ideal (AdicCompletion I A) := Ideal.map (algebraMap A (AdicCompletion I A)) J


noncomputable def toFunAdicCompletion : AdicCompletion I ↥I → ↥(I.adicCompletion I) := sorry

noncomputable def adicCompletionsAreSame : AdicCompletion I I ≃ₗ[AdicCompletion I A] I.adicCompletion I where
  toFun := toFunAdicCompletion I
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. Then the natural map `M → AdicComplation I M` is
  injective if and only iff `M` is Hausdorff w.r.t `I`.
  .
-/
lemma IsHausdorff_iff_Injective {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] :
    IsHausdorff I M ↔ Function.Injective (AdicCompletion.of I M) :=  by
  rw [isHausdorff_iff]
  rw [injective_iff_map_eq_zero (AdicCompletion.of I M)]
  apply forall_congr'
  intro a
  rw [AdicCompletion.ext_iff]
  rfl

/--
  Let `φₙ : M/I^nM → M` be the map that uses AC to send `⟦x⟧ₙ` to some `x`.
  Let `qₘ : M/I^nM → M` be the quotient map that sends `x` to `⟦x⟧ₘ`.
  Let `tₘₙ : M/IⁿM → M/IᵐM` be the transition map sends `⟦x⟧ₙ` to `⟦x⟧ₘ`.
  Then `qₘ ∘ φₙ = tₘₙ`.

  This can probably be generalized.
-/
lemma quotient_out_eq_transition_map {A : Type u} [CommRing A] {I : Ideal A} {M: Type u} [AddCommGroup M] [Module A M] {m n : ℕ} (m_le_n : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule A M)) :
    Submodule.Quotient.mk x.out = AdicCompletion.transitionMap I M m_le_n x := by
  calc
    Submodule.Quotient.mk x.out = AdicCompletion.transitionMap I M m_le_n (Submodule.Quotient.mk x.out) := by simp
    _ = AdicCompletion.transitionMap I M m_le_n ⟦ x.out ⟧ := rfl
    _ = AdicCompletion.transitionMap I M m_le_n x := by rw [Quotient.out_eq]


/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. If `M` is Precomple w.r.t `I`, then the
  natural map `M → AdicComplation I M` is surjective.
-/
lemma Surjective_ofIsPrecomplete {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [M_pc : IsPrecomplete I M] :
    Function.Surjective (AdicCompletion.of I M) := by
  intro ⟨f, h⟩
  set g : ℕ → M := fun n ↦ (f n).out
  have : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
    intro m n hmn
    show _ = _
    rw [quotient_out_eq_transition_map hmn (f n)]
    rw [h hmn]
    exact Quotient.out_eq _
  rcases M_pc.prec' g this with ⟨m, hm⟩
  use m
  ext n
  simp
  rw [←Quotient.out_eq (f n), ←(hm n)]
  rfl

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. If the natural map `M → AdicComplation I M` is
  surjective, then `M` is Precomple w.r.t `I`.
-/
lemma IsPrecomplete_of_Surjective {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] (hs : Function.Surjective (AdicCompletion.of I M)) :
    IsPrecomplete I M := by
  rw [isPrecomplete_iff]
  intro f hf
  set y : AdicCompletion I M := ⟨fun n ↦ ⟦f n⟧, fun hmn ↦ (hf hmn).symm⟩
  rcases hs y with ⟨x, hx⟩
  use x
  intro n
  exact (AdicCompletion.ext_iff.mp hx n).symm

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. Then `M` is `I`-adic complete if and only if the
  natural map `M → AdicComplation I M` is a bijection.
-/
lemma IsAdicComplete_iff_Bijective {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] :
    IsAdicComplete I M ↔ Function.Bijective (AdicCompletion.of I M) := by
  constructor
  · intro h
    exact ⟨(IsHausdorff_iff_Injective I M).mp ⟨h.haus'⟩, Surjective_ofIsPrecomplete I M⟩
  · intro ⟨inj, surj⟩
    exact @IsAdicComplete.mk A _ I M _ _ ((IsHausdorff_iff_Injective I M).mpr inj) ((IsPrecomplete_of_Surjective I M) surj)

instance {A : Type u} [CommRing A] {I : Ideal A}: IsAdicComplete (I.adicCompletion I) (AdicCompletion I A) := sorry
