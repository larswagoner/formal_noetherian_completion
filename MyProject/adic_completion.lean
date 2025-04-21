import Mathlib.RingTheory.AdicCompletion.Algebra

variable {A : Type*} [CommRing A] (I : Ideal A)

/--
  I adic completion of J = I.adicCompletion J.  Extension of J into I-adic completion via induced algebra map.
-/
def Ideal.adicCompletion (J : Ideal A): Ideal (AdicCompletion I A) := Ideal.map (algebraMap A (AdicCompletion I A)) J

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. If `M` is Hausdorff w.r.t `I`, then the
  natural map `M → AdicComplation I M` is injective.
-/
lemma adicCompletionInjective_ofHausdorff {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [M_h : IsHausdorff I M] :
    Function.Injective (AdicCompletion.of I M) := by
  apply (injective_iff_map_eq_zero (AdicCompletion.of I M)).mpr
  intro a h₁
  apply M_h.haus'
  intro n
  have h₂ := h₁ ▸ AdicCompletion.of_apply I M a n
  refine SModEq.zero.mpr ?_
  exact (Submodule.Quotient.mk_eq_zero (I ^ n • ⊤)).mp h₂.symm

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
lemma adicCompletionSurjective_ofPrecomplete {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [M_pc : IsPrecomplete I M] :
    Function.Surjective (AdicCompletion.of I M) := by
  intro ⟨f, h⟩
  set g : ℕ → M := fun n ↦ (f n).out
  have : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
    intro m n m_le_n
    show _ = _
    rw [quotient_out_eq_transition_map m_le_n (f n), h m_le_n]
    exact Quotient.out_eq _
  rcases M_pc.prec' g this with ⟨m, hm⟩
  use m
  ext n
  simp
  rw [←Quotient.out_eq (f n), ←(hm n)]
  rfl

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. If `M` is `I`-adic complete, then the
  natural map `M → AdicComplation I M` is a bijection.
-/
lemma adicCompletionBijective_ofIsAdicComplete {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [M_ac : IsAdicComplete I M] :
    Function.Bijective (AdicCompletion.of I M) :=
  ⟨adicCompletionInjective_ofHausdorff I M, adicCompletionSurjective_ofPrecomplete I M⟩

/-
  Adic Complete
-/
class IsReallyAdicComplete {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] where
  map_iso : Function.Bijective (AdicCompletion.of I M)

instance {A : Type u} [CommRing A] (I : Ideal A) (M: Type u) [AddCommGroup M] [Module A M] [IsAdicComplete I M] : IsReallyAdicComplete I M where
  map_iso := adicCompletionBijective_ofIsAdicComplete I M

instance {A : Type u} [CommRing A] {I : Ideal A}: IsAdicComplete (I.adicCompletion I) (AdicCompletion I A) :=  sorry
