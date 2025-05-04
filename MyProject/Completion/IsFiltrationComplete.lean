import MyProject.Completion.FiltrationCompletion

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M]
variable (F : I.Filtration M)

/-- A module `M` is Hausdorff with respect to a filtration `Mₙ` if `⋂ Mₙ = 0`. -/
class IsFiltrationHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD F.N n]) → x = 0

/-- A module `M` is Precomplete with respect to a filtration `Mₙ` if every Cauchy sequence converges. -/
class IsFiltrationPrecomplete : Prop where
  prec' : ∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD F.N m]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD F.N n]

/-- A module `M` is `Mₙ`-complete if it is Hausdorff and precomplete. -/
class IsFiltrationComplete : Prop extends IsFiltrationHausdorff F, IsFiltrationPrecomplete F

section

variable {F}

theorem IsFiltrationHausdorff.haus (_ : IsFiltrationHausdorff F) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD F.N n]) → x = 0 :=
  IsFiltrationHausdorff.haus'

theorem isFiltrationHausdorff_iff :
    IsFiltrationHausdorff F ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD F.N n]) → x = 0 :=
  ⟨IsFiltrationHausdorff.haus, fun h => ⟨h⟩⟩

theorem IsFiltrationPrecomplete.prec (_ : IsFiltrationPrecomplete F) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD F.N m]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD F.N n] :=
  IsFiltrationPrecomplete.prec' _

theorem isFiltrationPrecomplete_iff :
    IsFiltrationPrecomplete F ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD F.N m]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD F.N n] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

end

/--
  Let `M` be an `F`-filtered module. Then the natural map `M → FiltrationCompletion F` is
  injective if and only if `M` is `F`-Hausdorff.
-/
lemma IsFiltrationHausdorff_iff_Injective :
    IsFiltrationHausdorff F ↔ Function.Injective (FiltrationCompletion.of F) :=  by
  rw [isFiltrationHausdorff_iff]
  rw [injective_iff_map_eq_zero (FiltrationCompletion.of F)]
  apply forall_congr'
  intro a
  rw [←FiltrationCompletion.ext_iff]
  rfl

/--
  Let `φₙ : M/I^nM → M` be the map that uses AC to send `⟦x⟧ₙ` to some `x`.
  Let `qₘ : M/I^nM → M` be the quotient map that sends `x` to `⟦x⟧ₘ`.
  Let `tₘₙ : M/IⁿM → M/IᵐM` be the transition map sends `⟦x⟧ₙ` to `⟦x⟧ₘ`.
  Then `qₘ ∘ φₙ = tₘₙ`.

  This can probably be generalized.
-/
lemma quotient_out_eq_transition_map {m n : ℕ} (m_le_n : m ≤ n) (x : M ⧸ F.N n) :
    Submodule.Quotient.mk x.out = FISTransitionMap F m_le_n x := by
  calc
    Submodule.Quotient.mk x.out = FISTransitionMap F m_le_n (Submodule.Quotient.mk x.out) := rfl
    _ = FISTransitionMap F m_le_n ⟦ x.out ⟧ := rfl
    _ = FISTransitionMap F m_le_n x := by rw [Quotient.out_eq]



/--
  Let `M` be an `F`-filtered module. If `M` is `F`-Precomplete, then the natural map
  `M → FiltrationCompletion F` is surjective.
-/
lemma Surjective_ofIsFiltrationPrecomplete [M_pc : IsFiltrationPrecomplete F] :
    Function.Surjective (FiltrationCompletion.of F) := by
  intro ⟨f, h⟩
  set g : ℕ → M := fun n ↦ (f n).out
  have : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD F.N m] := by
    intro m n hmn
    show _ = _
    rw [quotient_out_eq_transition_map F hmn (f n)]
    rw [h hmn]
    exact Quotient.out_eq _
  rcases M_pc.prec' g this with ⟨m, hm⟩
  use m
  ext n
  simp
  rw [←Quotient.out_eq (f n)]
  have : ⟦g n⟧ = ⟦m⟧ := hm n
  rw [this]
  rfl

/--
  Let `M` be an `F`-filtered module. If the natural map `M → FiltrationCompletion F` is
  surjective, then `M` is `F`-Precomplete.
-/
lemma IsFiltrationPrecomplete_of_Surjective (hs : Function.Surjective (FiltrationCompletion.of F)) :
    IsFiltrationPrecomplete F := by
  rw [isFiltrationPrecomplete_iff]
  intro f hf
  set y : FiltrationCompletion F := ⟨fun n ↦ ⟦f n⟧, fun m n hmn ↦ (hf hmn).symm⟩
  rcases hs y with ⟨x, hx⟩
  use x
  intro n
  exact ((FiltrationCompletion.ext_iff F).mpr hx n).symm

/--
  Let `M` be an `A`-module and `I ⊆ A` an ideal. Then `M` is `I`-adic complete if and only if the
  natural map `M → AdicComplation I M` is a bijection.
-/
lemma IsFiltrationComplete_iff_Bijective :
    IsFiltrationComplete F ↔ Function.Bijective (FiltrationCompletion.of F) := by
  constructor
  · intro h
    exact ⟨
      (IsFiltrationHausdorff_iff_Injective F).mp ⟨h.haus'⟩,
      Surjective_ofIsFiltrationPrecomplete F
    ⟩
  · intro ⟨inj, surj⟩
    exact {
      __ := (IsFiltrationHausdorff_iff_Injective F).mpr inj
      __ := (IsFiltrationPrecomplete_of_Surjective F) surj
    }
