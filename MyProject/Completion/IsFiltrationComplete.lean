import MyProject.Completion.FiltrationCompletion
import MyProject.Filtration.Constructions

section

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

theorem isFiltrationComplete_iff :
    IsFiltrationComplete F ↔
      IsFiltrationHausdorff F ∧ IsFiltrationPrecomplete F := by
  constructor
  · exact fun h ↦ ⟨h.toIsFiltrationHausdorff, h.toIsFiltrationPrecomplete⟩
  · exact fun ⟨a, b⟩ ↦ { __ := a, __ := b }

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

/--
  Let `M` be a module with filtration `F` and `m : ℕ`. Then `M` is `F`-Hausdorff exactly if `M` is
  `OffsetFiltration F m`-Hausdorff.
-/
lemma Haussdorff_iff_offset_Haussdorf (m : ℕ) :
    IsFiltrationHausdorff F ↔ IsFiltrationHausdorff (OffsetFiltration F m) := by
  rw [isFiltrationHausdorff_iff]
  rw [isFiltrationHausdorff_iff]
  apply forall_congr'
  intro a
  constructor
  · intro h ha
    apply h
    intro n
    convert ha (n + m) using 1
    simp
  · intro h ha
    apply h
    intro n
    exact ha (n - m)

/--
  Let `M` be a module with filtration `F` and `m : ℕ`. Then `M` is `F`-Precomplete exactly if `M` is
  `OffsetFiltration F m`-Precomplete.
-/
lemma Precomplete_iff_offset_Precomplete (m : ℕ) :
    IsFiltrationPrecomplete F ↔ IsFiltrationPrecomplete (OffsetFiltration F m) := by
  rw [isFiltrationPrecomplete_iff]
  rw [isFiltrationPrecomplete_iff]
  constructor
  · intro h f hf
    have : (∀ {i j : ℕ}, i ≤ j → f (i + m) ≡ f (j + m) [SMOD F.N i]) := by
      intro i j hij
      convert hf (add_le_add_right hij m) using 1
      simp
    rcases h (fun n ↦ f (n + m)) this with ⟨L, hL⟩
    use L
    intro i
    by_cases him : i ≤ m
    · rw [offsetFiltration_eval_le F him]
      have h₁ := hf him
      rw [offsetFiltration_eval_le F him] at h₁
      apply trans h₁
      convert hL 0
      simp
    · convert (hL (i - m)) using 1
      push_neg at him
      rw [Nat.sub_add_cancel (le_of_lt him)]
  · intro h f hf
    have : (∀ {i j : ℕ}, i ≤ j → f (i - m) ≡ f (j - m) [SMOD (OffsetFiltration F m).N i]) := by
      intro i j hij
      exact hf (Nat.sub_le_sub_right hij m)
    rcases h (fun n ↦ f (n - m)) this with ⟨L, hL⟩
    use L
    intro i
    convert hL (i + m) using 1
    simp
    rw [Nat.add_sub_cancel]

/--
  Let `M` be a module with filtration `F` and `m : ℕ`. Then `M` is `F`-Complete exactly if `M` is
  `OffsetFiltration F m`-Complete.
-/
lemma Complete_iff_offset_Complete (m : ℕ) :
    IsFiltrationComplete F ↔ IsFiltrationComplete (OffsetFiltration F m) := by
  rw [isFiltrationComplete_iff]
  rw [Haussdorff_iff_offset_Haussdorf F m]
  rw [Precomplete_iff_offset_Precomplete F m]
  rw [isFiltrationComplete_iff]

end

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable (ι : Type*) (β : ι → Type*) [∀ i, AddCommGroup (β i)] [∀ i, Module A (β i)]
variable (F : ∀ i, I.Filtration (β i))

/--
  Let `{Mₙ}` be collection of modules with filtrations `Fᵢ`. Then `∏ᵢ Mᵢ` is `(∏ᵢ Fᵢ)`-Hausdorff,
  exactly if each `Mᵢ` is `Fᵢ`-Hausdorff.
-/
lemma product_Haussdorf_iff_forall_Haussdorff [DecidableEq ι] :
    IsFiltrationHausdorff (DirectProductFiltration ι β F) ↔ ∀ i, IsFiltrationHausdorff (F i) := by
  rw [isFiltrationHausdorff_iff]
  constructor
  · intro hHaus j
    rw [isFiltrationHausdorff_iff]
    intro x hx
    set y : ∀ i, β i := fun i ↦ if hij : i = j then (hij ▸ x) else 0
    by_contra x_ne_0
    have : y ≠ 0 := by
      intro h
      have : y j ≠ 0 := by
        intro h
        unfold y at h
        simp at h
        exact x_ne_0 h
      exact this (congrFun h j)
    apply this
    apply hHaus
    intro n
    rw [DirectProductFiltration_mod_iff]
    intro i
    by_cases hij : i = j
    · subst hij
      unfold y
      simp
      exact hx n
    · push_neg at hij
      unfold y
      simp [hij]
      rfl
  · intro hHaus x hx
    ext i
    have hi := hHaus i
    rw [isFiltrationHausdorff_iff] at hi
    apply hi
    intro n
    have := hx n
    rw [DirectProductFiltration_mod_iff] at this
    exact this i

/--
  Let `{Mₙ}` be collection of modules with filtrations `Fᵢ`. Then `∏ᵢ Mᵢ` is `(∏ᵢ Fᵢ)`-Precomplete,
  exactly if each `Mᵢ` is `Fᵢ`-Precomplete.
-/
lemma product_Precomplete_iff_forall_Precomplete [DecidableEq ι] :
    IsFiltrationPrecomplete (DirectProductFiltration ι β F) ↔ ∀ i, IsFiltrationPrecomplete (F i) := by
  rw [isFiltrationPrecomplete_iff]
  constructor
  · intro hPrec j
    rw [isFiltrationPrecomplete_iff]
    intro f hf
    set g : ℕ → (∀ i, β i) := by
      intro n i
      exact if hij : i = j then (hij ▸ (f n)) else 0
    have : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (DirectProductFiltration ι β F).N m] := by
      intro m n hmn
      rw [DirectProductFiltration_mod_iff]
      intro i
      by_cases hij : i = j
      · subst hij
        unfold g
        simp
        exact hf hmn
      · unfold g
        simp [hij]
        rfl
    rcases hPrec g this with ⟨L, hL⟩
    use (L j)
    intro n
    have := hL n
    rw [DirectProductFiltration_mod_iff] at this
    convert (this j)
    unfold g
    simp
  · intro hPrec f hf
    have : ∀ i : ι, ∃ L : β i, ∀ (n : ℕ), f n i ≡ L [SMOD (F i).N n] := by
      intro i
      set fᵢ : ℕ → (β i) := fun n ↦ f n i
      have : ∀ {m n : ℕ}, m ≤ n → fᵢ m ≡ fᵢ n [SMOD (F i).N m] := by
        intro m n hmn
        have := hf hmn
        rw [DirectProductFiltration_mod_iff] at this
        exact this i
      exact (hPrec i).prec' fᵢ this
    use (fun i ↦ (this i).choose)
    intro n
    rw [DirectProductFiltration_mod_iff]
    intro i
    exact (this i).choose_spec n


/--
  Let `{Mₙ}` be collection of modules with filtrations `Fᵢ`. Then `∏ᵢ Mᵢ` is `(∏ᵢ Fᵢ)`-Complete,
  exactly if each `Mᵢ` is `Fᵢ`-Complete
-/
lemma product_Complete_iff_forall_Complete [DecidableEq ι] :
    IsFiltrationComplete (DirectProductFiltration ι β F) ↔ ∀ i, IsFiltrationComplete (F i) := by
  rw [isFiltrationComplete_iff]
  rw [product_Haussdorf_iff_forall_Haussdorff ι β F]
  rw [product_Precomplete_iff_forall_Precomplete ι β F]
  rw [←forall_and]
  apply forall_congr'
  intro a
  rw [isFiltrationComplete_iff]

end

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M]

lemma isComplete_iff_isCanonicalComplete :
    IsAdicComplete I M ↔ IsFiltrationComplete (I.stableFiltration (⊤ : Submodule A M)) :=
  ⟨fun h ↦ { haus' := h.haus', prec' := h.prec' }, fun h ↦ { haus' := h.haus', prec' := h.prec' }⟩

lemma isHausdorff_iff_isCanonicalHausdorff :
    IsHausdorff I M ↔ IsFiltrationHausdorff (I.stableFiltration (⊤ : Submodule A M)) :=
  ⟨fun h ↦ { haus' := h.haus' }, fun h ↦ { haus' := h.haus' }⟩

lemma isPrecomplete_iff_isCanonicalPrecomplete :
    IsPrecomplete I M ↔ IsFiltrationPrecomplete (I.stableFiltration (⊤ : Submodule A M)) :=
  ⟨fun h ↦ { prec' := h.prec' }, fun h ↦ { prec' := h.prec' }⟩

end
