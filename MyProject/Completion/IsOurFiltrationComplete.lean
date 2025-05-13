import MyProject.Completion.OurFiltrationCompletion
import MyProject.Filtration.FConstructions

section

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)

/-- A predicate saying two elements of a group are equivalent modulo a subgroup. -/
def GModEq (x y : G)  : Prop :=
  (QuotientAddGroup.mk x : G ⧸ H) = (QuotientAddGroup.mk y)

@[inherit_doc] notation:50 x " ≡ " y " [GMOD " H "]" => GModEq H x y

section

variable {G : Type*} [AddCommGroup G] (F : OurFiltration G)

/-- A group `G` is Hausdorff with respect to a filtration `Gₙ` if `⋂ Gₙ = 0`. -/
class IsOurFiltrationHausdorff : Prop where
  haus' : ∀ x : G, (∀ n : ℕ, x ≡ 0 [GMOD F.N n]) → x = 0

/-- A group `G` is Precomplete with respect to a filtration `Gₙ` if every Cauchy sequence converges. -/
class IsOurFiltrationPrecomplete : Prop where
  prec' : ∀ f : ℕ → G, (∀ {m n}, m ≤ n → f m ≡ f n [GMOD F.N m]) →
    ∃ L : G, ∀ n, f n ≡ L [GMOD F.N n]

/-- A module `G` is `Gₙ`-complete if it is Hausdorff and precomplete. -/
class IsOurFiltrationComplete : Prop extends IsOurFiltrationHausdorff F, IsOurFiltrationPrecomplete F

section

variable {F}

theorem IsOurFiltrationHausdorff.haus (_ : IsOurFiltrationHausdorff F) :
    ∀ x : G, (∀ n : ℕ, x ≡ 0 [GMOD F.N n]) → x = 0 :=
  IsOurFiltrationHausdorff.haus'

theorem isOurFiltrationHausdorff_iff :
    IsOurFiltrationHausdorff F ↔ ∀ x : G, (∀ n : ℕ, x ≡ 0 [GMOD F.N n]) → x = 0 :=
  ⟨IsOurFiltrationHausdorff.haus, fun h => ⟨h⟩⟩

theorem IsOurFiltrationPrecomplete.prec (_ : IsOurFiltrationPrecomplete F) {f : ℕ → G} :
    (∀ {m n}, m ≤ n → f m ≡ f n [GMOD F.N m]) →
      ∃ L : G, ∀ n, f n ≡ L [GMOD F.N n] :=
  IsOurFiltrationPrecomplete.prec' _

theorem isOurFiltrationPrecomplete_iff :
    IsOurFiltrationPrecomplete F ↔
      ∀ f : ℕ → G,
        (∀ {m n}, m ≤ n → f m ≡ f n [GMOD F.N m]) →
          ∃ L : G, ∀ n, f n ≡ L [GMOD F.N n] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem isOurFiltrationComplete_iff :
    IsOurFiltrationComplete F ↔
      IsOurFiltrationHausdorff F ∧ IsOurFiltrationPrecomplete F := by
  constructor
  · exact fun h ↦ ⟨h.toIsOurFiltrationHausdorff, h.toIsOurFiltrationPrecomplete⟩
  · exact fun ⟨a, b⟩ ↦ { __ := a, __ := b }

end

/--
  Let `G` be an `F`-filtered group. Then the natural map `G → OurFiltrationCompletion F` is
  injective if and only if `G` is `F`-Hausdorff.
-/
lemma IsOurFiltrationHausdorff_iff_Injective :
    IsOurFiltrationHausdorff F ↔ Function.Injective (OurFiltrationCompletion.of F) :=  by
  rw [isOurFiltrationHausdorff_iff]
  rw [injective_iff_map_eq_zero (OurFiltrationCompletion.of F)]
  apply forall_congr'
  intro a
  rw [OurFiltrationCompletion.ext_iff]
  rfl


/--
  Let `φₙ : G/IⁿG → G` be the map that uses AC to send `⟦x⟧ₙ` to some `x`.
  Let `qₘ : G → G/IᵐG` be the quotient map that sends `x` to `⟦x⟧ₘ`.
  Let `tₘₙ : G/IⁿG → G/IᵐG` be the transition map sends `⟦x⟧ₙ` to `⟦x⟧ₘ`.
  Then `qₘ ∘ φₙ = tₘₙ`.

  This can probably be generalized.
-/
lemma quotient_out_eq_our_transition_map {m n : ℕ} (m_le_n : m ≤ n) (x : G ⧸ F.N n) :
    QuotientAddGroup.mk x.out = OFISTransitionMap F m_le_n x := by
  calc
    QuotientAddGroup.mk x.out = OFISTransitionMap F m_le_n (QuotientAddGroup.mk x.out) := rfl
    _ = OFISTransitionMap F m_le_n ⟦ x.out ⟧ := rfl
    _ = OFISTransitionMap F m_le_n x := by rw [Quotient.out_eq]



/--
  Let `G` be an `F`-filtered group. If `G` is `F`-Precomplete, then the natural map
  `G → OurFiltrationCompletion G` is surjective.
-/
lemma Surjective_ofIsOurFiltrationPrecomplete [G_pc : IsOurFiltrationPrecomplete F] :
    Function.Surjective (OurFiltrationCompletion.of F) := by
  intro ⟨f, h⟩
  set g : ℕ → G := fun n ↦ (f n).out
  have : ∀ {m n}, m ≤ n → g m ≡ g n [GMOD F.N m] := by
    intro m n hmn
    show _ = _
    rw [quotient_out_eq_our_transition_map F hmn (f n)]
    rw [h hmn]
    exact Quotient.out_eq _
  rcases G_pc.prec' g this with ⟨m, hm⟩
  use m
  ext n
  simp
  rw [←Quotient.out_eq (f n)]
  have : ⟦g n⟧ = ⟦m⟧ := hm n
  rw [this]
  rfl

/--
  Let `G` be an `F`-filtered group. If the natural map `G → OurFiltrationCompletion F` is
  surjective, then `G` is `F`-Precomplete.
-/
lemma IsOurFiltrationPrecomplete_of_Surjective (hs : Function.Surjective (OurFiltrationCompletion.of F)) :
    IsOurFiltrationPrecomplete F := by
  rw [isOurFiltrationPrecomplete_iff]
  intro f hf
  set y : OurFiltrationCompletion F := ⟨fun n ↦ ⟦f n⟧, fun m n hmn ↦ (hf hmn).symm⟩
  rcases hs y with ⟨x, hx⟩
  use x
  intro n
  exact ((OurFiltrationCompletion.ext_iff).mp hx n).symm

/--
  Let `G` be an `F`-filtered group. Then `G` is `F`-complete if and only if the
  natural map `G → OurFiltrationCompletion F` is a bijection.
-/
lemma IsOurFiltrationComplete_iff_Bijective :
    IsOurFiltrationComplete F ↔ Function.Bijective (OurFiltrationCompletion.of F) := by
  constructor
  · intro h
    exact ⟨
      (IsOurFiltrationHausdorff_iff_Injective F).mp ⟨h.haus'⟩,
      Surjective_ofIsOurFiltrationPrecomplete F
    ⟩
  · intro ⟨inj, surj⟩
    exact {
      __ := (IsOurFiltrationHausdorff_iff_Injective F).mpr inj
      __ := (IsOurFiltrationPrecomplete_of_Surjective F) surj
    }

section

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M]

lemma isComplete_iff_isCanonicalOurComplete :
    IsAdicComplete I M ↔ IsOurFiltrationComplete (I.stableFiltration (⊤ : Submodule A M)).toOurFiltration :=
  ⟨fun h ↦ { haus' := h.haus', prec' := h.prec' }, fun h ↦ { haus' := h.haus', prec' := h.prec' }⟩

lemma isHausdorff_iff_isCanonicalOurHausdorff :
    IsHausdorff I M ↔ IsOurFiltrationHausdorff (I.stableFiltration (⊤ : Submodule A M)).toOurFiltration :=
  ⟨fun h ↦ { haus' := h.haus' }, fun h ↦ { haus' := h.haus' }⟩

lemma isPrecomplete_iff_isCanonicalOurPrecomplete :
    IsPrecomplete I M ↔ IsOurFiltrationPrecomplete (I.stableFiltration (⊤ : Submodule A M)).toOurFiltration :=
  ⟨fun h ↦ { prec' := h.prec' }, fun h ↦ { prec' := h.prec' }⟩

end
