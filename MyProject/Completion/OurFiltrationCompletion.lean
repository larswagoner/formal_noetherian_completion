import MyProject.Completion.NaiveInverseLimit
import MyProject.Filtration.OurFiltration
import Mathlib.RingTheory.AdicCompletion.Algebra

section

variable {G : Type u} [AddCommGroup G] {σ : Type v} [SetLike σ G] [AddSubgroupClass σ G] (F : OurFiltration G σ)

def OurFiltrationIS : ℕ → Type _ := fun n ↦ G ⧸ (AddSubgroup.ofClass (F.N n))

instance (i : ℕ) : AddCommGroup (OurFiltrationIS F i) := by
  unfold OurFiltrationIS
  infer_instance

def OFISTransitionMap :
    ∀ ⦃n m⦄, n ≤ m → OurFiltrationIS F m →+ OurFiltrationIS F n :=
  fun n m h ↦
    QuotientAddGroup.map (AddSubgroup.ofClass (F.N m)) (AddSubgroup.ofClass (F.N n)) (AddMonoidHom.id G) (by sorry) --OurFiltration_antitone F h)

instance : AddInverseSystem (OFISTransitionMap F) where
  map_self := by
    rintro n ⟨x⟩
    rfl
  map_map := by
    rintro k j i hkj hji ⟨x⟩
    rfl

def OurFiltrationCompletion : Type u :=
  NaiveAddInverseLimit (OFISTransitionMap F)

@[ext]
lemma OurFiltrationCompletion.ext {x y : OurFiltrationCompletion F} (h : ∀ n, x.1 n = y.1 n) : x = y :=
  Subtype.eq (funext h)

instance : AddCommGroup (OurFiltrationCompletion F) :=
  instAddCommGroupElemForallNaiveAddInverseLimit (OFISTransitionMap F)

def OurFiltrationCompletion.of :
    G →+ (OurFiltrationCompletion F) where
  toFun := fun m ↦ ⟨fun _ ↦ ⟦m⟧, fun _ _ _ ↦ rfl⟩
  map_add' := fun _ _ ↦ rfl
  map_zero' := rfl

end

section

variable {A : Type u} [CommRing A] {I : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]
variable (F : I.Filtration M)

lemma AdicCompletion_eq_OurFiltrationCompletion :
  AdicCompletion I M =
    OurFiltrationCompletion (I.stableFiltration (⊤ : Submodule A M)).toOurFiltration := rfl

end

section

variable {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂]
variable {σ₁ σ₂ : Type*} [SetLike σ₁ G₁] [AddSubgroupClass σ₁ G₁] [SetLike σ₂ G₂] [AddSubgroupClass σ₂ G₂]
variable {F₁ : OurFiltration G₁ σ₁} {F₂ : OurFiltration G₂ σ₂} (φ : G₁ →+ G₂)
variable (hφ : ∀ n, (AddSubgroup.ofClass (F₁.N n)) ≤ (AddSubgroup.ofClass (F₂.N n)).comap φ)

def OFISystemHom.of_comap_le :
    AddInverseSystemHom (OFISTransitionMap F₁) (OFISTransitionMap F₂) where
  maps := fun n ↦ (QuotientAddGroup.map _ _ φ (hφ n))
  compatible := by
    rintro _ _ _ ⟨x⟩
    rfl

def OurFiltrationCompletionHom.of_comap_le :
    OurFiltrationCompletion F₁ →+ OurFiltrationCompletion F₂ :=
  InverseLimitHom (OFISystemHom.of_comap_le φ hφ)

def OurFiltrationCompletionHom.comm :
  (OurFiltrationCompletion.of F₂).comp φ =
    (OurFiltrationCompletionHom.of_comap_le φ hφ).comp (OurFiltrationCompletion.of F₁) := rfl

end
