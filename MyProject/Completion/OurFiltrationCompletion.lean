import MyProject.Completion.NaiveInverseLimit
import MyProject.Filtration.OurFiltration
import Mathlib.RingTheory.AdicCompletion.Algebra

section

variable {G : Type u} [AddCommGroup G] (F : OurFiltration G)

def OurFiltrationIS : ℕ → Type _ := fun n ↦ G ⧸ (F.N n)

instance (i : ℕ) : AddCommGroup (OurFiltrationIS F i) := by
  unfold OurFiltrationIS
  infer_instance

def OFISTransitionMap :
    ∀ ⦃n m⦄, n ≤ m → OurFiltrationIS F m →+ OurFiltrationIS F n :=
  fun n m h ↦
    QuotientAddGroup.map (F.N m) (F.N n) (AddMonoidHom.id G) (OurFiltration_antitone F h)

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

lemma OurFiltrationCompletion.of_apply (x : G) (n : ℕ) :
  (OurFiltrationCompletion.of F x).1 n = ⟦x⟧ := rfl

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

variable {G₁ G₂ G₃ : Type*} [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
variable (F₁ : OurFiltration G₁) (F₂ : OurFiltration G₂) (F₃ : OurFiltration G₃)
variable (φ : G₁ →+ G₂) (ψ : G₂ →+ G₃)
variable (hφ : ∀ n, (F₁.N n) ≤ (F₂.N n).comap φ) (hψ : ∀ n, (F₂.N n) ≤ (F₃.N n).comap ψ)

def OFISystemHom.of_comap_le :
    AddInverseSystemHom (OFISTransitionMap F₁) (OFISTransitionMap F₂) where
  maps := fun n ↦ (QuotientAddGroup.map _ _ φ (hφ n))
  compatible := by
    rintro _ _ _ ⟨x⟩
    rfl

def OurFiltrationCompletionHom.of_comap_le :
    OurFiltrationCompletion F₁ →+ OurFiltrationCompletion F₂ :=
  InducedNaiveInverseLimitHom (OFISystemHom.of_comap_le F₁ F₂ φ hφ)

lemma OurFiltrationCompletionHom.of_comap_le_apply (x : OurFiltrationCompletion F₁) (n : ℕ) :
    (OurFiltrationCompletionHom.of_comap_le F₁ F₂ φ hφ x).1 n =
      QuotientAddGroup.map _ _ φ (hφ n) (x.1 n) :=
  rfl

lemma OurFiltrationCompletionHom.of_comap_le_comp_eq :
  OurFiltrationCompletionHom.of_comap_le F₁ F₃ (ψ.comp φ) (fun n _ a ↦ hψ n (hφ n a)) =
    (OurFiltrationCompletionHom.of_comap_le F₂ F₃ ψ hψ).comp
      (OurFiltrationCompletionHom.of_comap_le F₁ F₂ φ hφ) := by
  ext x n
  simp
  repeat rw [OurFiltrationCompletionHom.of_comap_le_apply]
  rw [QuotientAddGroup.map_map]

lemma OurFiltrationCompletionHom.comm :
  (OurFiltrationCompletion.of F₂).comp φ =
    (OurFiltrationCompletionHom.of_comap_le F₁ F₂ φ hφ).comp (OurFiltrationCompletion.of F₁) := rfl

end
