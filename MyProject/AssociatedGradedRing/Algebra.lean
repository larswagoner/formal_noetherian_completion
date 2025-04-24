import MyProject.AssociatedGradedRing.Ring

/--
  # Associated Graded Module
  In this file, we prove that the associated graded module `G(M)` of an
  `A`-module `M` is a `G(A)`-module.
-/
def algebraMap_fn₁ {A : Type u} [CommRing A] (I : Ideal A) : A →  (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) := fun a => ⟦(⟨a, by simp⟩)⟧

def algebraMap_fn₁_morphism {A : Type u} [CommRing A] (I : Ideal A) : A →+*(GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) where
  toFun := algebraMap_fn₁ I
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def algebraMap_fn₂ {A : Type u} [CommRing A] (I : Ideal A) :
    (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) → AssociatedGradedRing I := fun a
 => (DirectSum.of _ 0 a )


def algebraMap_fn₂_morphism {A : Type u} [CommRing A] (I : Ideal A) : (GradedPiece (I.stableFiltration (⊤ : Submodule A A)) 0) →+* AssociatedGradedRing I where
  toFun := algebraMap_fn₂ I
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry


def AssociatedGradedRing_algebraMap {A : Type u} [CommRing A] (I : Ideal A) : A →+* AssociatedGradedRing I := (algebraMap_fn₂_morphism I).comp (algebraMap_fn₁_morphism I)


instance {A : Type u} [CommRing A] (I : Ideal A) : Algebra A (AssociatedGradedRing I) where
  smul a x := a • x
  algebraMap := AssociatedGradedRing_algebraMap I
  commutes' := sorry
  smul_def' := sorry
