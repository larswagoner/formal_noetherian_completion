import MyProject.AssociatedGradedRing.Ring


variable {A : Type u} [CommRing A] (I : Ideal A)


#check (CanonicalFiltration I).N 0

def aux1 : A →+ (CanonicalFiltration I).N 0 where
  toFun := (fun a => ⟨ a , by simp ⟩)
  map_zero' := rfl
  map_add' := fun _ _ => rfl



-- we need A/I  ≃+* GRP I 0 , the sorries below may not be necessary, nonetheless the general case of I^m/I^m+1 ≃+ GRP I m should be proven. 

def aux2 : A ⧸ I →+ (GradedPiece (CanonicalFiltration I) 0) := by
  apply QuotientAddGroup.map _ _ (aux1 I) _
  · intro x hx
    simp
    exact hx


def zeroeth_morphism : A ⧸ I →+* (GradedPiece (CanonicalFiltration I) 0) where
  toFun := aux2 I
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩ 
    rfl
  map_zero' := AddMonoidHom.map_zero (aux2 I)
  map_add' := fun x y => AddMonoidHom.map_add (aux2 I) x y




def aux11 (I : Ideal A) (m : ℕ ): (CanonicalFiltration I).N m →+  ↥(I^m) := sorry

lemma aux1.Bijective (I : Ideal A) (m : ℕ ) : Function.Bijective (idealPowerToFiltrationComponent I m ):= sorry 





noncomputable def GradedRingPiece.toIdealQuotient.map (I : Ideal A) (m : ℕ) : GradedRingPiece I m → I^m/I^(m+1) := by
  unfold GradedRingPiece GradedPiece CanonicalFiltration
  simp 
  intro x
  refine Classical.indefiniteDescription (Membership.mem (I ^ m / I ^ (m + 1))) ?_
  refine Subtype.existsOfSubtype ?_

  
  sorry

noncomputable def GradedRingPiece.toIdealQuotient (I : Ideal A) (m : ℕ) : GradedRingPiece I m →+ I^m/I^(m+1) where
  toFun := GradedRingPiece.toIdealQuotient.map I m
  map_zero' := sorry
  map_add' := sorry

lemma GradedRingPiece.toIdealQuotient.isBijective (I : Ideal A) (m : ℕ) : Function.Bijective (GradedRingPiece.toIdealQuotient I m):= sorry
