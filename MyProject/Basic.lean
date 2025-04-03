import Mathlib


structure MyStruct where
  val : Nat

instance a : MyStruct := { val := 42 }



theorem AdicCompletion.isNoetherianRing {A : Type*} [CommRing A] (I : Ideal A) [h: IsNoetherianRing A] : IsNoetherian A (AdicCompletion I A) := by 
  sorry


