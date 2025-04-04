import Mathlib


-- 7.5 Polynomial.isNoetherianRing



-- 10.22(i)
-- inspiration GradedRing.GradeZero.isNoetherianRing

--lemma GradedRing.ofNoetherian.isNoetherian {A: Type*} [Ring A] [IsNoetherianRing A]


-- 10.25

-- 10.26
theorem AdicCompletion.ofNoetherianRing.isNoetherianRing {A : Type*} [CommRing A] (I : Ideal A) [h: IsNoetherianRing A] : IsNoetherianRing (AdicCompletion I A) := by
  sorry
