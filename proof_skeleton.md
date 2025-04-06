Numbering from Atiyah-Macdonald. Make note if available in mathlib.

Questions to ask:
- in what generality are the statements true? should we prove more general results?
- are there any results in mathlib that imply a desired result?
- the lemmas as stated might not be needed for the main result, nonetheless it is probably good to formallize them as stated in A-M (e.g. 10.15 might not be needed, the result that implies it could be used directly).

# Proof Tree

- [ ] 10.26. 
    - [ ] ⁠10.22. 
        - [ ] 7.6.
            - [X] 7.5.
                - [ ] 6.2. 
                - [ ] 6.5.
                    - [ ] 6.3.
                    - [ ] 6.4.
                      - [ ] 6.3 see above.
        - [ ] 10.15.
            - [X] 10.13.
                - [ ] 2.18.
                    - [ ] 2.9. 
                - [?] 10.3.
                    - [ ] 10.2.
                        - [ ] 2.10.
                - [ ] 10.12.
                    - [?] 10.3
            - [X] 10.14.
            - [ ] 10.5.
            - [ ] 10.4.
                - [?] 10.3.
            - [ ] 1.9.
            - [ ] 1.5. 
    - [ ] ⁠10.25.
        - [ ] 6.2.
        - [ ] 10.24.
            - [ ] 10.23.
                - [ ] 10.2

## Ordered
Check box when implemented in lean. If already in mathlib make note.

- [ ] 1.5 (every non-unit contained in maximal ideal).

- [ ] 1.9 (x in jacobson radical iff 1-xy unit for all y).

- [ ] 2.9 (exactness of sequence iff exact on hom space).

- [ ] 2.10 (snake lemma).

- [ ] 2.18 (tensor is exact).

- [X] 6.2 (**in mathlib**) (M Noeth A-mod iff every submod of M is f.g.). 

- [ ] 6.3 (exact sequence of A-mods, middle Noeth iff edges are).

- [ ] 6.4 (Direct sum of Noeth A-mods is Noeth - same for Artin).

- [ ] 6.5 (A NoethRing, M f.g. A-mod ==> M Noeth - same for Artin).

- [X] 7.5 (**mathlib**: Polynomial.isNoetherianRing) (Hilbert's Basis Theorem).

- [ ] 7.6 (Hilbert's Basis Theorem for n variables).

- [ ] 10.2 (inverse limits left exact. if system is surjective then exact)

- [?] 10.3  (**mathlib**: AdicCompletion.map_exact) (completion of exact sequence of groups is exact).

- [ ] 10.4 (quotient of completion iso to quotient).

- [ ] 10.5 (completion is complete).

- [ ] 10.12 (completion of exact sequence of f.g. A-mods, A NoethRing,  is exact).

- [X] 10.13 (**mathlib**: AdicCompletion.ofTensorProductEquivOfFiniteNoetherian) (M fg A-mod, surjection onto M', isomorphism if A NoetherianRing).

- [X] 10.14 (**mathlib**: AdicCompletion.flat_of_isNoetherian) (A NoethRing, A' I-adic completion, A' flat A-alg).

- [ ] 10.15.
    - [X] i. (**mathlib** AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian, take I = M. this might also cover 10.15.ii.). (A Noethring, A' I-adic compl. ==> I' \cong A'tensor I)
    - [?] ii. (A Noethring, A' I-adic compl. ==> I^n ' = I'^n)
    - [ ] iii. (A NoethRing, A' I-adic compl. ==>  consec quotient I^n iso to completion of it).

- [ ] 10.22 
    - [ ] i. (A NoethRing, I ideal, G(A) Noetherian)
    - [ ] ii. (A NoethRing, I ideal. G(A) \simeq G(A')

- [ ] 10.23 (phi: A -> B filtered group homom, inducing phi'. G(phi) h ==> phi' h, for h inj or surj).

- [ ] 10.24 (M_n I filtration of M. A complete, M Hausdorff, G(M) f.g.==> M f.g. A-mod).

- [ ] 10.25 (assumptions on A, M, G(A) f.g, G(M) Noeth G(A) module ==> M Noeth A Mod).

- [ ] 10.26 (main theorem).

