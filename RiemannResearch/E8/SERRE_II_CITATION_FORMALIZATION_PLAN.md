# Citation-to-Lean formalization plan

Artifact: `serre_ii_e8_program_2026-08-05.pdf` (51 pages).

This is the implementation ledger for all 33 bibliography entries. It is
deliberately stricter than the source audit: a row is complete only when the
exact result used by the manuscript is represented by a kernel-checked Lean
declaration with all hypotheses visible. Reading or validating a paper does not
complete a row.

## Status key

- **Kernel foundation**: reusable Lean infrastructure has been proved, but the
  cited theorem itself has not.
- **Mathlib foundation**: relevant upstream definitions exist, but the cited
  theorem is absent.
- **Not started**: no theorem-level formalization exists.
- **Certificate missing**: Lean can check a finite certificate once supplied,
  but the manuscript does not include the certificate.
- **Context only**: the citation is not a proof input to a labeled result.
- **Unused**: the bibliography item is not cited in the body.

## Bibliography-wide target ledger

| Ref. | Exact Lean target for the manuscript use | Reusable base now available | Status / next dependency |
|---|---|---|---|
| [1] Bayer-Fluckiger--Parimala | Serre II for the split nontrialitarian (D_8) groups used in Theorem 4.6 and Propositions 6.16--6.17 | Clifford and spin groups exist in Mathlib | Not started; needs reductive group schemes, torsors, and field cohomological dimension |
| [2] Bhaskhar | No positive theorem is invoked; encode the stated scope exclusion only if the warning becomes a formal specification | None required | Context only |
| [3] Barquero--Merkurjev | Norm-principle map and the proof that the relevant (E_8) abelian quotient gives only a tautology | Basic group quotients exist | Context only; full reductive-group norm principle absent |
| [4] Borovoi--Reichstein--Gille | Power operation used in Warning 5.15 and the exact statement of Proposition B.1(3) | Pointed-set kernel logic in `Logic.PointedKernel` | Context only; nonabelian cohomology operation absent |
| [5] Brosnan | Motivic Białynicki--Birula decomposition used in Theorem 3.2(ii) | Schemes and algebraic cycles exist in Mathlib | Not started; Chow groups, correspondences, and motives are absent |
| [6] Bruhat--Tits | Local Serre II endpoint cited in Remark 5.21 | Valued fields exist in Mathlib | Context only; Bruhat--Tits/reductive-group layer absent |
| [7] Brown | Stable-elements theorem in additive group cohomology, specialized to the Sylow calculation of Theorem 5.7 | Restriction towers and coefficient transports; subgroup conjugation naturality; inner conjugation triviality; finite-group averaging; normal finite-index injectivity | Kernel foundation; the arbitrary-subgroup stable-elements submodule and reverse image characterization still require cohomological transfer and the Mackey formula |
| [8] Chernousov--Gille--Merkurjev | Integral Rost nilpotence for projective homogeneous varieties | Schemes and algebraic cycles exist | Not started; Chow motives and projective homogeneous varieties absent |
| [9] Chernousov | The maximal-torus/toral lifting theorem used in Theorem 6.1 | Affine group schemes, global fpqc Čech (H^1), and finite-Galois coordinate comparison exist | Not started; the explicit Yoneda/torsor bridge, quasi-split (E_8), and centralizers remain absent |
| [10] Creutz | The particular index-one/no-rational-point surface example in Remark 4.10 | Algebraic schemes exist | Context only |
| [11] de Jong--He--Starr | Rational-simple-connectedness result delimiting the surface-function-field case | Schemes exist | Context only |
| [12] De Concini--Springer | Wonderful compactification over the manuscript's characteristic-zero base | Root systems exist | Not started; split semisimple group schemes, orbit strata, and descent absent |
| [13] Evens--Jones | One-sided fixed-locus and tangent-weight calculation after a valid chamber change | `LinearAlgebra.regularFunctional_exists_adaptedBase`; E8 Coxeter length facts | Kernel foundation; fixed schemes, tangent representations, and arbitrary-field descent remain |
| [14] Garibaldi | No body occurrence; likely intended for the HSpin16/EVIII setup | Clifford/spin foundations exist | Unused |
| [15] Garibaldi--Semenov | Odd-degree splitting of (E_8)-torsors over the stated fields | Nonabelian discrete (H^1) and neutral-class functoriality | Not started; Rost invariants, cohomological dimension, and algebraic (E_8) absent |
| [16] GAP/CTblLib/TomLib | Machine-checkable certificates for Theorems 6.9--6.12, Propositions 6.16--6.17 and 6.26, and Corollary 6.28 | Finite arithmetic and abstract Burnside/top-mark kernels | Certificate missing; scripts, database snapshot, row maps, fusions, and raw witnesses are absent |
| [17] Geldhauser--Petrov | Selected (E_6/P_{1,2,6}) index-one-to-point theorem | None specific | Context only; not an (E_8) proof input |
| [18] Gille 2001 | Cyclic degree (2,3,5) neutral-kernel theorems, cyclic-prime torus theorem, and toral lifting | Discrete and global fpqc nonabelian (H^1), finite-Galois coordinate comparison, restriction neutrality, and `HasTrivialKernel.comp` | Kernel foundation; the explicit Yoneda/torsor bridge, algebraic (E_8), tori, and cd hypotheses remain |
| [19] Gille LNM 2238 | Corollaries 9.3.6--9.3.7, corrected Lemma 1.6.5 use, and the exact scope of Theorem 8.4.1(2) | Same nonabelian (H^1) and pointed-kernel foundations | Not started at theorem level; requires almost-abelian (E_8), multiplicative-type groups, and (R)-equivalence |
| [20] Gille errata | Corrected hypotheses/statements integrated into the Lean versions of [19] | Source audit fixes the intended statements | Not started; must be built into [19], not postulated separately |
| [21] Gille--Lee | Oriented embedding functor as a homogeneous space | Affine group schemes exist | Context only; reductive homogeneous spaces absent |
| [22] Gille survey | No standalone proof input | None required | Context only |
| [23] Harari--Szamuely | The exact Poitou--Tate segment for a torus used in Theorem 5.13 | Additive homological algebra exists | Not started; global fields, restricted products, duality, and 1-motives absent |
| [24] Harbater--Hartmann--Krashen | Equivalence between patching and simultaneous factorization in the cited setting | Fields and linear algebra exist | Context only; patching inverse systems absent |
| [25] Izquierdo--Lucchini Arteche | Corollary 4.14 at (q=0), transfer/index-one theorem, and the reduction theorem used in 2.1, 2.2, and 7.2 | Point-field gcd infrastructure exists | Not started; Rost/norm groups, algebraic torsors, and cd hypotheses absent |
| [26] Merkurjev | Theorem 4's constructed (2)-special cd-(le2) field and preserved examples | Field towers and quadratic forms partly exist | Not started; valuation/tower construction and Brauer-division preservation absent |
| [27] Parimala | Homogeneous index-one/no-point examples delimiting Theorem 4.9 | Schemes exist | Context only |
| [28] Platonov--Rapinchuk | Kneser--Harder--Chernousov Hasse principle and local vanishing used in Theorem 5.13 | Number fields have partial Mathlib support | Not started; simply connected semisimple groups and nonabelian adelic (H^1) absent |
| [29] Sansuc | Proposition 6.10 Picard--Brauer exact sequence for (E_8/HSpin_{16}) | Scheme cohomology foundations are incomplete | Not started; Picard/Brauer groups of homogeneous spaces absent |
| [30] Sechin--Semenov | Oriented Rost nilpotence, split-motive criterion, and height monotonicity | Algebraic cycles exist | Not started; oriented cohomology and algebraic Morava (K)-motives absent |
| [31] Semenov | The narrower (p=2), high-height independent check actually supported by Theorem 6.16 | None beyond cycles | Not started; not used as a substitute for the uniform transfer proof |
| [32] Totaro | Degree-dividing-2880 splitting theorem and the exact finite (E_8) subgroup/stabilizer table uses | E8 Coxeter/Cartan data and manuscript arithmetic certificates | Kernel foundation only; finite (W(E_8)) realization, algebraic torsors, and splitting-field geometry remain |
| [33] Thang | Local/global corestriction principle mentioned after Proposition 6.34 | Additive restriction foundations exist | Context only; nonabelian corestriction absent |

## Shared dependency order

1. Complete the explicit Yoneda-section comparison for the finite-Galois
   singleton cover and fpqc torsor classification. Discrete (H^1), the global
   fpqc Čech quotient, and the coordinate Čech/discrete equivalence now compile.
2. Build split reductive group schemes, maximal tori/Borels, root data, and the
   split (E_8) group; connect its Weyl group to Mathlib's E8 Coxeter group.
3. Add cohomological dimension, restriction/corestriction, Rost invariants, and
   the cyclic-kernel machinery needed by [18], [19], [15], [25], and [9].
4. Independently build finite (W(E_8)) certificate checkers and commit every
   external computation as explicit data checked by Lean's kernel.
5. Build Chow groups, correspondences, projective homogeneous varieties,
   motives, oriented theories, and Rost nilpotence for [5], [8], [30], [31].
6. Add global duality/adelic infrastructure for [23] and [28].

No row may be upgraded from a source citation to a Lean theorem merely by
declaring the paper's conclusion as a hypothesis. Conditional assembly
theorems remain useful, but they do not close a bibliography row.
