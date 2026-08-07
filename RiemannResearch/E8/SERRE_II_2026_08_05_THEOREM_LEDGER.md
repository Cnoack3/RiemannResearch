# Theorem ledger for the 5 August 2026 E8 Serre II memorandum

Artifact: serre_ii_e8_program_2026-08-05.pdf, 51 pages.

This ledger covers every labeled result in the attached artifact: 61 theorems,
propositions, corollaries, and lemmas; four conjectures; and Question 5.22.
It records the strongest evidence currently available. It is not a claim that
the E8 case of Serre's Conjecture II has been solved.

## Status key

- **Lean exact fragment**: the cited declaration proves the stated arithmetic
  or abstract implication without placeholders.
- **Lean conditional**: Lean proves the consequence only after named
  domain-specific hypotheses are supplied.
- **Source dependent**: the manuscript proof materially invokes external
  results not formalized in this project.
- **Manuscript only**: an informal proof is printed, but no kernel proof exists.
- **Unreproduced computation**: required scripts or raw output are absent.
- **Open**: explicitly conjectural or equivalent to the unresolved E8 case.

## Sections 2--4

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 2.1 | Source dependent | The three conclusions are supported respectively by Izquierdo--Lucchini Arteche Corollary 4.14, Garibaldi--Semenov, and Totaro Theorem 0.1; none is formalized here. |
| Theorem 2.2 | Manuscript only, conditional on 2.1 | The co-p closure and finite-descent argument is coherent; no nonabelian Bezout conclusion is drawn. |
| Proposition 3.1 | Source dependent | Requires the wonderful compactification, orbit geometry, and fpqc descent absent from Mathlib. |
| Theorem 3.2 | **Literal statement defective; Lean conditional after correction** | Changing the sign of an arbitrary regular cocharacter does not normalize its Weyl chamber in rank greater than one. See a2Coroot_sign_normalization_counterexample. The corrected assembly universalFixedLocusAndSplittingField has twelve open, load-bearing inputs. |
| Corollary 3.3 | Unverified | Depends on Theorems 2.1 and 3.2. |
| Proposition 4.1 | Manuscript only | The localization calculation CH0(Gm)=0 is not formalized here. |
| Proposition 4.2 | Source dependent | Uses rationality of the split EVIII space, compactification, and localization. |
| Theorem 4.3 | Citation conditional | The exact scope of Gille Corollary 9.3.6 has not been checked from the source text. |
| Corollary 4.4 | Citation conditional | Depends on Theorem 4.3. |
| Theorem 4.5 | Citation conditional | Depends on Theorem 4.3 or the separately cited finite-subgroup criterion. |
| Theorem 4.6 | Source dependent | Uses Sansuc, classical Serre II, Kummer theory, and Theorem 2.1; the standing characteristic-zero hypothesis should be explicit in part (ii). |
| Proposition 4.7 | Source dependent | Uses Proposition 4.6, rationality, and purity. |
| Proposition 4.8 | Manuscript only | The correspondence proof is standard but Chow motives are not formalized here. |
| Theorem 4.9 | Source dependent | Requires motivic restriction/corestriction, Rost nilpotence, and a split-motive criterion. |
| Theorem 4.11 | Source dependent | Requires Theorem 2.2 and the cited algebraic Morava K-motive formalism. |
| Corollary 4.12 | Unverified | Depends on Theorems 4.9 and 4.11. |

## Section 5

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 5.4 | Source dependent | Iterates Gille's cyclic descent theorem over a solvable normal series. |
| Theorem 5.6 | Manuscript only | An explicit finite quadratic-space construction is printed, but the A5 action is not formalized here. |
| Theorem 5.7 | Source dependent | Uses rational A5 representation theory, a linking form, stable elements, and Gille's marker criterion. |
| Corollary 5.8 | Citation conditional | Depends on Theorems 4.3, 5.6, and 5.7. |
| Theorem 5.9 | Manuscript only | The explicit S5 lattice construction and its mod-p invariant calculation are not formalized. |
| Corollary 5.10 | Source dependent | Depends on Theorem 5.7 and quadratic cyclic descent. |
| Theorem 5.11 | Source dependent | The lattice assertions and the corrected R1 marker lemma are not instantiated in Lean. |
| Proposition 5.12 | Manuscript only | Inflation--restriction deduction from Theorem 5.11. |
| Theorem 5.13 | Source dependent | Uses Chebotarev, local norm computations, Poitou--Tate, and Kneser--Harder--Chernousov. |
| Corollary 5.14 | Unverified | Depends on Theorems 5.11 and 5.13. |
| Theorem 5.16 | Citation conditional; arithmetic exact in Lean | Existence and splitting of the fields use Totaro and Theorem 4.3. The exact index products and gcd for 135, 11200, 12096 are checked in SerreIIProgramChecks. |
| Corollary 5.17 | Exact arithmetic and additive shadow in Lean; geometry unverified | serreIIProgram_threeSubsystem_bezout and serreIIProgram_threeSubsystem_gcd check the degree calculation. The splitting cycles still depend on Theorem 5.16. |
| Theorem 5.19 | Lean conditional | quasisimpleCoreOfFullWeylDescent has eleven open, load-bearing E8, Galois, and nonabelian-cohomology inputs. |

## Section 6

| Result | Current status | Evidence or blocker |
|---|---|---|
| Theorem 6.1 | Citation conditional | Uses toral lifting, cyclic descent, Totaro's maximal-subgroup table, and Theorem 4.3. |
| Proposition 6.2 | Manuscript only | The finite orbit and marker data are not reproduced in Lean. |
| Theorem 6.3 | Manuscript only | The finite quadratic-module and Fourier calculations are not formalized. |
| Theorem 6.5 | Citation conditional | Uses building geometry and Theorem 4.3. |
| Theorem 6.6 | Manuscript only; statement ambiguous | Gauge independence is proved only after fixing the flag. Changing the flag requires an explicit conjugacy identification of the fields and double-coset spaces. |
| Proposition 6.7 | Exact arithmetic/additive shadow in Lean; nonabelian statement unverified | serreIIProgram_a8Gauge_field_degrees, serreIIProgram_a8Gauge_bezout, serreIIProgram_a8Gauge_gcd, and eq_zero_of_serreIIProgram_a8Gauge_annihilators check the numerical and abelian core. The PDF also contains the literal token qquad in the statement. |
| Theorem 6.9 | Exact table arithmetic in Lean; field claims unreproduced | serreIIProgram_survivorEnvelope_bezout and serreIIProgram_survivorEnvelope_gcd check all five rows. The GAP double-coset certificate and Theorem 4.3 input are missing. |
| Theorem 6.10 | Unreproduced computation | The 11171 to 313 to 303 sieve requires absent GAP, CTblLib, and TomLib scripts and raw output. |
| Theorem 6.11 | Unreproduced computation | The 303 to 150 plus 153 to 31 compression depends on the missing table-of-marks computation. |
| Proposition 6.12 | Unreproduced computation | Nonsplitting, fusion, marker, and H1 data for all 31 lifts have not been rerun. |
| Corollary 6.13 | Unverified | Depends on Theorems 6.11 and 6.12. |
| Corollary 6.14 | Citation/computation conditional | Depends on Proposition 6.12 and the corrected Gille marker lemma. |
| Proposition 6.15 | Exact order arithmetic in Lean; group/gauge statement unverified | serreIIProgram_binaryIcosahedral_index_arithmetic checks the displayed orders and indices. The nonsplit lift and descent inputs remain external. |
| Proposition 6.16 | Computation and citation conditional | Requires missing subsystem-orbit data, classical Serre II, and the lift data of Proposition 6.12. |
| Proposition 6.17 | Unreproduced computation | The twelve triality tests require the absent root-action script. |
| Proposition 6.19 | Manuscript only | The oriented transporter and bitorsor descent are not formalized. |
| Proposition 6.21 | Abstract additive kernel checked | eq_zero_of_coprime_restrictions checks the coprime restriction--corestriction core; the group-cohomology instantiation is not formalized. |
| Proposition 6.22 | Manuscript only | The Weil-restriction dimension and density argument is not formalized. |
| Proposition 6.24 | Manuscript only | The Bass--Serre amalgam and Euler-characteristic calculation are not formalized. |
| Proposition 6.26 | Unreproduced computation | The A11 Burnside relation and even conjugators require an absent GAP certificate. |
| Corollary 6.28 | Computation conditional | Depends on Proposition 6.26 before the field-theoretic realization. |
| Theorem 6.30 | Computation conditional | The abstract generation argument depends on Theorem 6.10's unreproduced gcd data; the common-fixed-point core is isolated in GeneratedFixedPoint.lean. |
| Corollary 6.31 | Unverified | Depends on Theorems 6.10 and 6.30. |
| Proposition 6.32 | Exact abstract top-mark kernel in Lean | not_mem_addSubgroup_closure_of_mark proves that a mark-one class cannot be additively generated by mark-zero classes. Instantiating the abstract group with the Burnside ring remains unformalized. |
| Proposition 6.34 | Conditional on an open conjecture | The implication uses Conjecture 6.33, Theorems 6.1 and 6.10, and quadratic descent. |
| Proposition 6.35 | Open-equivalence reformulation | The printed equivalence is not independent progress beyond the unresolved E8 case. |
| Lemma 6.36 | **Lean exact abstract kernel** | eq_zero_of_gcd_one_annihilators proves the finite Bezout-annihilator argument. Applying it to H1 still requires the stated restriction--corestriction maps and formulas. |

## Section 7

| Result | Current status | Evidence or blocker |
|---|---|---|
| Lemma 7.1 | Manuscript only | Requires finite-presentation descent for torsors over filtered field unions. |
| Theorem 7.2 | Source dependent | Uses Theorem 2.1 over a p-special field and the elementary gcd-of-p-powers argument. |
| Corollary 7.3 | Source dependent | Depends on Theorem 7.2 and Merkurjev's construction. |
| Proposition 7.4 | Manuscript only | The specialization argument for affine torsors over a pure transcendental extension is not formalized. |
| Proposition 7.5 | Partial abstract kernel only | fixed_of_fixed_on_join_eq_top checks the common-fixed-point implication; the Galois and gauge-coset realization is not formalized. |

## Explicitly open items

| Item | Status |
|---|---|
| Conjecture 5.1 | Open odd-degree wonderful descent. |
| Conjecture 5.2 | Open odd-degree Borel descent. |
| Conjecture 5.3 | Open odd-degree EVIII descent. |
| Question 5.22 | Open full-Weyl toral neutrality question. |
| Conjecture 6.33 | Open finite-etale kernel norm principle; the product-algebra kernel and componentwise corestriction conventions need formal definitions. |

## Artifact and version defects

1. Theorem 3.2's sign-only chamber normalization is false. The corrected
   statement must choose a chamber-normalized cocharacter or conjugate and
   reindex.
2. Proposition 6.7 contains the literal malformed token qquad where a spacing
   command was intended.
3. Theorem 6.6's phrase “independent of every choice” is only justified after
   fixing the flag.
4. Appendix A names computations but does not include the executable scripts,
   row maps, fusion witnesses, package snapshots, or raw output.
5. WeylIndexPacket.lean checks the distinct packet 135, 2240, 48384, not the
   attached PDF's 135, 11200, 12096. A8NormalizerArithmetic.lean checks
   15, 35, 336, not Proposition 6.7's 15, 35, 4032.
6. Almost abelian, R1 H1, the motive categories, normalized abelian invariant,
   and the product-algebra neutral fiber in Conjecture 6.33 need exact
   definitions before literal formalization.
