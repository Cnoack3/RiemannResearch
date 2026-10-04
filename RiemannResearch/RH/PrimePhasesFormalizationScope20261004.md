# Prime phases: formalization scope, 4 October 2026

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, source version 2.
Lean 4.33.0-rc2; Mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`.
The project checkpoint validates these modules in their actual import environment.
Successful snippet checks are development evidence, rather than publication evidence.

| Manuscript component | Established formal result | Remaining obligation |
|---|---|---|
| Complete inverse Gram bounds | Actual inverse quadratic bound `5 R² H_R² ||a||₂²`; actual subdictionary/composite corollaries; physical Gram minus full inverse is a residual norm square | RH-strength signed saturation |
| Dual-defect replacement | Actual q_K, exact error `A_K²/(K-A_K)+1/(K+1)`; eventual `2 log(K+1)/sqrt K`; moving full-inverse defect iff closed-span membership | Provider making the defect vanish; classical RH-to-density converse formalization |
| Corrected prime-only dyadic energy | Exact signed prime incidence budget; actual prime-power error square summability; exact paired factor 1/2; dyadic error budget 3E; signed energy difference bound | Decisive cofinal O(log N) arithmetic estimate |
| Integrated zero series | Actual zeta kernel absolutely summable; finite head retains both endpoints and multiplicities; exact complete-minus-head remainder; explicit real tail bound | Arithmetic Perron/approximation identity; trivial-zero/dilogarithm evaluation |
| Growing Fourier estimates | Generic finite Wiener and cardinality/ell2 error bounds | Actual quantitative FMZ/Landau provider, permitted growing support, covariance Schur assembly |
| Distinct-ordinate phase measure class | Finite weighted/distinct sampling and continuous weak-limit regularity imply mutual absolute continuity | Actual Haar convergence and uniformly bounded normalized multiplicity-square budget |
| Marked Fourier tail | Tent inverse-square envelope, positive-kernel row bound, finite endpoint remainder and two-sided 4C/B scalar tail | Actual microscopic cluster budget, Gaussian/kernel/Fourier representation and integral partition |

The unconditional arithmetic specialization consumes the repository's proved
`NumberTheory/PrimeNumberTheorem/Quantitative/MediumPNT.lean`, not a new
arithmetic hypothesis. During snippet development its exact predicate was supplied
explicitly because its object file was absent; publication validation builds and
imports the actual provider. The Costa-Pereira separation is in the pinned Mathlib.

For the actual integrated zero kernel
`-m(rho) exp(rho log x) (1-exp(-rho log 2))/rho²`, the integer weight tail is
at most `32 A0 log(K+3)/K`, and the kernel tail is at most
`192 A0 x log(K+3)/K` for K >= 5 and x >= 1.
For real Y >= 10 the finite-head error is at most `768 A0 x log Y/Y`.
A0 is a proved unit-window count constant, rather than a numerically certified
decimal. This convergent-series statement does not identify it with the
integrated Chebyshev error.

The distinct-ordinate law conclusion is equality of null sets with Haar when the
listed actual providers are discharged; it is not equality of measures.
A generic uniform spectral-window mass hypothesis is not established by the
ordinary unit-window O(log T) zero count. The required microscopic square budget
is the substantive Tsang input (see Simonič, Trudgian and Turnage-Butterbaugh,
Trans. AMS 375 (2022), Theorem 2, https://arxiv.org/abs/2010.10675).
Formalizing that input and the actual marked assembly is still open.

Bounded-frequency signed marked cancellation, the cofinal arithmetic bound,
and signed inverse saturation remain unproved. No new proof of RH is asserted.
`#print axioms` reports foundational axioms, not local theorem hypotheses;
the catalog separately records every unresolved analytic provider.

The support projection coefficients are obtained from actual finite-span
membership. The manuscript's additional closed-form multiples-sum formula for
those coefficients is not asserted here.
