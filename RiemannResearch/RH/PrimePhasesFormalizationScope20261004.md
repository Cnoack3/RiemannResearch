# Prime phases: formalization scope, 4 October 2026

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, source version 2.
Lean 4.33.0-rc2; Mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`.
Publication validation checks the actual modules and their genuine dependencies.
A checked implication does not discharge an analytic hypothesis in its type.

| Manuscript component | Established formal result | Remaining obligation |
|---|---|---|
| Complete inverse Gram bounds | Actual full, subdictionary and composite inverse bounds `4 R² M_R² ||a||₂² <= 4 R² H_R² ||a||₂²`; exact energy completion retains all interior squares and terminal boundary; physical Gram minus full inverse is a residual norm square | RH-strength signed saturation |
| Dual-defect replacement | Actual q_K and explicit harmonic multiples-sum coefficients for every conductor; exact error `A_K²/(K-A_K)+1/(K+1)`; eventual `2 log(K+1)/sqrt K`; moving full-inverse defect iff actual closed-span membership | Provider making the defect vanish; classical RH-to-density formalization |
| Natural approximation | Exact natural error = head error + signed charge squared; exact arbitrary-threshold improper tail; centering and charge correction each cost at most factor 2 | Classical RH-to-natural-approximation provider |
| Corrected prime-only dyadic energy | Actual prime-power error square summability; exact paired factor 1/2; dyadic error budget 3E; signed energy difference bound | Decisive cofinal O(log N) arithmetic estimate |
| Integrated zero expression | Actual zeta kernel absolutely summable, complete-minus-head identity and real-height tail bound; exact real dilogarithm/logarithmic-integral trivial-zero correction, positive and at most 2/x² for x>=3 | Arithmetic Perron/approximation identity joining these pieces |
| Growing Fourier estimates | Actual complete integer prime-power covariance rows <= log N+log 4+4; exact square-root conjugation; signed complex quadratic Schur bound; conditional entrywise-remainder consumer | Actual uniform Landau/FMZ provider and actual-zero growing-support specialization |
| Distinct-ordinate phase measure class | Finite sampling inequalities and continuous weak-limit regularity imply mutual absolute continuity | Actual empirical-measure/Haar convergence and uniformly bounded normalized ordinate-square budget |
| Marked Fourier tail | Exact original rational-kernel Laplace representation and Cauchy bound; literal tent Fourier integral, L1 inversion; actual full-copy Gaussian/window assembly; literal fixed-shell absolute tail O(B^-1) with exact occupancy constant | Known unconditional microscopic square-budget theorem needs a checked provider for uniformity in shell height; bounded-frequency signed cancellation remains open |

Write `H_R=sum_(1<=q<=R) 1/q` and `M_R=sum_(1<=q<=R) |mu(q)|/q`.
Vanishing Möbius coefficients sharpen an estimate without deleting any physical
conductor. In particular every composite and nonsquarefree conductor remains
in the complete dictionaries. The inverse bounds are Euclidean quadratic bounds.

For the actual support projection, the coefficients are now defined by actual
inner products and proved equal to the manuscript's multiples sum:

    tau_(K,d) = sum_(1<=j<=K/d) [
      -1/(d*j) + 1/(K+1)
      + A_K/(K-A_K) * (H_(K+1)-H_(d*j)) ].

This formula feeds the existing moving-support inverse criterion directly.
The criterion is equivalent to closed-span membership; its sufficient RH
implication is checked. Calling it an RH equivalence additionally requires the
classical RH-to-density provider absent from the current formalization.

The prime-only arithmetic specialization consumes the repository's proved
`NumberTheory/PrimeNumberTheorem/Quantitative/MediumPNT.lean`. The phase-covariance
row specialization consumes the proved `Mertens.E₁Λ.le`. Neither introduces
a new arithmetic hypothesis. The phase-covariance logarithmic bound concerns
a different matrix from the decisive cofinal screened inverse Gram bound.

For the actual integrated zero kernel
`-m(rho) exp(rho log x) (1-exp(-rho log 2))/rho²`, the integer weight tail is
at most `32 A0 log(K+3)/K`, and the kernel tail is at most
`192 A0 x log(K+3)/K` for K>=5 and x>=1.
For real Y>=10 the finite-head error is at most `768 A0 x log Y/Y`.
Both endpoints and all multiplicities belong to the finite head. A0 is a proved
unit-window count constant, not a numerically certified decimal.
The trivial-zero correction is exactly

    [Li2(4/x²)-Li2(1/x²)]/4
      = integral_(x/2)^x [-log(1-t^-2)/(2t)] dt,  x>2.

These checked series and correction identities still do not identify the full
expression with the integrated Chebyshev error.

The distinct-ordinate limiting-law conclusion is equality of null sets with
Haar after its actual sampling providers are supplied. It is not equality of
measures. The generic weak-limit theorem cannot substitute for those providers.

For marked tails, let M be the number of all analytic zero copies in (T,2T],
Q the square occupancy budget at scaled ordinates `scale*gamma/sqrt(2)`, and
`c0=exp(-1/8)/sqrt(2*pi)`. The actual normalized original rational marked form
has literal absolute tent-weighted tail, including |alpha|=B, at most

    24 Q / (c0 M pi² B),  B>=1.

This finite-shell statement is unconditional, including totalized empty-shell
division. Its uniform-in-T consumer gives `24 C/(c0 pi² B)` from `Q<=C M`.
The latter budget is a missing Lean formalization of the known unconditional
Tsang/Selberg/Fujii second-moment input. Ordinary unit-height O(log T) zero
counts do not discharge it. Sources: Simonič, Trudgian and Turnage-Butterbaugh,
Theorem 2, https://arxiv.org/abs/2010.10675; Goldston, Lee, Schettler and
Suriajaya, Propositions 1-2 and (5.4)-(5.6), https://arxiv.org/abs/2503.15449.

Bounded-frequency signed marked cancellation, the cofinal arithmetic bound,
and signed inverse saturation remain unproved. No new proof of RH is asserted.
`#print axioms` reports foundational axioms, not local theorem hypotheses;
the catalog separately records unresolved domain-specific providers.
The proposed larger-support bootstrap is recorded separately as unverified
research, not as a Lean-established result.
