# Projection displacement audit and quantitative prime control

5 November 2026. The source document is *Projection_Displacement_Prime_Atoms_and_Carries.pdf*, seven pages, pinned to `24c6dcd3`. This audit uses repository revision `69cb8cb6` and the companion modules added with this note.

## Conclusion

The actual matched projections obey a quantitative bound

\[
\|1-f_P\|_P^6\le64\zeta(2)\|P_Wd\|_Q^2,
\qquad d=f_Q-f_P,
\]

where \(W\) is the closed prime-atom span. The canonical projected-carry decomposition is formalized. The premise \(P_Wd=0\) remains open. This audit does not prove \(d=0\) or RH.

Both fits project the target \(1\) onto the same closed space of physical sequences. They use the two equivalent inner products induced by \(Q(n)=1/(\zeta(2)n^2)\) and \(P(n)=1/[n(n+1)]\).

## Corrections and conditional inputs

On page 6, the sourced signed-series criteria require

\[
\sum_{m\ge1}\left|\sum_{n\ge m}Q(n)d(n)\right|<\infty,
\qquad
\sum_{M\ge1}\frac1{M^2}\left|\sum_{n\le M}d(n)\right|<\infty.
\]

The outer absolute values are missing in the PDF. Lean's `Summable` for real sequences supplies absolute outer summability. The cited declarations are `riemannHypothesis_of_summable_displacement_signedTail` and `riemannHypothesis_of_summable_displacement_prefix` in `QSquarefreeDisplacementSignedTails.lean`. Ordinary conditional convergence of the displayed series would require an additional argument. This is a mismatch between the wording and its cited proof. No counterexample to the weaker wording has been established here.

On page 7, `riemannHypothesis_of_displacement_eighth` explicitly retains `HasSubcriticalApproximation`. The externally cited zero-free region and Lee approximation discussion do not discharge that premise inside this Lean development. The Vinogradov--Korobov displacement transfer likewise retains its stated arithmetic input. The unconditional stretched-log displacement criterion is a separate checked declaration.

Bagchi's two-way squarefree equivalence is a published input to the exposition. The project contains the direction to Mathlib's `RiemannHypothesis` used by its vanishing criteria. This audit does not claim a fresh formalization of every external converse in the bibliography.

The finite subtree recursion on page 4 is understood for a root included in the cutoff, \(r\le H\).

## Source and declaration audit

| PDF material | Relevant Lean declarations or modules | Scope |
|---|---|---|
| Page 1, reciprocal charge and sitewise synthesis | `QHeadSlopeLimit.headCharge_tendsto_zero`, `headSynthesis_tendsto_at_site`, `QPrimeCRTCarries`, `QCompositeCarryDetection` | Charge limit, finite identities, and continuous charge detectors |
| Page 2, metric change, matched normal equation, energy gap | `QSquarefreeDisplacementRigidity.witness_mean_energy`, `QSquarefreeSchurOperator.schur_variational_gap`, `QSquarefreeDisplacementEnergy.arithmetic_displacement_energy_bound_983_2000` | Exact signed identities and stated quantitative inequality |
| Page 3, finite fitted displacement | `QSquarefreeFiniteDisplacement.finiteDisplacement_tendsto`, `QFiniteForcingData.full_conductor_forcing_deficit`, `full_conductor_forcing_error` | Actual Q/P fits of the same target and dictionary |
| Page 3, canonical orthogonal carry split | New `NestedOrthogonalDecomposition` and `QPrimeCarryProjection` | Exact projection identity, orthogonality, Pythagoras, generated closed space, and component convergence |
| Page 4, translation carries and normalized tree readout | `QDisplacementTranslationCarry.displacement_translation`, `PrimeTreeNormalizedReadout.normalized_remainder_Hilbert_tendsto` | Strong normalized convergence holds for every exponent \(a>1/2\), including the PDF's \(a=1\) |
| Page 5, increment Parseval | `QJordanChargeRows.displacement_squarefree_charge_parseval` | The actual radical-invariant increment and its squarefree charge packets |
| Page 5, divisor coefficients | `QDivisorDilationCoefficients.normalizedDivisorWavelet_inner_dilation`, `dilation_mean_eq_sum_divisor_coefficients` | Full divisor basis with unknown dilated means retained |
| Page 6, increments and regularity | `QDifferenceLimits.finite_difference_limit_iff_displacement_zero`, `QSquarefreeDisplacementRegularity.displacement_crt_blowup_of_ne_zero` | Existence of an ordinary increment limit remains a premise |
| Page 6, signed-series criteria | `QSquarefreeDisplacementSignedTails` | Outer absolute summability as corrected above |
| Page 6, multiplication and distance tests | `QSquarefreePrimeProductCriterion`, `QSquarefreeLogLeakage` | Explicit membership or leakage hypotheses |
| Page 7, finite metric gap and growth | `QFiniteMetricGap`, `MertensUnconditionalStretched`, `QSquarefreeVKDisplacement` | Exact gap, unconditional stretched-log implication, and explicitly conditional VK transfer |
| Page 7, eighth moment | `QFiniteEighthMoment`, `QFiniteEighthLee` | Approximation input and moment input remain explicit |

The audit distinguishes a declaration's proof from the truth of assumptions in its type. A compiled conditional implication supplies no proof of its open premise.

## Orthogonal decomposition and finite projections

For closed subspaces \(W\subseteq V\), put \(C=V\cap W^\perp\). The new general module proves

\[
P_C=P_V-P_W,\qquad V=W\oplus^\perp C.
\]

If \(V=\overline{\operatorname{span}}S\), it also proves

\[
C=\overline{\operatorname{span}}\{(I-P_W)s:s\in S\}.
\]

For the actual CRT carry \(C_m\), the prime synthesis identity yields

\[
(I-P_W)C_m=-(I-P_W)g_m.
\]

Consequently, the actual carry complement is exactly the closed span of the projected canonical CRT carries. The application module supplies

\[
d=d_W+d_C,\qquad
\|d\|_Q^2=\|d_W\|_Q^2+\|d_C\|_Q^2.
\]

For increasing finite spaces \(W_N\subseteq V_N\),

\[
P_{C_N}=P_{V_N}-P_{W_N}\longrightarrow P_V-P_W=P_C
\]

strongly. The theorem also permits norm-convergent inputs, including the actual \(d_N\). No monotonicity assumption is placed on \(C_N\).

## Quantitative estimate from the full matched equations

Let \(H=N+1\), \(r_{P,N}=1-f_{P,N}\), and

\[
\varepsilon_N=\|r_{P,N}\|_P^2,\qquad
\alpha_N=\|P_{W_N}d_N\|_Q.
\]

Here \(W_N\) can be any orthogonally projected subspace containing every prime atom with conductor at most \(H\). The complete signed identity, before estimating any terms, is

\[
\varepsilon_N=\zeta(2)p\langle d_N,g_p\rangle_Q+
\sum_{k\ge1}P(k)r_{P,N}(k)
 \left(1-\frac{k\bmod p}{k}\right).
\]

The remainder vanishes below \(p\). Cauchy--Schwarz and \(P(k\ge p)=1/p\) imply

\[
\left|\varepsilon_N-\zeta(2)p\langle d_N,g_p\rangle_Q\right|
\le\sqrt{\varepsilon_N/p}.
\]

Since \(g_p\in W_N\) and \(\|g_p\|_Q^2\le2/(\zeta(2)p)\),

\[
\varepsilon_N\le\sqrt{2\zeta(2)p}\,\alpha_N+
\sqrt{\varepsilon_N/p}.
\]

If \(H\varepsilon_N\ge8\), choose a prime using Bertrand's postulate after
\(n=\lfloor4/\varepsilon_N\rfloor\). Then
\(4\le p\varepsilon_N\le8\) and \(p\le H\). Thus

\[
\varepsilon_N/2\le\sqrt{2\zeta(2)p}\,\alpha_N,
\qquad
\varepsilon_N^3\le64\zeta(2)\alpha_N^2.
\]

The complementary case gives the exact final estimate

\[
\boxed{\quad
\varepsilon_N^3\le
\max\left\{\left(\frac8{N+1}\right)^3,
64\zeta(2)\alpha_N^2\right\}.
\quad}
\]

This is `QSquarefreeFiniteDisplacement.finitePResidual_cube_le_prime_projection`.
Strong convergence of the two actual fits gives

\[
\boxed{\quad
\|r_P\|_P^6\le64\zeta(2)\|P_Wd\|_Q^2.
\quad}
\]

The theorem `QPrimeCarryProjection.primeDisplacement_eq_zero_iff` then proves
\(P_Wd=0\iff d=0\). Its forward direction passes through vanishing of the actual Pareto residual.

## Remaining obligation

The finite decomposition supplies convergence
\(P_{W_N}d_N\to P_Wd\). To finish this route one must establish a cofinal vanishing estimate for these prime components. The CRT identities and the existence of the two projection limits leave that estimate open.

The five new companion modules are `Analysis/NestedOrthogonalDecomposition.lean`, `NumberTheory/PrimeScaleBounds.lean`, `RH/QPrimeProjectionControl.lean`, `RH/QPrimeProjectionLimit.lean`, and `RH/QPrimeCarryProjection.lean`.

The coherent preliminary check `job_REY3FdNJVBFEmXsOSW1KZPMP_XFWBVXg` accepted the general decomposition, finite bound, infinite bound, and conditional zero theorem (10.462 seconds of compiler time). The final import and axiom audit `job_6-gJsxC9DauPzj6uTmUa1wmv8rwW7xrb` then succeeded with exit code 0 and `verified: true` (15.910 seconds of compiler time). It imported all five split modules, including the actual CRT application, and inspected the cited conditional theorem types. These compiler durations exclude workspace recovery and transport delays. The inspected axiom lists contained only `propext`, `Classical.choice`, and `Quot.sound`. Repository publication additionally requires the server checkpoint to validate the aggregate import and architecture.
