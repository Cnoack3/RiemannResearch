# Actual damped prime operator: construction, nuclear certificate, and continuation

Date: 2026-11-16 UTC; continuation of the November 15 handoff.
Development base: `83f7729300d3292343129382f43502a9ec364455`.
Input: `Prime_Side_Weil_Factorization_Continuation_2026-11-15(1).md`.
Earlier formal checkpoint: `b2e18509`.

## Result and scope

The actual damped synthesis map and the actual signed, two-sided separated prime
operator have now been constructed. For every complex L² function supported
almost everywhere in a bounded interval, the synthesis has square-summable
columns when \(\sigma>1/2\). When \(\sigma>1\), the prime operator has an
absolutely summable rank-one representation, is self-adjoint, and agrees
entrywise and on every finite coordinate form with the previously formalized
von Mangoldt prime kernel.

This completes the main construction and nuclear-certificate tasks in
Priorities 1–2 of the continuation. Smoothness and nonnegativity of the bump
are unnecessary for these conclusions. The exact support identity holds for
every real translation, as an identity of bounded operators.

The endpoint is an explicit nuclear representation, the standard trace-class
criterion on a Hilbert space. A separate singular-value or trace-norm API is
not introduced. No positivity of the completed Weil form, unconditional
factorization through a positive operator, or RH theorem follows here.

## Definitions and conventions

Let \(H=L^2(\mathbb R,dx;\mathbb C)\), \(E=\ell^2(\mathbb N;\mathbb C)\), and
suppose \(\phi\in H\) satisfies \(\phi(x)=0\) almost everywhere for \(|x|>r\).
The code uses the translation
\[
(S_a f)(x)=f(x-a),\qquad \tau_a=S_{-a}.
\]
The natural-number coordinates 0 and 1, and all non-prime-power coordinates,
have zero weight. Thus using all natural coordinates only appends zero columns
to the prime-power synthesis.

Define
\[
a_\sigma(m)=\sqrt{\Lambda(m)}m^{-\sigma},\quad
u_\sigma(m)=a_\sigma(m)S_{\log m}\phi,\quad
E_\sigma(m)=\Lambda(m)m^{-2\sigma}.
\]
The bounded map \(J_\sigma:E\to H\) is constructed as the adjoint of the bounded
analysis map \(f\mapsto(\langle u_\sigma(m),f\rangle)_m\). Lean proves
\[
J_\sigma e_m=u_\sigma(m),\qquad
J_\sigma c=\sum_m c_m u_\sigma(m),\qquad
\sum_m\|J_\sigma e_m\|^2=\|\phi\|^2\sum_m E_\sigma(m)<\infty.
\]
The vector sum is a genuine `HasSum`, not an unproved convergence assertion.

Write
\[
T_a=J_\sigma^*\tau_aJ_\sigma,\qquad
w_n=\frac{\Lambda(n)}{\sqrt n},\qquad
P_{\sigma,\phi}=-\sum_{n\ge2}w_n(T_{\log n}+T_{\log n}^*).
\]
The Lean definition `primeOperator` is a `tsum` for \(\sigma>1/2\), but its
proved summability and all asserted operator identities below require
\(\sigma>1\) and the stated support hypothesis. Nothing is inferred from a
`tsum` definition outside that proven regime.

## The support and damping mechanism

For every real \(a\), let \(P_{r,a}\) be the coordinate mask retaining
\(m\ge2e^{a-2r}\). Lean proves the exact identity
\[
T_a=T_aP_{r,a}.
\]
For an excluded column, every possible nonzero row has disjoint translated
support. The proof handles null sets in L² and the zero columns explicitly.

A flexible arithmetic estimate replaces the logarithmic-tail integral route.
For \(1/2<\beta\le\sigma\) and \(Y>0\),
\[
\sum_{m\ge Y}\Lambda(m)m^{-2\sigma}
\le Y^{-2(\sigma-\beta)}
   \sum_m\Lambda(m)m^{-2\beta}.
\]
This follows from an elementary pointwise power inequality and Mathlib's
absolute convergence theorem for the von Mangoldt Dirichlet series.
It requires neither PNT nor RH.

Taking \(\beta=\sigma/2\), valid for \(\sigma>1\), gives
\[
\|1_{m\ge Y}u_\sigma\|_{\ell^2(H)}
\le Y^{-\sigma/2}\|u_{\sigma/2}\|_{\ell^2(H)}.
\]
At \(a=\log n\), the support threshold is \(Y=c_rn\), where
\(c_r=2e^{-2r}>0\). The weighted nuclear cost is therefore dominated by a
constant times
\[
\Lambda(n)n^{-(\sigma+1)/2},
\]
whose sum converges for \(\sigma>1\).

This is a simpler route to the same target threshold. It is not a claim
to improve the sharp asymptotic logarithmic-tail estimate in the markdown.

## Nuclear construction

The reusable theorem `product_nuclear_representation` constructs an absolute
rank-one expansion for
\[
A_u\,U\,A_v^*,
\]
where \(A_u,A_v\) are analysis maps of square-summable columns and \(U\) is a
linear isometry. Bessel's inequality, a Hilbert basis, and Cauchy–Schwarz give
a total rank-one cost at most \(\|u\|_{\ell^2}\|v\|_{\ell^2}\).

Applying this after the support identity yields an expansion of each \(T_{\log n}\)
with cost at most
\[
\|u_\sigma\|_{\ell^2(H)}
\|1_{m\ge c_rn}u_\sigma\|_{\ell^2(H)}.
\]
The symmetrization theorem preserves the minus sign and both translation
directions. A further theorem flattens the absolutely summable double family
into a single rank-one expansion of \(P_{\sigma,\phi}\).

The basis-free endpoint is:

```lean
RiemannResearch.RH.WeilDampedSynthesis.primeOperator_nuclear
  {σ r : ℝ}
  (hσ : 1 < σ) (φ : L2)
  (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
  ∃ s : Set L2, ∃ p q : ℕ × (s ⊕ s) → Coeff ℕ,
    Summable (fun z => ‖p z‖ * ‖q z‖) ∧
    HasSum (fun z => rankOne (p z) (q z))
      (primeOperator (by linarith : 1 / 2 < σ) φ)
```

Here `rankOne p q x = inner ℂ q x • p`.
The index set is a Hilbert-basis subtype; absolute summability supplies the
usual countably supported nuclear expansion. No basis or operator-existence
hypothesis is required from the caller.

## Exact arithmetic kernel and finite forms

Define the actual autocorrelation
\[
C_\phi(t)=\langle\phi,\tau_t\phi\rangle.
\]
Lean proves \(C_\phi(t)=0\) whenever \(|t|>2r\). With the existing kernel
\[
K_C(d)=-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 \bigl(C(\log n-d)+C(-\log n-d)\bigr),
\]
the exact matrix formula is
\[
\langle e_k,P_{\sigma,\phi}e_m\rangle
 =a_\sigma(k)a_\sigma(m)
 K_{C_\phi}(\log m-\log k).
\]
This holds for all natural indices, including the zero-weight coordinates.
The finite sesquilinear identity holds for arbitrary finite sets \(s,t\)
and arbitrary complex coefficient functions \(c,d\):
\[
\left\langle\sum_{k\in s}c_ke_k,
 P_{\sigma,\phi}\sum_{m\in t}d_me_m\right\rangle
=\sum_{k\in s}\sum_{m\in t}
 \overline{c_k}d_m\,a_\sigma(k)a_\sigma(m)
 K_{C_\phi}(\log m-\log k).
\]
The existing support-cutoff kernel theorem supplies the finite arithmetic
cutoff. Both signs and the ratio-shifted support windows are retained.
Self-adjointness is proved separately and is not treated as positivity.

## Modules and exact entry points

All eight modules are exported by `RiemannResearch.lean`.
There are 75 new named theorems.

| File | Main declarations | Theorems |
|---|---|---:|
| `Analysis/SquareSummableSynthesis.lean` | `synthesis_hasSum`, `synthesis_comp_projection`, `synthesis_column_square_sum` | 15 |
| `Analysis/NuclearSynthesis.lean` | `analysis_orthonormal_tsum_le`, `product_nuclear_representation` | 8 |
| `Analysis/NuclearSeries.lean` | `symmetrized_nuclear_representation`, `nuclear_series_flatten` | 4 |
| `RH/WeilDampedWeights.lean` | `energy_summable`, `tailEnergy_le`, `prime_majorant_summable` | 11 |
| `RH/WeilDampedSynthesis.lean` | `J_hasSum`, `J_column_square_sum`, `support_projection_identity` | 15 |
| `RH/WeilDampedPrimeOperator.lean` | `weighted_tail_summable`, `primeTerm_norm_summable`, `primeOperator_hasSum` | 9 |
| `RH/WeilDampedPrimeKernel.lean` | `primeOperator_entry`, `primeOperator_finite_form`, `primeOperator_adjoint` | 11 |
| `RH/WeilDampedPrimeNuclear.lean` | `primeOperator_nuclear_representation`, `primeOperator_nuclear` | 2 |

Analysis declarations use namespace
`RiemannResearch.Analysis.SquareSummableSynthesis`.
Arithmetic weights use `RiemannResearch.RH.WeilDampedWeights`.
The remaining declarations use `RiemannResearch.RH.WeilDampedSynthesis`.

## Research agenda after this checkpoint

| Task | Current status | Next concrete obligation |
|---|---|---|
| Actual synthesis, \(\sigma>1/2\) | Lean proved | Optional bridge to a reusable named Hilbert–Schmidt predicate |
| Exact support projection | Lean proved for every real shift | Optional range-support statement; not required by the proved operator identity |
| Separated prime operator, \(\sigma>1\) | Lean proved: absolute operator series and nuclear expansion | Optional trace-norm/singular-value API and quantitative global cost theorem |
| Exact finite prime kernel | Lean proved | Instantiate a concrete bump and certify integral entries and finite spectral error bounds |
| Polar and archimedean sectors | Still open in this construction | Construct their actual forms/operators with compatible domains and the same sign conventions |
| Completed Weil-form identification | Still open | Prove equality to the completed distribution on the required full test class |
| Positive completed factorization | Still open | Supply a positive factor or a signed defect bound that tends to zero with every required quantifier |
| Removing damping / \(\sigma\le1\) | Not established here | Determine cancellation in the completed form before asserting boundedness or taking a limit |
| RH deduction | No new unconditional provider | Connect the full-class completed positivity result to the existing criterion only after all analytic hypotheses are discharged |

The canonical next analytic task is to construct and identify the actual
completed form, including polar and archimedean contributions, in the same
coefficient and translation conventions. A theorem only about its separated
prime sector cannot supply completed positivity.

Finite matrices can now be tied to an actual infinite operator, but numerical
positive semidefiniteness, finite prime cutoffs, and convergence at fixed
\(\sigma>1\) do not by themselves prove the required full-class or undamped
positivity. No lower-damping obstruction theorem or new certified numerical
Galerkin experiment is claimed in this checkpoint.

## Verification and external checks

Focused saved-module verification succeeded with Bazel and BuildBuddy:
`job_WAubQjhAs3XSxZ48sTfhHHhxZhIHavYM`, exit code 0, 80.105 seconds.
The snippet imported the final kernel and nuclear modules and checked the
principal declarations. BuildBuddy invocation:
https://app.buildbuddy.io/invocation/131c72b5-5a8e-49e7-9445-61e39f9c369d

The source audit found no added axioms, unfinished proofs, or unsafe declarations.
Publication uses the managed checkpoint, which performs the repository's full
Bazel validation and integration checks before pushing; its receipt identifies
the published commit and full-build evidence.

Wolfram independently confirmed the logarithmic-tail integral and the exponent
normalization underlying the comparison bound. These checks guided the proof;
the Lean proof uses Mathlib identities and does not depend on numerical output
or imported computer-algebra assertions.

## Literature and provenance

- The attached November 15 continuation and the
  [earlier factorization catalog](THEOREM_CATALOG_PRIME_SIDE_FACTORIZATION_20261115.md)
  specify the operator, sign, and remaining RH obligations.
- Jordan Bell, [Trace class operators and Hilbert-Schmidt operators](https://jordanbell.info/LaTeX/mathematics/traceclass/),
  Theorem 18: standard Hilbert–Schmidt product strategy. The rank-one construction
  used here is proved in Lean.
- Connes–Consani, [Weil positivity and trace formula, the archimedean place](https://arxiv.org/abs/2006.13771):
  relevant local archimedean context; it is not used as a provider of full
  completed positivity.
- Suzuki, [On the Hilbert space derived from the Weil distribution](https://arxiv.org/abs/2301.00421):
  related Hilbert-space constructions; an RH-dependent construction cannot
  be used as an unconditional positivity input.
