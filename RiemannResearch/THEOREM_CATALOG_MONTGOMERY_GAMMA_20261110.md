# Montgomery gamma: exact poles and a cubic spatial matrix bound

Date: 2026-11-10. Source baseline: `cbec05a996ad24c24329f8b9f1a85d868664eec7`.
Continuation of the user-provided `MontgomeryGammaAudit20261110.md`.

## Scope

This development proves the explicit spatial-kernel Taylor and Schur estimates
that the audit previously supplied only on paper. It also integrates the earlier
checked, unpublished pole/gamma module and its compact-C2 regularity adapter.
It does **not** prove Montgomery's pair correlation conjecture or RH.

The matrix theorem below concerns the explicitly defined spatial matrix E.
There is no new checked theorem identifying E with the centered complete
actual-zero matrix. This identification and the diagonal asymptotic remain
formalization obligations. The raw-ordinate transfer and the high-support
arithmetic estimate are separate substantive research obligations.

## Exact definitions and main theorem

For t > 0 set

    A(t) = 1/(2 sinh t) + 1/(4 cosh(t/2)^2).

This is exactly the sech-modified Weil gamma kernel, as established by
`PrimeBandlimitedWeil.sechGammaKernel_split`.
For a real continuous function F define

    mu_j(F) = integral_{-1}^1 x^j F(x) dx,
    M_2(F) = integral_{-1}^1 x^2 |F(x)| dx,
    I(F,T,u) = integral_{-1}^1 F(x) A(u+x/T) dx.

Let F be even with mu_0(F)=0. Let S be a finite set of positive integers
bounded by D, and suppose T > 1 and 2D <= T. Define the real symmetric matrix

    E(n,n) = 0,
    E(n,m) = -I(F,T,|log n-log m|)/(T log T),  n != m.

For arbitrary complex coefficients c, the checked declaration
`SechGammaMatrix.quadratic_bound` states

    |sum_{n,m in S} c_n conjugate(c_m) E(n,m)|
       <= 72 M_2(F) (D/T)^3 / log T * sum_{n in S} |c_n|^2.

The theorem has no hypotheses about zeta zeros, primes, RH, pair correlation,
or a limiting point process. It requires no positivity of F. Repeated integer
indices must be combined before forming the finite set S. The diagonal is
zero by the definition of E; this theorem does not justify replacing the
diagonal of an actual-zero matrix by 1.

## Exact remainder before the bound

`SechGammaBounds.window_exact_remainder` keeps both signed low moments:

    I(F,T,u) - A(u) mu_0(F) - A'(u)/T mu_1(F)
      = integral_{-1}^1 F(x)[A(u+x/T)-A(u)-(x/T)A'(u)] dx.

For u > 0, T > 0 and 1/T <= u/2, the absolute value of this exact remainder
is at most 24 M_2(F)/(T^2 u^3). Evenness implies mu_1(F)=0 in Lean.
Normalization by T log T supplies the third inverse power of T.

The derivative bound |A''(t)| <= 6/t^3 is proved from the explicit derivatives.
The proof establishes cosh(x) >= 1+x^2/2 and 6 sinh(x) >= x^3 for x >= 0.
For the sech-squared contribution, a polynomial inequality gives
t^3 <= 8 cosh(t/2)^2. No decimal approximation to an exponential maximum
is used.

The finite inverse-cube tail is bounded with its endpoint retained:

    sum_{k=0}^{N-1} 1/(k+2)^3 <= 1/2 - 1/[2(N+1)^2].

This yields the row bound 3 on distinct integer gaps. The logarithmic
separation |n-m| <= D |log n-log m| and the existing symmetric Schur
quadratic inequality complete the constant 72 estimate.

## Declaration map

| File | Principal declarations | Scope |
| --- | --- | --- |
| `Analysis/PrimeBandlimitedGamma.lean` | `pole_integrand_cancel`, `pole_pair_frequencyTest`, `pole_pair_frequencyTest_eq_zero`, `constant_pole_quadratic` | Both poles evaluated exactly; their matrix is rank one. |
| Same file | `actual_zero_sum_homogeneous_complete` | Exact complete actual-zero sum equals pole plus gamma on an equal-Omega block, with the stated isolation hypotheses. |
| Same file | `gammaContribution_diagonal_spatial`, `sechGammaKernel_split` | Exact regulated real diagonal and exact spatial kernel split. |
| Same file | `gamma_kernel_window_bound` | New normalized window bound directly for the actual sech-modified Weil gamma kernel. |
| `RH/WeilGammaFourierAdapter.lean` | `gamma_spatial_of_contDiff_two` | Compact C2 support discharges analytic regularity/decay inputs; even real part remains explicit. |
| `Analysis/SechGammaBounds.lean` | `hasDerivAt_kernel`, `hasDerivAt_first`, `second_abs_le`, `iteratedDeriv_two`, `taylor_remainder_le` | Explicit derivatives and the constant 24 Taylor estimate. |
| Same file | `window_exact_remainder`, `window_remainder_bound`, `first_moment_eq_zero_of_even`, `normalized_window_bound_of_even` | Signed moments, even-window cancellation, and normalized integral decay. |
| `Analysis/IntegerGapSchur.lean` | `tail_sum_with_remainder`, `cube_sum_le`, `row_le`, `quadratic_le` | Exact finite tail, row mass at most 3, and coefficient-sensitive Schur assembly. |
| `Analysis/SechGammaMatrix.lean` | `log_gap_mul_bound`, `entry_bound`, `quadratic_bound` | Explicit spatial matrix with its cubic rate and constant 72. |

Namespaces are under `RiemannResearch.Analysis`, except the adapter under
`RiemannResearch.RH.SignedWeilCorrelation`.

## Remaining obligations

1. **Formalization open: actual off-diagonal identity.** Extend/symmetrize the
   spatial gamma adapter for shifted real tests, retain the full zero and pole
   identity, and prove the change of variables giving (4.2)--(4.3) of the audit.
   Establish any reality/symmetry needed to identify the complex zero matrix
   with the real spatial matrix. Only then apply `quadratic_bound` to that matrix.
2. **Formalization open: diagonal evaluation.** Prove the exact regulated
   identities (6.2)--(6.3), then the bound (6.4). The generally nonzero
   c_F/log T correction has not been removed by zero ordinary moments.
3. **Research open: transfer to raw ordinates.** Neither the full smoothed
   complex-zero sum nor Gaussian Fourier-damping removal supplies the
   hard-cutoff, ordinate-only Montgomery limit. Horizontal displacement,
   fixed-width sech smoothing, and height cutoff transfers need justified
   hypotheses and estimates.
4. **Research open: signed prime correlations above support one.** In the
   repository's centered short-interval notation the target remains

       C(N,H) = -HN log H + o_epsilon(HN log N),

   uniformly for N^epsilon <= H <= N^(1-epsilon), together with the diagonal
   estimate and the stated prime/zero transfer hypotheses. Homogeneous
   multiplicative cancellation does not prove this additive correlation bound.
5. **Research/provider open: transition control.** Retain the corrected
   low-support uniform error and control concentration near |alpha|=1 before
   asserting a full raw test-function limit.

For a degree-k polynomial in integer modes bounded by D_0, the length entering
the matrix theorem can be D_0^k. More prime-torus coordinates do not remove
the requirement that this full length be at most T/2.

## Provenance and verification policy

The user's audit supplies the analytic argument in Sections 4--5 and identifies
the unresolved transfers in Sections 8--9. The exact Guinand--Weil formula is
provided by the repository's existing checked development, with the conventions
of Garrett, *Guinand's explicit formula*, Theorem 0.0.1, and
Iwaniec--Kowalski, *Analytic Number Theory*, Theorem 5.12. DLMF 5.9.16 supports
the digamma representation used by the spatial adapter:
https://dlmf.nist.gov/5.9.E16

The corrected low-support formula, including its uniform error, is in
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, Section 3:
https://arxiv.org/html/2501.14545v3#S3
That paper is a research reference here, not an added Lean axiom.

Publication is gated by the server's full incremental Bazel/BuildBuddy target
`//:RiemannResearch`, including all source modules. The release response records
the terminal checkpoint job and exact published commit. Snippet checks alone
are not represented as whole-project validation. No unfinished proof or
domain-specific axiom is introduced by these additions.

## Development verification record

- Combined proof candidate: `job_7J3nNtuMoITAGs6-gHE2AaHn-agPapl1`, terminal
  `succeeded`, `verified=true`, Bazel/BuildBuddy.
  Evidence: https://app.buildbuddy.io/invocation/04bc7e0c-330c-4821-9ed9-9388b339da5a
- Saved-module check: `job_H8fQ8Ll0-kkDB-TPCVm7sqOH5DtGsPns`, terminal
  `succeeded`, `verified=true`, exit code `0`.
  A temporary importer checked `PrimeBandlimitedGamma` and `SechGammaMatrix`
  and all their transitive imports. The log records separate compilation of
  `SechGammaBounds`, `IntegerGapSchur`, `SechGammaMatrix`, and
  `PrimeBandlimitedGamma`. The temporary importer was removed afterward.
  Evidence: https://app.buildbuddy.io/invocation/aacbc79b-d2a6-43cf-bb7b-3d1bfd91f299
- Server-reported duration for the saved-module check: 263.841 seconds.
  This is not a measurement of pure kernel CPU time; workspace setup and
  subsequent polling delays are separate.
- These records establish the development/module scopes above. The final
  publication checkpoint additionally validates the complete repository.
