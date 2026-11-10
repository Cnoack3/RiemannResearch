# Montgomery gamma: exact poles and a cubic spatial matrix bound

Date: 2026-11-10. Source baseline: `cbec05a996ad24c24329f8b9f1a85d868664eec7`.
Continuation of the user-provided `MontgomeryGammaAudit20261110.md`.

## Scope

This development proves the explicit spatial-kernel Taylor and Schur estimates
that the audit previously supplied only on paper. It also integrates the earlier
checked, unpublished pole/gamma module and its compact-C2 regularity adapter.
It does **not** prove Montgomery's pair correlation conjecture or RH.

The matrix theorem below concerns the explicitly defined spatial matrix E.
The continuation now proves its exact identification with the centered complete
actual-zero matrix and evaluates the full diagonal, including both poles,
the c_F/log T correction, and an explicit O(1/(T^2 log T)) remainder.
See [the current matrix/transfer/prime catalog](THEOREM_CATALOG_MONTGOMERY_MATRIX_TRANSFER_PRIMES_20261110.md).
The raw-ordinate transfer and complete high-support arithmetic estimate remain
separate substantive research obligations; their new partial results are recorded there.

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

## Updated obligation status

1. **Closed: actual off-diagonal identity.** The new
   PrimeBandlimitedMatrix module proves centeredZeroEntry_eq_spatial and
   actual_zero_centered_quadratic_bound for real even compact C2 zero-mean
   windows and homogeneous positive integer blocks, T >= 4, 2D <= T.
   The shifted gamma reality/reflection and affine change of variables are proved.
2. **Closed: diagonal evaluation.** SechGammaDiagonal, PrimeBandlimitedDiagonal,
   and PrimeBandlimitedMatrixDiagonal prove the exact regulated formula and
   normalizedDiagonal_exact, retaining the pole term even without zero mean.
   Under zero mean the remainder after F(0)+c_F/log T is at most
   11 M_1(F)/(48 T^2 log T). The corrected actual-zero quadratic theorem
   assembles this with the constant-72 spatial estimate.
3. **Research open: full transfer to raw ordinates.** New averaged one-point
   criteria transfer actual hard-cutoff complex pairings to raw pairings and
   remove Gaussian damping. Their budget decay remains an explicit hypothesis.
   A proved obstruction shows all-frequency positive-budget decay is equivalent
   to the critical-line assertion for actual positive zeros. The separate
   full-height smoothed-matrix comparison still requires a justified tail estimate.
4. **Research open: complete signed prime correlations above support one.**
   Exact endpoint/prefix identities and an unconditional odd-gap raw bound are
   now proved. The actual PNT gives R_N(h(N))/N -> -1 for every eventually odd
   gap sequence h(N) <= N. Even-gap cancellation remains missing from the target

       C(N,H) = -HN log H + o_epsilon(HN log N),

   uniformly for N^epsilon <= H <= N^(1-epsilon), together with the diagonal
   estimate and the stated prime/zero transfer hypotheses. The coarse H^3
   endpoint bound cannot be discarded throughout this range.
5. **Research/provider open: transition control.** Retain the corrected
   low-support uniform error and control concentration near |alpha|=1 before
   asserting a full raw test-function limit.

The complete statements, dependencies, and new verification records are in
THEOREM_CATALOG_MONTGOMERY_MATRIX_TRANSFER_PRIMES_20261110.md. The development
verification records below document the earlier spatial-only stage.

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
