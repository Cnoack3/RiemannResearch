# Annular Lean formalization: source-check evidence

10 October 2026. **All 33 continuation sources passed the combined Lean check.**
The exhaustive axiom audit covered **320 public theorems**, including conditional
theorems. This establishes their stated propositions with their stated
hypotheses; it does not establish the hypotheses of the remaining arithmetic
providers or prove RH.

Later continuation: five exported lattice/energy modules add 49 public
theorems, including the sharp actual lattice bound `10/(27*x^2)`, actual
weighted membership for `a>-2`, analytic correction control on `Re(z)>-2`,
and bounded, convergent critical-energy transfer. `ActualLatticeDecay` is
now discharged. See `RH/AnnularLatticeContinuation20261010.md` for its
separate verification scope.

## Exact verification evidence

| Item | Recorded value |
|---|---|
| Completion evidence | `research/all_check_final_completion.json` |
| Job | `job_-eG4Ca0_gz7zDe3iqG9n98SUin3ERoZv` |
| Result | `state: succeeded`, `classification: success`, `exit_code: 0`, `verified: true` |
| Combined checker SHA-256 | `4a0d7bbd028970cb3a3027421baa458a1eddef5bb80b44cce1f19c4612efe1b1` |
| Audit | `AXIOM_AUDIT_OK: 320 public theorems` |
| Union of theorem axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Repository baseline | `443c8a75da168bb561d0f3ca2298a039d69607ee` |
| Lean | `4.33.0-rc2` |
| Pinned mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |

The combined checker uses all canonical continuation sources, hoists their
external imports, and checks an exhaustive public-theorem audit. It is a
successful source check against the recorded baseline. This document records the source check. Repository integration is independently
validated by the checkpoint introducing these modules; the source-check job
itself is not the repository-build certificate. The final external verification
ledger records that later result and the exact source hashes. The detailed claim-by-claim scope is
in `research/paper_claim_coverage.md`.

## Checked improvements

- Weighted Mellin evaluation and every derivative evaluation have explicit
  continuity bounds. Genuine finite-energy extremizers prove the derivative
  constants optimal. Negative weights give uniform evaluations and derivative
  jets at full-zero coordinates, conditional on genuine vector membership.
- The actual prime-power sequence is constructed, with exact raw-psi cell
  assembly and initial energy 1. The actual second-Riesz convolution, centered
  Mellin identity, and `ActualRieszMellinProvider` are proved on `Re(s)>1`.
  The actual centered annular Mellin identity is also proved on that domain.
- Annular support, nonnegativity, sharp maximum `7/24`, mass `7/64`, square
  mass `35/1536`, centering, and the actual finite-integral Gram identities are
  proved. These include the signed residual identity and ratio-eight kernel
  vanishing, with equality at the boundary.
- The canonical twin-prime Euler product converges positively, with
  `1/2 <= C2 <= 11011/16384` and a rational finite-product tail certificate.
  All four explicit logarithm hypotheses are removed from the model-coefficient
  bound, strengthened to `cW < -51611/1536000 < -1/32`.
- Every finite actual annular truncation belongs to every weighted Hilbert
  space `Ha`, with an explicit norm envelope and entire Mellin transform. The
  envelope grows with the cutoff and does not give infinite-vector control.
- General filters are nonzero on `Re(s)>0`; the meromorphic annular expression
  has the proved pole order at an actual zero, and RH is equivalent to its
  specified holomorphy criterion. Smoothing-order coupling is uniform in the
  order, with sharper rational Gaussian coefficients.

## Analytic obligations still open

1. **Actual infinite-vector control and prime gaps:** unconditional gap inputs,
   geometric tails, `ActualArithmeticGridLogBound`, transfer to arbitrary real
   cutoffs, and useful quantitative control of the actual centered vector in a
   topology where full-zero evaluations are continuous.
2. **Continuation and full-zero data:** extend the actual initial-half-plane
   identity to neighborhoods used by the membership obstruction; construct
   `FullZeroData` with true multiplicities and `ZeroSupremumProvider`; prove
   actual growth detection, all-damping/critical-energy equivalence, stable
   dilation bounds, and `ResidualZeroGrowthProvider`.
3. **Complete spectral formulas:** logarithmic Riesz convolution, actual residue
   values, `ActualRieszExplicitFormulaProvider`,
   `ActualAnnularExplicitFormulaProvider`, bounded remainders, absolute
   convergence, `AnnularSupportHeightProvider`, and the weight transform's
   entire removable extension. The checked centered Mellin provider supplies
   only the initial identity.
4. **Spectral averaging and prime-square shifts:** actual Fourier/Bohr and
   autocorrelation identities, sinc resolution, raw mean squares, unsmoothed
   tails, Abel averaging, `ActualAnnularSpectralProvider`, and the PNT-based
   prime-square limiting shifts `1` and `8/15`, including higher powers.
5. **Kernel, spline, and lattice analysis:** evaluated Riesz/background kernels,
   annular diagonal transformations and endpoint weights, weighted-PNT
   diagonal asymptotics, `C^1`/distributional spline properties, actual Fourier
   formulas, Fourier/Poisson lattice identities, additive Parseval,
   high-frequency envelopes, and central-window reduction.
   The scalar `ActualLatticeDecay` obligation is discharged by the later
   annular lattice continuation; the separate Fourier identities remain open.
6. **Actual model asymptotics:** `TriangularSingularSeriesProvider`, real
   interpolation, exact convolution transport, weighted-PNT model estimates,
   integral identification of `I` and `J`, `ModelConvergentRemainder`, and
   `ActualModelLogBound`. Negativity of the displayed coefficient alone does
   not identify it as the actual model slope or prove the actual residual floor.
7. **Twisted and zero-free estimates:** `ActualTwistedMellinProvider`,
   `ActualTwistedExplicitFormulaProvider`, the actual Fourier integral identity,
   complete zero-free input, `ActualZeroFreeEnvelopeProvider`, and energy-tail
   integration. Estimates at weight `x^-3` do not supply the critical `x^-2`
   bound.
8. **The decisive arithmetic estimate:** `ActualRHEnergyCriterion` and
   `ActualSignedResidualUpperBound` for every `X>=2`, with the full signed
   aggregate, diagonal, prime powers, singleton terms, comparable-scale support,
   and terminal cutoff. The checked RH/residual equivalence retains its model
   and energy premises. The spectral residual limit likewise retains its two
   actual-limit premises.

The main quantitative research target remains control of the actual centered
arithmetic vector, rather than only finite truncations or response kernels.
The checked results isolate the exact arithmetic and analytic premises needed
to connect primes, full-zero coordinates, and RH.
