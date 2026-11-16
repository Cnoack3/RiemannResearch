# Estermann collision contours and explicit Hurwitz growth transfer

Prepared 16 November 2026, America/Los_Angeles. This is a topical theorem catalog
for the checkpoint containing this file.

## Established contour results

All declarations in this section are proved from standard analytic assumptions,
without an unresolved Estermann growth provider.

| Declaration | File | Exact role |
|---|---|---|
| `Complex.integral_affine_hasDerivAt` | `Analysis/RectanglePoleSubtraction.lean` | Integrates a primitive along an affine segment. |
| `Complex.rectangleIntegral_eq_zero_of_primitive` | same | Boundary primitive and continuity imply zero rectangle integral; no interior holomorphy assumption. |
| `Complex.rectangleIntegral_div_sub_sq_eq_zero` | same | A/(s-p)^2 integrates to zero for p off the boundary, including interior p. |
| `Complex.meromorphicOrderAt_ge_neg_one_of_residue_limit` | same | A finite simple-residue limit implies order at least -1. |
| `Complex.rectangleIntegral'_eq_sum_of_residue_limits` | same | Finite residue accounting allowing removable candidate poles. |
| `analyticAt_estermannMellinCollisionRegularized` | `Analysis/ConreyBaluyotEstermannMellinCollisionShift.lean` | The pole-subtracted kernel is analytic off zero and one in Re(s)>-1. |
| `meromorphicAt_estermannMellinCollisionRegularized` | same | Meromorphy of that kernel on Re(s)>-1. |
| `estermannMellinCollisionRegularized_residue_zero` | same | Its residue at zero remains E_h(0,0). |
| `rectangleIntegral_estermannMellinKernel_diagonal` | same | Exact finite contour formula for the original double-pole kernel. |

Application declarations have namespace
`RiemannResearch.Analysis.ConreyBaluyot`.

For K>0, h a unit modulo K, lambda!=0, -1<a<0, b>1, and T>0, the finite formula is

```text
RectangleIntegral'(Gamma(s)*lambda^(-s)*E_h(s,s), a-i*T, b+i*T)
  = E_h(0,0) + (EulerGamma-log(lambda)-2*log(K))/(K*lambda).
```

The simple-pole residue theorem is used only after subtracting
1/(K*lambda*(s-1)^2). The primitive -1/(K*lambda*(s-1)) shows that the removed
term contributes zero on the closed contour.

## Established finite bound

`norm_estermann_le_hurwitz_sum_product` in
`Analysis/ConreyBaluyotEstermannHurwitzGrowth.lean` proves

```text
|E_h(u,v)| <= K^(-Re(u)-Re(v)) * sum_j |Hurwitz(j/K,u)| * sum_j |Hurwitz(j/K,v)|.
```

It starts from the exact finite Hurwitz identity. It applies to all numerator
classes h modulo positive K, including nonunits; the zero class represents
Hurwitz parameter one.

## Conditional research reductions

| Declaration | File | Unresolved provider |
|---|---|---|
| `estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound` | `Analysis/ConreyBaluyotEstermannMellinCollisionShift.lean` | Closed-strip inverse-quadratic tail for the actual kernel. |
| `estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_polynomial_growth` | same | Actual polynomial growth of the continued Estermann function. |
| `finite_estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound` | `Analysis/ConreyBaluyotEstermannMellinFinite.lean` | Per-summand tails; arbitrary finite complex coefficients and varying moduli/damping are retained. |
| `norm_estermann_shifted_le_of_hurwitz_polynomial_bounds` | `Analysis/ConreyBaluyotEstermannHurwitzGrowth.lean` | Actual polynomial bounds for both shifted Hurwitz factors, uniform in r in [a,b]. |

For the last declaration, degrees n,m give degree n+m and explicit constant

```text
K^(-2*a-Re(alpha)-Re(beta)) * (sum_j C_j) * (sum_j D_j).
```

The shifts may be complex. The estimate is uniform in h for fixed K. Nonnegativity
hypotheses on C,D are unnecessary for the transfer itself: the supplied upper
bounds on norms yield the intermediate nonnegative sums.

## Open analytic work

1. Identify the corrected Euler–Maclaurin representation with Mathlib's
   Hurwitz continuation and prove uniform quadratic growth on fixed strips
   with left endpoint greater than -1.
2. Apply the proved finite transfer and Gamma strip estimate to close the
   distinct and collision global shifts for fixed damping.
3. Establish domination along both actual Gaussian rays, including endpoints.
4. Complete the signed decomposition and arithmetic estimates.
5. Prove a cofinal uniform moment provider and the separate Ingham density provider.

The existing signed Gaussian correction remains unchanged. No unconditional
new density bound or RH conclusion is claimed.

## Evidence

- Finite collision and global reductions: focused Bazel job
  `job_vP2owhl0VsL3LXfGwDv9mTgjoElxOoVV`, succeeded.
  [BuildBuddy log](https://app.buildbuddy.io/invocation/44a23418-c82c-48da-89ed-91a7df57bb3f).
- Finite coefficient assembly, Hurwitz transfer, and imports: Bazel job
  `job_u4Xdfyv8_c9vDE6QVxhoyjsx_j7ZcNj3`, succeeded.
  [BuildBuddy log](https://app.buildbuddy.io/invocation/c4c00b05-cf53-4616-8010-ee8f99ef97e3).
- Nine guarded axiom checks: Bazel job `job_EWdgJI4df7g87j8vbMzi6GUr1-frYVNp`,
  succeeded. Every audited declaration depends exactly on `propext`,
  `Classical.choice`, and `Quot.sound`.
  [BuildBuddy log](https://app.buildbuddy.io/invocation/c1d2e6bf-9541-419f-8e1a-9cbff89e9f84).

The managed publication checkpoint validates the entire project. A focused
check is not a substitute for that checkpoint. Axiom audits do not discharge
the explicit growth hypotheses.

## Sources

- [Baluyot, On the Zeros of Riemann's Zeta-function (2017)](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320),
  equation (3.1.7), Lemma 3.1.3, pp. 95–97: finite Hurwitz identity and contour strategy.
- [DLMF 25.11.6](https://dlmf.nist.gov/25.11.E6): corrected second-order
  Euler–Maclaurin formula for the remaining Hurwitz provider.
