# Ramanujan dual development, transfers 21–30

Date: 23 October 2026. Continuation of transfers 1–20 at main `44ac993267cf4474cb04808a1745dc6f27bedaf4`.

Each numbered transfer is verified by Lean and published in its own commit. All full RH equivalences retain the explicit open converse provider `hBaezDuarte : RiemannHypothesis → Pareto.BaezDuarte.NaturalApproximation`. No proof of RH is claimed. Original positive residue coefficients target **−μ(m)**; the packet coefficients are a different finite Möbius transform.

## 21. Simultaneous prescribed arithmetic coefficients

General arbitrary real inner-product-space theorem: exact double-inverse correction, feasibility, full error completion, and uniqueness. The Ramanujan source matrix is `B H⁻¹ Bᵀ`, automatically positive definite for distinct in-stage original coordinates. The exact constrained error is `1 − M_n + δᵀ(B H⁻¹ Bᵀ)⁻¹δ`, retaining all cross couplings. No nonsingularity provider is assumed.

Isolated Lean verification: `job_2E45CyATyuc2xgr3bfpdhXPhtfFiBuUe`, succeeded, server 5.152 s.

## 22. Exact finite Möbius pinning preserves approximation

An explicit continuous finite coordinate projection repairs the selected original coefficients to −μ. Once all selected conductors enter the stage, the repaired vector has a genuine same-stage packet expansion. Its error equals `1 − M_n + ‖repair(1 − F_n)‖²` and lies between `1 − M_n` and `(1 + ‖repair‖²)(1 − M_n)`. Thus its zero-error criterion, along any cofinal nontrivial filter, is equivalent to canonical saturation and convergence of all original coefficients to −μ. The forward implication to RH is proved; the RH converse explicitly requires hBaezDuarte.

Isolated Lean verification: `job_iIMPVEIcm0IyhgHNn1zCJV-mSShvsMyb`, succeeded, server 9.289 s.

## 23. Complete arithmetic feasibility, including singular constraint systems

Arbitrary repeated and offstage conductor requests are feasible exactly when duplicate requests agree and offstage targets vanish. The source rows have full rank exactly when the conductors are distinct and all belong to the stage. Feasibility alone constructs a source-Gram normal solution even when that Gram is singular. The signed normal pairing gives the exact minimum; the full Gram displacement gives completion and uniqueness of the optimizing packet array (multipliers need not be unique). For targets −μ, feasibility reduces exactly to vanishing of every offstage Möbius value.

Isolated Lean verification: `job_YBlm1lhRYXjuEzH9qKerqpNmzAX2iDRo`, succeeded, server 5.766 s.

## 24. Exact inverse-Gram normal-defect certificates

For every finite independent dictionary, arbitrary target and arbitrary trial, δ = G a − b satisfies `error(a) = error(a*) + δᵀG⁻¹δ`. The defect equals the full squared synthesis displacement, vanishes exactly at the optimizer, and has an exact dual completion and directionwise Cauchy–Schwarz certificate. The actual Pareto packet source is Λ; Q uses its distinct actual source. Both arithmetic normal defects and full trial error identities are exposed.

Isolated Lean verification: `job_BQOGehNw_RyxljlwDZx2zOnas4E7lbbZ`, succeeded, server 6.316 s.

## 25. Arbitrary trial arrays and the two-measure convergence criterion

Stages and trial coefficients may vary along any cofinal nontrivial filter. Trial norm tends to zero iff canonical limiting energy is zero and the complete inverse-Gram defect tends to zero, separately for P and Q. For the same physical trial, P and Q convergence are equivalent without cofinality or optimality, and the exact metric-correction budget is proved. Conditional RH-and-defect versions keep hBaezDuarte explicit. The underlying nonnegative-budget convergence lemmas are reusable Analysis declarations.

Isolated Lean verification: `job_wHo0xWb1-Ei7SRxqom5JLKbnl907hRYn` (25–26 together), succeeded, server 6.516 s.

## 26. Positive limiting coordinate capacity and the full closed affine optimum

The actual coordinate representer is the projection of −mobiusRieszHilbert. Its capacity increases to a strictly positive finite limit, with an explicit divisor-sum upper bound and exact missing-capacity squared norm. Along any cofinal filter, varying prescribed values tending to t produce candidates tending to `P∞1 + (t − c∞(m))/κ∞(m) · P∞R_m`. Over the entire closed legal space with coefficient m fixed to t, the exact error is `E∞ + (t − c∞(m))²/κ∞(m) + ‖y − candidate∞‖²`. Thus the displayed limit is the unique global affine optimizer. No RH hypothesis is used.

Isolated Lean verification: `job_wHo0xWb1-Ei7SRxqom5JLKbnl907hRYn` (25–26 together), succeeded, server 6.516 s.

## 27. Automatic Cauchy and Mellin nonsingularity

Over an arbitrary field, with all denominators nonzero, the Cauchy matrix has nonzero determinant iff both node and pole maps are injective. The proof constructs the polynomial numerator of a kernel vector and recovers its coefficients at the poles. In the strict complex half-plane the Mellin Cauchy-Gram is nonsingular exactly when the test-point map is injective. Thus repeated points are its only singularity mechanism, and all later distinct-point certificates discharge the old determinant hypothesis internally.

Isolated Lean verification: `job_L48JqQKbkn2KsFejsPnWTJtbwR1PE_Mu` (27 and 30 together), succeeded, server 6.054 s.

## 28. Full Mellin enlargement and explicit complex Schur updates

Finite pushforward preserves the complete sesquilinear quadratic form. Enlarging any nonsingular test family changes its capacity by exactly the full Gram quadratic of the inverse-coefficient displacement. Strict-half-plane prefix capacities are monotone for every injective sequence and arbitrary complex source signature. A new point has an explicit complex coefficient update and exact capacity gain `‖innovation‖² / Re(Schur)`, with positive denominator and strict gain iff the innovation is nonzero. The actual-zero packet specialization discharges determinants from distinctness and retains the entire Mellin integral remainder.

Isolated Lean verification: `job_RB5nSR-HYdTriPJIvjqurfo9bEHDqlim` (28–29 together), succeeded, server 6.102 s.

## 29. Strong arbitrary-filter exact-head and full-tail-product criteria

For arbitrary filters, with neither cofinality nor NeBot, frequent simultaneous exact-head trials and arbitrarily small full tail products are equivalent to zero canonical residual together with frequent exact-head trials. This gives RH in the forward direction without a converse provider. Under eventual exact heads on a nontrivial filter, product convergence to zero is equivalent to saturation and, with hBaezDuarte, RH. Moving budgets only need dominate the full trial error frequently; nonzero residual forces cofinal exact-head trial error to diverge. Frequent bounded-error and divergence statements also avoid unnecessary NeBot assumptions. The full physical residual tail and entire packet Gram displacement are preserved. No existence of the required trial families is asserted.

Isolated Lean verification: `job_7GTWHa9Qm893S0OwfyXUgT5-_3sJ3AX7` (strengthened 29–30 together), succeeded, server 6.281 s.

## 30. Exact finite products and the countable product budget

Over any field, the mixed inverse Cauchy pairing has an exact finite product formula, proved by a rank-one determinant identity. For distinct strict-half-plane complex test points, the actual zero-source Mellin capacity is exactly `1 − ∏ |(z−1)/z|²`, with no determinant provider. Actual zero families give the complete canonical error `1 − M_n = 1 − product + full Mellin remainder`, and arbitrary competitors retain the additional entire packet Gram displacement. This yields mass bounds, limiting energy floors, and concrete finite-family zero exclusion.

For every injective strict-half-plane sequence, the prefix products are decreasing, converge to their infimum, and have a limit in [0,1]. For an actual zero sequence, every finite packet mass and the limiting captured mass are bounded by that product limit. The limit is strictly positive, since one legal packet stage already has positive captured mass. These are inequalities with complete residual budgets; no assertion that the zero tests exhaust the canonical residual is used.

Isolated Lean verification: `job_7GTWHa9Qm893S0OwfyXUgT5-_3sJ3AX7` (strengthened 29–30 together), succeeded, server 6.281 s.

The finite-product strategy is motivated by J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann Hypothesis*, https://arxiv.org/abs/math/9910055. Wolfram's symbolic simplification returned zero for the scalar Cauchy rank-one identity; all statements above are proved and checked in Lean independently of that symbolic computation.

## Kernel dependency audit

Audit job `job_LrqIe3QsMBnSZjy2l3GHyUmWFmhXBoj9` succeeded (server 6.302 s). Eleven principal theorem closures, spanning transfers 21–30 and the countable product positivity result, report only `propext`, `Classical.choice`, and `Quot.sound`. The signatures explicitly retain `hBaezDuarte` in full RH equivalences. The main frequent-head/product criterion has no `NeBot` assumption.

## Publication receipts

Every checkpoint built the aggregate `RiemannResearch` module and its changed Lean modules before pushing to main. Times below are server build durations, not tool round-trip times. Transfer 23 additionally passed a 72.618 s integration build against newer main.

| Transfer | Published commit | Checkpoint job | Build seconds |
|---|---|---|---:|
| 21 | `25273c78d44070ed0eb5be0c46f5075571f5f512` | `job_hhD75su5uFmR913YXIajD_1_Js5zfYl8` | 43.228 |
| 22 | `5bab9ca74acb927ed3aa9c1964d0ec5ab76eaf89` | `job_Nzl3jB3srWdWhWi_c8o6WCJjMc1He5su` | 42.521 |
| 23 | `d81fad8a2a6f5425b1ae6210a8bce28ca9616d38` | `job_cvjptm6Q7En8RNTkdwhEaKKEfE5k5SGT` | 42.202 |
| 24 | `47243db3fb914c4e99987fa127714b0ad7e8757e` | `job_cOiR7wXtYAzBvNVXDRO6Frfm_eH-4G-M` | 64.705 |
| 25 | `09cc7dfa68507f83857021d1bf1ce158e3000c78` | `job_uYzTHf_yaH_tkInYLOjixJ6p_2sY3Oqp` | 56.491 |
| 26 | `f9b3ab6396d215e8403429396b973beeace834c3` | `job_TwfIcspQVG7BesvEQI8s5gXQHKis1b8b` | 57.602 |
| 27 | `436e191169582d9cd35843f7a259ecf59122ec8a` | `job_eb7rkhBD5GPoClFVwInp3-Vj2qz1Pp7a` | 62.475 |
| 28 | `7bd2aa5d4f5cd8dd7e00d4472e2d3c7c1e683cc5` | `job_QtgjTE1DuT7wkN0EEvsW8pDCk56lyXuo` | 39.41 |
| 29 | `4c8e986c53ab15c03b9beda26c1ca607d95d2f40` | `job_Y74oCNOrvfVZ0mw2sBIJG8Hx90s9dDPH` | 58.141 |

Transfer 30 is the commit containing the completed product modules and this audit; its final checkpoint receipt is reported in the completion message. Work stops after this tenth transfer.
