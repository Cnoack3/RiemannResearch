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
