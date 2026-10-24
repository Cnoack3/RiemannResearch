# Ramanujan dual development, transfers 21–30

Date: 23 October 2026. Continuation of transfers 1–20 at main `44ac993267cf4474cb04808a1745dc6f27bedaf4`.

Each numbered transfer is verified by Lean and published in its own commit. All full RH equivalences retain the explicit open converse provider `hBaezDuarte : RiemannHypothesis → Pareto.BaezDuarte.NaturalApproximation`. No proof of RH is claimed. Original positive residue coefficients target **−μ(m)**; the packet coefficients are a different finite Möbius transform.

## 21. Simultaneous prescribed arithmetic coefficients

General arbitrary real inner-product-space theorem: exact double-inverse correction, feasibility, full error completion, and uniqueness. The Ramanujan source matrix is `B H⁻¹ Bᵀ`, automatically positive definite for distinct in-stage original coordinates. The exact constrained error is `1 − M_n + δᵀ(B H⁻¹ Bᵀ)⁻¹δ`, retaining all cross couplings. No nonsingularity provider is assumed.

Isolated Lean verification: `job_2E45CyATyuc2xgr3bfpdhXPhtfFiBuUe`, succeeded, server 5.152 s.

## 22. Exact finite Möbius pinning preserves approximation

An explicit continuous finite coordinate projection repairs the selected original coefficients to −μ. Once all selected conductors enter the stage, the repaired vector has a genuine same-stage packet expansion. Its error equals `1 − M_n + ‖repair(1 − F_n)‖²` and lies between `1 − M_n` and `(1 + ‖repair‖²)(1 − M_n)`. Thus its zero-error criterion, along any cofinal nontrivial filter, is equivalent to canonical saturation and convergence of all original coefficients to −μ. The forward implication to RH is proved; the RH converse explicitly requires hBaezDuarte.

Isolated Lean verification: `job_iIMPVEIcm0IyhgHNn1zCJV-mSShvsMyb`, succeeded, server 9.289 s.
