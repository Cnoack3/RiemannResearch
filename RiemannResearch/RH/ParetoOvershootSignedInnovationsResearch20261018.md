# Full-Pareto overshoot and signed innovation continuation

Prepared 18 October 2026 for Christian Noack.

## Scope and provenance

Source: the user-provided Pareto_Parity_Overshoot_and_Relative_Bounds_2026-10-18(1).md, Sections 1–3. These elementary Hilbert-space arguments carry no novelty claim. All expectations and norms use the complete law P(N=k)=1/[k(k+1)] on positive integers.

The manuscript cutoff M corresponds to projection (M-1); optimizer n corresponds to M=n+3. The actual manuscript dyadic stage 2M is optimizer (2*n+3).

## Established mathematical statements

* The full negative-part mass is 1-Lipschitz from the Pareto Hilbert norm, with the sharper intermediate bound by the complete L1 norm of the difference.
* The exact residual mean is energy n. Thus projectionOvershoot n=(hilbertL1Norm(hilbertOne-projection n)-energy n)/2, with the analogous limiting equality.
* Orthogonality to the odd indicator gives f(1) <= 2*hilbertNegativeMass f, including the finite positive-part first-coordinate lower bound.
* The limiting overshoot lies between (1-sqrt(2)/2)*limitEnergy and (sqrt(limitEnergy)-limitEnergy)/2.
* Vanishing projection overshoot, vanishing residual L1 excess, zero limiting residual, and constant membership in the closed legal span are equivalent.
* At the first nonempty projection stage, corresponding to M=2, overshoot is exactly zero and energy is strictly positive. This does not contradict the limiting criterion.
* The optimizer first coordinate satisfies -U(1)>=(2-sqrt(2))*||U-evenIndicator||^2.

The generic module Analysis/ProjectionPairingVariation.lean proves finite two-gap square-root budgets, absolute summability, the limiting total-variation budget, and the signed telescoping endpoint for arbitrary nested orthogonal projections with the stated strong limits.

RH/ParetoSignedInnovations.lean applies this to the actual Pareto projection and the first-coordinate Riesz vector. Its summands retain the exact signed expression schurEta(n)*innovation(n)(1)/schurSigma(n), and:
  sum_{n>=1} firstInnovation(n) = -limitResidual(1).
The complete absolute tail from any stage k is bounded by:
  sqrt(energy(k)-limitEnergy) *
  ||P_closed firstCoordinateRiesz-P_finite(k) firstCoordinateRiesz||.
The signed total is bounded between -(2+sqrt(2))*limitEnergy and -(2-sqrt(2))*limitEnergy and vanishes exactly when the limiting residual does.

## Conditional research reductions

Open: an eventual complete-overshoot upper bound along a cofinal selection j,
  projectionOvershoot(j(n)) <= theta*energy(n)+beta(n),
where beta tends to zero and theta < 1-sqrt(2)/2.

Open: an eventual ordinary residual first-coordinate upper bound,
  residual(j(n))(1) <= theta*energy(n)+beta(n),
where beta tends to zero and theta < 2-sqrt(2).

Open: an eventual parity-optimizer first-coordinate upper bound,
  -optimizer(j(n))(1) <= theta*||optimizer(n)-evenIndicator||^2+beta(n),
where beta tends to zero and theta < 2-sqrt(2).
The manuscript dyadic case is supplied explicitly.

Open: an arithmetic provider forcing the signed innovation endpoint to vanish.

The proved conditional consumers force zero limiting defect and then use the existing project implication to Mathlib's RiemannHypothesis. None of these arithmetic providers is supplied by convergence or absolute summability. No unconditional RH conclusion is asserted.

## Numerical and classical-reference status

The source Markdown's floating-point Gram table is exploratory and is not promoted to a Lean numerical certificate.

Bagchi, “On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis” (2006), Theorem 1, https://arxiv.org/abs/math/0607733, supports the classical full-Pareto discrete closure background. Its RH-to-closure implication is not newly formalized here.

## Verification and publication

The recovered old job job_lslNcqcrI_LNcJww9GduLQcHX54VEJ1Z had terminated by wall timeout, without a verification certificate. The recovered appendix required Lean elaboration repairs; it was never treated as verified.

Final project-source validation is the publication checkpoint on these exact files.
The candidate job job_NcnBjQ7ezlQKpoPIY9XpZEMlVArvqrBK reached every declaration.
Its relative optimizer RH consumer, complete signed-innovation absolute-tail bound,
and signed-endpoint RH consumer report only propext, Classical.choice, and Quot.sound.
The candidate's one remaining error was a concrete if-expression simplification in
the overshoot witness inequality; this source rewrites that branch explicitly.
The checkpoint, rather than the incomplete candidate run, is the verification
certificate for all 42 theorems in their final owning modules.
This record is published only if the final server checkpoint succeeds, including its affected-module validation and any required integration validation.
