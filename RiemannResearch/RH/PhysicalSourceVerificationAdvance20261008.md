# Physical squarefree Pareto verification, exact mean repair, and source rates

Date: 2026-10-08 UTC. Baseline: commit `5d11b51aa4c7dd7abc4fe1c94b2e2495059179df`.

The complete 37-module source set passes one coherent Lean compilation and a
transitive axiom audit of all 540 listed public declarations. This includes the
previous arithmetic core, inertia, physical optimizer, repair closure, signed
Schur updates, source limits, optimizer agreement, and quantitative zero
obstruction. Seven new modules add 45 declarations. The existing finite-minimum
transcendence theorem is strengthened by discharging its π premise.

This is a verification and finite/quantitative advance. The unconditional
arithmetic endpoint and the analytic RH converse are still open.

## Exact physical mean repair

For a finite packet set whose conductors exceed one and which contains an odd
prime, use the actual physical Gram matrix and core:

\[
\Gamma=\pi F+\tfrac12(\lambda\phi^\top+\phi\lambda^\top),\qquad
A=\lambda^\top F^{-1}\lambda,\quad
B=\lambda^\top F^{-1}\phi,\quad C=\phi^\top F^{-1}\phi.
\]

Write \(S=2\pi+B\), \(T=AC-S^2>0\).
The actual unconstrained projection coefficients \(u\) and ordinary-mean dual
\(v\) solve \(\Gamma u=\lambda\) and \(\Gamma v=\phi\).
The new module `PhysicalMeanRepairProjection.lean` proves

\[
\boxed{c^0=u+\frac{S}{C}v},\qquad
\phi^\top u=2+\frac{4\pi S}{T},\qquad
\phi^\top v=\frac{-4\pi C}{T}>0.
\]

The repair coefficient remains signed. Its complete error penalty is

\[
\boxed{
E(c^0)-E(u)
=\frac{(2-\phi^\top u)^2}{\phi^\top v}
=\frac{4\pi S^2}{(-C)T}.
}
\]

The existing complete projection identity is retained:

\[
E(c)=1-Q+(c-u)^\top\Gamma(c-u).
\]

The new application proves the actual unconstrained optimizer is unique and
that \(Q\) is monotone under nested legal packet enlargement. It also proves,
for the actual primorial charge limit,

\[
0\le E(c_n^0)-E(u_n)
\le \frac{4\pi}{C_n}-\frac{4\pi}{C_\infty}.
\]

The convergence premise in this last declaration is supplied unconditionally
by the existing actual primorial charge-limit theorem. Its value remains
unidentified. The already published `PhysicalOptimizerLimits.lean` supplies
the common error limit and pointwise agreement; those results are not duplicated.

## Quantitative unconditional source bounds

`PhysicalSourceRates.lean` retains the exact signed determinant
\(T=AC-(2\pi+B)^2\) and proves, whenever a prime \(p\) belongs to the legal packet
set,

\[
-A<\frac{4(-C)p}{3(p-1)^2},\qquad
(2\pi+B)^2<\frac{4C^2p}{3(p-1)^2}.
\]

The simpler consequences are

\[
-A<\frac{16(-C)}{3p},\qquad
(2\pi+B)^2<\frac{16C^2}{3p}.
\]

For the actual stage
\(L_n=\operatorname{primorial}(n+3)\), every prime \(p\le n+3\) is formally
shown to belong to the packet set. The existing bound \(-C_n\le8\sqrt3\)
then gives the internally discharged application

\[
\boxed{
0<-A_n<\frac{128\sqrt3}{3p},\qquad
(2\pi+B_n)^2<\frac{1024}{p}.
}
\]

These estimates concern the unnormalized shifted source square. Since
\(-A_n\) also tends to zero, they do not supply a rate for
\((2\pi+B_n)^2/(-A_n)\), a charge-convergence rate, or charge saturation.

## The π-transcendence premise is discharged

Five modules under `NumberTheory/Transcendence/` adapt 27 declarations from
[Trevor Morris's Apache-2.0 formalization](https://github.com/gotrevor/lean-formalizations/tree/bad0e21a37874f09f45072dad6225de55742e6c5/src/LeanFormalizations/NumberTheory/Transcendence).
Upstream statements and proof bodies are attributed in each module.
The adaptation uses focused imports, the project namespace, only the two
factorial/prime-selection helpers needed for π, and an explicit powerset base
case required by the project's Mathlib version.

The checked capstone is
`RiemannResearch.NumberTheory.Transcendence.transcendental_pi`.
Consequently,
`ArithmeticMinimumTranscendence.constrainedOptimizer_error_transcendental`
now needs only the genuine finite legalness and odd-prime hypotheses; it
takes no `hpi` argument.

A finite error's transcendence does not prevent its limit from being zero.

## Verification record

The coherent source check is `job_2pJldf1mdWbmMpSXOY-T3mu_vaViflk5`,
exit code zero, 36.08 seconds. Its exact code SHA-256 is

`6e52a7e34742fe65846c55a7d85b24c5eb351730a40644f1c849aee35d0458b5`.

Decisive output:

```text
AXIOM AUDIT PASSED: 540 public declarations; only propext, Classical.choice, Quot.sound
```

The companion JSON records every declaration, all 37 source hashes, the
request hash, exact theorem-type checks, and verification output.
No placeholder, project-local axiom, or unsafe declaration was added.
After this check, a documentation line starting with “axiom-clean” was rephrased
because the textual publication scan misclassified it as an axiom declaration.
No declaration type or proof body changed; the JSON records this comment edit.
Publication separately validates actual module imports and affected project
dependents through the checkpoint service; the coherent source check alone
is not a whole-repository build.

## Remaining obligations and next research

| Obligation | Status |
|---|---|
| Actual arithmetic core and inertia | Established |
| Physical constrained optimizer, uniqueness, exact minimum, and repair closure | Established |
| Actual projection solve, signed source limits, and optimizer agreement | Established |
| Exact signed mean repair and explicit source bounds above | Established |
| Finite minimum transcendence without supplied π premise | Established |
| Unconditional \(C_\infty=-4\pi\) | **Open** |
| `RiemannHypothesis → SquarefreeCenteredApproximation` analytic provider | **Open in Lean** |

The actual limit exists in the previously improved thirty-period interval.
The complete signed correction vanishes, but the common limiting error is
still \(1+4\pi/C_\infty\). Proving that error is zero, equivalently \(Q_n\to1\)
or \(C_n\to-4\pi\), would imply RH by the existing checked forward implication.

The analytic converse is a different formalization obligation. The primary
[Bagchi survey](https://arxiv.org/abs/math/0607733) supplies an RH-conditional
analytic proof strategy: fixed-damping Möbius approximation, RH-controlled
partial sums, an integrable Mellin majorant, and passage to small damping.
Its argument is not silently substituted for a Lean provider. The existing
half-damping and seed-and-dilation declarations do not discharge this
squarefree-only converse.

Next arithmetic work should control the remaining actual projection defect
or total signed Schur gain. The bounds on \(A\) and \(B\) alone do not force
the projection charge to one. The critical-zero-obstructed stretched-scale
optimizer-tail estimate remains excluded.
