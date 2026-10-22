# Squarefree RH bridge and finite signed-indicator classification

Date: 16 October 2026.

This continues the five targets in `QDivisorLegality_Research_2026-10-16.md`,
with priority given to the external squarefree RH bridge.

**Target 1 has been advanced, but is not complete.** The implementation proves
the squarefree support, the actual Hilbert limits for damping at least one
half, the exact critical Hardy norm, the exact finite Mellin formula, and the
analytic-estimate-to-RH direction. It does not prove the needed analytic
estimate from RH. No RH-to-density axiom or equivalent assumed theorem has
been introduced.

## 1. Actual squarefree approximants and their unconditional range

For real damping ε and natural cutoff N, define

\[
 F_{\varepsilon,N}=-\sum_{d=1}^{N}\mu(d)d^{-\varepsilon}g_d.
\]

The conductor-one atom is zero. Every nonsquarefree coefficient is zero, so
these are finite squarefree legal candidates for every ε and N. There is no
extra conductor at the cutoff and no boundary correction. The coefficient
signs are retained exactly.

The Pareto realization is the existing
`arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N`. Its Q realization
is `qDampedMobiusPartial ε N`, with precisely the same physical sequence.

`DampedMobiusSquarefreeClosure.lean` proves that every norm limit of these
cutoffs belongs to the closed squarefree span. Using the previously proved
natural-order convergence theorem, it obtains such a limit for every
ε ≥ 1/2, in both P and Q. Its exact physical sequence is

\[
 f_\varepsilon(n)=A_\varepsilon(n)
  -n\,\operatorname{Re}\frac1{\zeta(1+\varepsilon)},\qquad
 A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor.
\]

The additional finite bound

\[
 |F_{\varepsilon,N}(n)|\le
 \sum_{d=1}^{N}|\mu(d)d^{-\varepsilon}|
\]

is used solely to justify the finite residual's ordinary critical-line
integral. It is not a uniform approximation or energy estimate.

## 2. Exact main norm identification

Let \(\mathcal Mf(s)=\int_1^\infty f(\lfloor x\rfloor)x^{-s-1}\,dx\),
using the project's actual Pareto physical sequence. Write
\(s_{\sigma,w}=\sigma+2\pi i w\).

`ParetoMellinHardyNorm.lean` proves, for every Pareto Hilbert vector,

\[
 \boxed{\|f\|_P^2=
  \sup_{\sigma>1/2}\int_{\mathbb R}
     |\mathcal Mf(s_{\sigma,w})|^2\,dw.}
\]

The formal statement is an `IsLUB`, so it includes both directions of the
supremum assertion. Uniform interior-line integral bounds are therefore
equivalent to bounds on the complete physical Hilbert norm. The proof uses
the actual step-function energy identity and the established Fourier
Plancherel theorem; it has no supplied isometry hypothesis.

For bounded physical sequences the same module also proves

\[
 \boxed{\|f\|_P^2=\frac1{2\pi}
   \int_{\mathbb R}|\mathcal Mf(1/2+it)|^2\,dt.}
\]

The proof establishes finite energy at every positive exponent before
applying Plancherel. In `DampedMobiusHardyBridge.lean` this is specialized to
the actual residual \(1-F_{\varepsilon,N}\), with the required boundedness
proved internally. No general boundary trace for arbitrary unbounded
Hilbert vectors is claimed.

## 3. Exact zeta formula and the explicit remaining estimate

Set

\[
 H_{\varepsilon,N}(s)=\frac{\zeta(s)}s
 \left(\sum_{d=1}^{N}\mu(d)d^{-\varepsilon}d^{-s}
       -\sum_{d=1}^{N}\frac{\mu(d)d^{-\varepsilon}}d\right).
\]

The generator definition supplies the removable value at s=1. The displayed
zeta formula is proved for Re(s)>0 and s≠1. The exact transform identities

\[
 \mathcal MF_{\varepsilon,N}(s)=H_{\varepsilon,N}(s),\qquad
 \mathcal M(1-F_{\varepsilon,N})(s)=s^{-1}-H_{\varepsilon,N}(s)
\]

are proved on Re(s)>1/2. Combining them with the main norm theorem gives
the exact equivalence, for every real B,

\[
 \|1-F_{\varepsilon,N}\|_P^2\le B
 \iff \forall\sigma>1/2,\quad
 \int_{\mathbb R}|s_{\sigma,w}^{-1}
       -H_{\varepsilon,N}(s_{\sigma,w})|^2\,dw\le B.
\]

`DampedHardyApproximation` names the concrete assertion

\[
 \forall\delta>0\ \exists\varepsilon>0\ \exists N\quad
 \forall\sigma>1/2,\quad
 \int_{\mathbb R}|s_{\sigma,w}^{-1}
       -H_{\varepsilon,N}(s_{\sigma,w})|^2\,dw\le\delta.
\]

The three theorems ending `of_dampedHardyApproximation` are **conditional
research reductions**. From this explicit premise they prove Pareto
squarefree constant closure membership, Q squarefree constant closure
membership, and Mathlib's `RiemannHypothesis`. All legality, norm transfer,
and the existing closure-to-RH argument are discharged internally.

**Open provider:**

```lean
RiemannHypothesis → DampedHardyApproximation
```

This implication is not declared as a theorem, axiom, instance, or available
provider. The unconditional half-damping range cannot approach zero.

Bagchi's published proof, Theorem 2 and Remarks 4 and 8, uses two limits:
first cutoff to infinity at fixed positive damping, then damping to zero.
Möbius support yields the squarefree restriction. Formalizing the remaining
analytic estimates requires the RH-dependent reciprocal-zeta estimates,
the uniform partial-Dirichlet-sum control, the completed-zeta shift and
Gamma-ratio bounds, and the associated dominated-convergence arguments.
The new exact norm bridge supplies the geometric and Plancherel component;
it does not discharge those RH-dependent estimates.

Reference: B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, arXiv:math/0607733 (2006),
https://arxiv.org/abs/math/0607733.

## 4. Complete classification of finite signed indicator sums

Let \(F=\sum_{m\in S}b_mI_m\), where S is finite and contains positive
conductors. The concurrently published `QSignedDivisorLegality.lean` and
`QParityGeometry.lean` supply the established classification equivalent to

\[
 \boxed{F\in H_{\rm sf}\iff
 \exists\alpha,\beta\in\mathbb R:\quad
 F=\alpha\,1+\beta I_2\quad\text{and}\quad
 (\alpha+\beta=0\ \text{or}\ 1\in H_{\rm sf}).}
\]

The representation here is equality of actual Hilbert vectors, not an
informal truncation of an indicator expansion. No signs or sizes of b are
restricted. This retains cancellations such as \(I_1-I_2=2g_2\).

The decisive argument is already formalized in the published
`Analysis/EvenPeriodicSquareJump.lean`. Extend a finite divisor sum to all
integers by the ordinary divisibility formula, including its ordinary value
at zero. The extension is even and periodic with a positive common period.
Periodicity carries the positive-site square-jump identities to all integers.
Evenness then gives

\[
 \Delta F(-n)=F(n)-F(n+1),\qquad
 \Delta F(n)=F(n)-F(n-1),\qquad
 \Delta F(-n)=\Delta F(n),
\]

so \(F(n+1)=F(n-1)\). Thus any finite divisor sum passing all square-jump
tests depends only on parity. Returning to the positive Hilbert coordinates
keeps the auxiliary zero anchor unchanged.

Finally,

\[
 \alpha\,1+\beta I_2=(\alpha+\beta)\,1-2\beta g_2.
\]

The subspace properties give the exact closure condition above. The constant
membership alternative is retained as a proposition; RH is not assumed.

## 5. Agenda status

| Original target | Status after this continuation |
| --- | --- |
| 1. Formalize the external squarefree RH bridge | Advanced: actual squarefree damped family, unconditional half-damping limits, critical norm identities, and exact analytic consumer; RH-to-estimate provider remains open. |
| 2. Quantify the obstruction | Already implemented in the base commit's `QSquarefreeJumpDistance.lean`; no duplicate witness construction added. |
| 3. Classify finite signed indicator combinations | Completed as the exact closure-membership classification above; passing all square-jump tests already forces parity in this finite dictionary. |
| 4. Transfer annihilators to Parseval coordinates | Open; no new coordinate-map theorem is asserted here. |
| 5. Obtain a norm estimate for actual constant approximants | The exact analytic bound is now explicit and has a checked consumer; no new global bound is proved. |

The highest-priority continuation is the analytic provider in Section 3.
Neither the parity classification nor local jump tests establish constant
closure membership. No unconditional proof of RH is claimed.

## 6. Verification and publication

The new source modules and this record are submitted together to the mandatory
server checkpoint, which validates the changed modules and aggregate project
before publication. The terminal checkpoint response supplies the exact job,
validation scope, and published commit. Representative axiom checks are
included in the final verification snippet. Only standard Lean foundations
are permitted; the source contains no proof placeholders or local axioms.

An initial checkpoint validated the new sources but publication encountered
an integration conflict: concurrent commit
`79f8396436af1310ce18dd6f4428ebfe5810f718` added the independently developed
finite-indicator classification at the same general module path. The
unpublished work was preserved. This continuation reuses that fuller
published classification instead of adding duplicate declarations. It
publishes only the three new analytic bridge modules and their documentation.
