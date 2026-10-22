# Recovered Lean proofs and cancellation-preserving digamma differences

7 October 2026

The earlier Mellin, zeta, and digamma formalization survived the interruption.
The retained project is clean at published commit
`04db1cc3090d06e1abd30261b4a5f4d27df8e189`. Its thirteen modules contain 124
public theorems and 13 private helpers. The successful affected-module build
and 24 selected standard-foundation axiom reports remain recorded in
`RH/MellinZetaDigammaFormalization20261007.md`.

This continuation adds two cohesive modules, with 20 public theorems and one
private helper, proving a stronger bound on actual digamma differences and
applying it to complete physical CRT weights. The proofs reuse the actual
Gamma/digamma, endpoint-defect, and progression-weight providers. No desired
analytic identity is assumed.

## Stronger all-order remainder difference

For \(N\ge0\), set \(k=2N+2\), \(b_k=B_k/k\), and define the actual error
\[
E_N(t)=\psi(t)-\left(\log t-\frac1{2t}
-\sum_{j=1}^{N}\frac{B_{2j}}{2j\,t^{2j}}\right).
\]
For every \(0<x<y\), the new Lean theorem proves
\[
\boxed{0<(-1)^{N+1}\bigl(E_N(x)-E_N(y)\bigr)
<|b_k|\bigl(x^{-k}-y^{-k}\bigr).}
\]
It also proves strict decrease of the signed error on the entire positive
axis. The difference bound retains cancellation between the endpoints.
Adding the two older absolute endpoint bounds would instead give the larger
quantity \(|b_k|(x^{-k}+y^{-k})\).

The full identity is retained before any estimate. Writing
\[
C_N(t)=\int_0^1\bigl(B_k(u)-B_k(0)\bigr)(t+u)^{-k-1}\,du,
\]
the exact difference is
\[
E_N(x)-E_N(y)=\sum_{n\ge0}\bigl(C_N(n+x)-C_N(n+y)\bigr),
\]
and each cell difference is one integral with the common polynomial factor:
\[
C_N(x)-C_N(y)=\int_0^1\bigl(B_k(u)-B_k(0)\bigr)
\bigl((x+u)^{-k-1}-(y+u)^{-k-1}\bigr)\,du.
\]
The proved Bernoulli Fourier sign is nonnegative on the entire cell and
strict at its midpoint. The kernel difference is strictly positive.
Continuity gives a positive signed cell integral; the actual complete
`HasSum` gives a positive signed global difference. The exact recurrence
\[
E_N(x)-E_N(y)=-b_k(x^{-k}-y^{-k})+
\bigl(E_{N+1}(x)-E_{N+1}(y)\bigr)
\]
then yields the strict upper bound from the next-order sign.

For the actual digamma difference, define
\[
L_N(x,y)=\log(y/x)+\frac1{2x}-\frac1{2y}
+\sum_{j=1}^N\frac{B_{2j}}{2j}(x^{-2j}-y^{-2j}).
\]
Lean proves the exact identity
\[
\psi(y)-\psi(x)=L_N(x,y)-\bigl(E_N(x)-E_N(y)\bigr),
\]
with the same strict signed remainder enclosure. Existing reality theorems
identify the formal real part of `Complex.digamma` with digamma at real inputs.

The main declaration is
`RiemannResearch.RH.DigammaBernoulliDifferences.evenDigammaError_sub_strict_signed_bound`.

```lean
import RiemannResearch.RH.DigammaBernoulliDifferences

open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliSignedRemainder
open RiemannResearch.RH.DigammaBernoulliDifferences

example {x y : ℝ} (hx : 0 < x) (hxy : x < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError N x - evenDigammaError N y) ∧
    (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError N x - evenDigammaError N y) <
      |bernoulliCoefficient (2 * N + 2)| *
        ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) :=
  evenDigammaError_sub_strict_signed_bound hx hxy N
```

## Complete CRT weights with the physical head retained

For integers \(Q>0\), \(1\le r\le Q\), the actual progression weight is
\[
\rho_Q(r)=\sum_{m\ge0}\frac1{(r+Qm)(r+Qm+1)}.
\]
Put \(x=1+r/Q\), \(y=1+(r+1)/Q\), and
\[
A_N(t)=\log t-\frac1{2t}-\sum_{j=1}^N\frac{B_{2j}}{2j\,t^{2j}},
\qquad
P_N(Q,r)=\frac1{r(r+1)}+\frac{A_N(y)-A_N(x)}Q.
\]
The first physical-site mass remains exact. The newly proved complete error is
\[
\rho_Q(r)-P_N(Q,r)=-\frac{E_N(x)-E_N(y)}Q.
\]
For every finite order \(N\), Lean proves
\[
\boxed{0<(-1)^N\bigl(\rho_Q(r)-P_N(Q,r)\bigr)
<\frac{|B_k|}{kQ}\bigl(x^{-k}-y^{-k}\bigr).}
\]
Even orders are strict lower bounds, and odd orders are strict upper bounds.
The exact next approximation correction is retained:
\[
P_{N+1}(Q,r)-P_N(Q,r)=\frac{b_k}Q(x^{-k}-y^{-k}).
\]
In particular the certified first bracket is
\[
P_0(Q,r)<\rho_Q(r)<P_1(Q,r),\qquad
P_1-P_0=\frac1{12Q}(x^{-2}-y^{-2}).
\]
The result includes the zero residue represented by \(r=Q\), and \(Q=1\).
It controls the complete infinite progression, rather than a finite prefix
or uniform replacement of the Pareto residue weights. Increasing the order
does not assert convergence of the infinite Bernoulli series at fixed inputs.

The application is
`ParetoProgressionBernoulliBounds.progressionWeight_sub_bernoulliApprox_strict_signed_bound`;
the canonical approximation definition is `progressionBernoulliApprox`.

## Proof inventory and verification

| New module, relative to `RiemannResearch/` | Public theorems | Content |
|---|---:|---|
| `RH/DigammaBernoulliDifferences.lean` | 14 | Actual cell integrability, common-kernel identity, complete signed series difference, strict monotonicity, exact next-order difference, sharp signed and absolute bounds, actual digamma difference |
| `RH/ParetoProgressionBernoulliBounds.lean` | 6 | Canonical head-retaining approximation, exact correction and full error, sharp signed and absolute bounds, certified even/odd brackets |

The generic coherent proof check `job_sZtqIbr57lYRoHSMe8lfAoHoUBK3lV1r`
returned `verified: true`, exit code 0, in 3.818 seconds. Its Lean source
SHA-256 is `a9f4578d35c9ef63ef18627772cc35125afca190706848e1c76945c7305ca76b`.
The coherent generic-plus-CRT check
`job_qxBfLgJmtbIFMDiP5Jbwy9wlqxqjO1-b` returned `verified: true`, exit code 0,
in 20.095 seconds. Its Lean source SHA-256 is
`adbf55cf48e9cf7d48af108494f17cac692e56fc8d834bda2f65bd0a62581d94`.
All 20 new public theorems have clean selected axiom reports. Three additional
reports recheck the recovered actual zeta coefficients, Mellin/zeta identity,
and complex Laurent identity. All 23 reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Both new sources pass scans for proof
holes, custom axioms, unsafe declarations, and unqualified `import Mathlib`.
Project integration is validated and published through one push-enabled
checkpoint; its completed record is included in the delivered copy.

The interruption did not invalidate the earlier proofs. One diagnostic in
this continuation caught missing parentheses around a difference inside
an infinite-sum binder; correcting the grouping made the exact complete
series declaration compile. No hypothesis or mathematical term was removed.

## Remaining RH obligation

This supplies verified analytic estimates for the exact physical CRT weights.
It does not prove that the actual optimized residual converges to zero.
The cumulative arithmetic gain or signed-source cancellation estimate,
the approximation converse/squarefree provider, and the complete named
continuum correction-norm assembly remain open research obligations.
No new proof of RH is claimed.

The proof strategy extends the verified endpoint-defect representation in
`DigammaBernoulliSignedRemainder`. Its Fourier input is Mathlib's actual
Bernoulli series, classically recorded at
[NIST DLMF 24.8.1](https://dlmf.nist.gov/24.8.E1).
