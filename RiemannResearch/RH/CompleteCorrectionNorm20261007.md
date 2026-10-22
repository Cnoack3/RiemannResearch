# Complete correction-norm assembly in Lean

Date: 2026-10-07. Project: [Cnoack3/RiemannResearch](https://github.com/Cnoack3/RiemannResearch). Lean: `v4.33.0-rc2`.

## Result

The complete correction norm is derived from the literal continuum integral. Its norm constant, signed source, projected norm, residual variance, infinite tail, and initial interval are proved inputs. The result holds for every vector of the canonical Pareto Hilbert space; boundedness, periodicity, finite support, and RH are not hypotheses.

Write

\[
w_j=\frac1{j(j+1)},\qquad
c_j=j(j+1)\log\!\left(1+\frac1j\right)-j,\qquad j\ge1.
\]

For a zero-anchored physical sequence \(h\) of finite weighted square energy, define

\[
H=\sum_{j\ge1}w_jh_j^2,\quad
L=\sum_{j\ge1}w_jh_jc_j,\quad
A=\sum_{j\ge1}w_jc_j^2,
\qquad C=\log(2\pi)-\gamma.
\]

Here \(J h(t)=h_{\lfloor t\rfloor}\), and \(\rho(t)=\{t\}\). The actual complete integral satisfies

\[
\boxed{I(h,\alpha):=\int_0^\infty
\frac{(Jh(t)-\alpha\rho(t))^2}{t^2}\,dt
=H-2\alpha L+\alpha^2 C.}
\]

Every source and energy series used here is proved absolutely convergent. Completing the charge gives the exact identity

\[
\boxed{I(h,\alpha)=H-\frac{L^2}{C}
+C\left(\alpha-\frac LC\right)^2.}
\]

The actual cell variances are

\[
V_j=1-j(j+1)\log^2\!\left(1+\frac1j\right)>0,
\quad B=1+\sum_{j\ge1}V_j=C-A.
\]

Consequently the full orthogonal split and transfer are

\[
I(h,\alpha)=\sum_{j\ge1}w_j(h_j-\alpha c_j)^2+B\alpha^2,
\qquad
\boxed{H\le\frac CB I(h,\alpha).}
\]

The norm version is proved for the actual canonical Hilbert vector:

\[
\boxed{\|h\|\le\sqrt{\frac C{C-A}}\sqrt{I(h,\alpha)}.}
\]

The factor is optimal on the whole structural Hilbert space. Lean proves that any universally valid squared factor is at least \(C/B\). Its equality witness is \(h=c\), \(\alpha=A/C\); \(A>0\) is proved, so the witness is nonzero. Minimality of the norm factor is also proved among nonnegative norm factors.

## Strict improvement and complete tail certificates

The cell means satisfy \(0<c_j<1/2\), and \(0<A\le1/4\). The interval \((0,1)\) contributes exactly \(\alpha^2\) to the corrected norm and exactly \(1\) to \(C\) and \(B\). The first tail-cell variance is exactly

\[
V_1=1-2\log^2 2>0.
\]

Retaining the next positive variance proves the strict bound

\[
B>2-2\log^2 2>1,
\qquad
\frac CB<\frac C{2-2\log^2 2}<C.
\]

Thus the new transfer factor strictly improves the previous \(\sqrt C\) factor. The stronger universal factor \(\sqrt{C/B}\) is exact; the first-cell expression is a closed upper bound.

For every \(N\ge0\), let \(A_N=\sum_{j=1}^Nw_jc_j^2\), \(C_N=1+\sum_{j=1}^Nq_j\), and \(B_N=1+\sum_{j=1}^NV_j\), where

\[
q_j=2-\frac1{j+1}-2j\log\!\left(1+\frac1j\right).
\]

Lean proves the complete brackets

\[
A_N\le A\le A_N+\frac1{4(N+1)},
\quad C_N\le C\le C_N+\frac1{3(N+1)},
\quad B_N\le B\le B_N+\frac1{3(N+1)}.
\]

The bounds use actual cell energies \(0<q_j<w_j/3\) and \(0<V_j<w_j/3\), together with the complete Pareto tail mass. They do not replace any infinite norm by a finite truncation.

## Proof structure and declarations

| Module | Main contribution |
|---|---|
| `Analysis/PositiveNaturalCellIntegral.lean` | Exact countable partition of the full positive ray; nonnegative identity requires no integrability hypothesis. |
| `RH/StepCorrectionNorm.lean` | Actual mass, first moment, raw square, and corrected cell integrals; strict mean/variance and one-third cell bounds. |
| `RH/FractionalPartNormConstant.lean` | Finite harmonic/factorial telescope, actual Stirling limit, and complete `HasSum` equal to \(C-1\). |
| `RH/StepCorrectionComplete.lean` | Complete series convergence, signed assembly, orthogonal split, completion, Cauchy gap, transfer, optimality, and finite-prefix certificates. |
| `RH/StepCorrectionContinuum.lean` | Literal fractional-part continuum integral, full integrability, canonical Hilbert consumers, and actual continuum optimality. |
| `RH/StepCorrectionConstant.lean` | Named constant \(C\), strict residual bounds, and the full continuum/Hilbert assembly with \(\log(2\pi)-\gamma\) substituted. |

All correction declarations use namespace `RiemannResearch.RH.StepCorrectionNorm`. The positive-ray partition uses `RiemannResearch.Analysis.PositiveNaturalCellIntegral`.

Principal declarations:

- `fract_energy_eq_log_two_pi_sub_gamma`
- `continuumCorrection_assembly_gamma`
- `continuumCorrection_completed_square_gamma`
- `continuumCorrection_hilbert_gamma`
- `continuumCorrection_hilbert_norm_transfer`
- `continuumCorrection_hilbert_factor_minimal`
- `continuumCorrection_hilbert_norm_factor_minimal`
- `residualEnergy_gt_first_cell`
- `projectionEnergy_prefix_bracket`, `residueEnergy_prefix_bracket`, `residualEnergy_prefix_bracket`

The constant proof retains the finite endpoint exactly:

\[
1+\sum_{j=1}^{n-1}q_j
=2n-H_n-2n\log n+2\log(n!)
=2\log(s_n)+\log2-(H_n-\log n),
\]

where Mathlib proves \(s_n\to\sqrt\pi\) and \(H_n-\log n\to\gamma\). This yields \(C\), rather than assuming a fractional-part norm formula. Integer endpoint changes in the continuum realization are justified using their zero Lebesgue measure.

## Verification and publication

Standalone verification succeeded in job `job_hm4UAkVWPJw3M0BWyrdcpdaYuSltm_cx` (exit code 0). Decisive output:

```text
Audited 93 public theorems: only propext, Classical.choice, Quot.sound.
```

All six separate project modules compiled successfully in job `job_114HqmQilousEWyECN3ibnXRoSJxjJSQ`. An audit importing the actual built modules succeeded in job `job_5jLj7_7BNSKAlpmQe4e21z6f6g3TlEuU`, again confirming all 93 declarations use only the three standard axioms. The source scan found no `sorry`, `admit`, project axiom, unsafe declaration, or blanket `import Mathlib`.

Publication uses one push-enabled checkpoint, which validates the changed modules and project integration.

The project base was `9127674d0aaa3877908103d0c581e1d343984319`. The final source contains 93 public theorem declarations across six modules, with focused imports. An exhaustive transitive axiom audit checks every one of these declarations against `propext`, `Classical.choice`, and `Quot.sound`. The publication checkpoint validates the actual separate modules and project integration.

## Independent checks and provenance

GitHub reads confirmed the published project base, existing abstract `StepCorrectionGain` consumer, and Mathlib's actual Stirling source. Web review used [NIST DLMF §5.11](https://dlmf.nist.gov/5.11), which supports the classical Stirling statement; the complete correction-norm specialization is derived in Lean. The originating argument is Christian Noack's `RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md`, correction-norm and tail-bracket sections.

Wolfram independently returned zero for the differences between the raw/first-moment integrals and their closed forms, and simplified the first cell variance to \(1-2\log^2 2\). Evaluating the Lean-proved finite-prefix formulas at \(N=2000\) gave an approximate sharp norm-factor enclosure \([1.0801809104,1.0802433689]\), a closed first-cell upper bound near \(1.1014678244\), and the old factor near \(1.1227917890\). These decimal evaluations are independent numerical checks; the exact formulas and tail inequalities are the kernel-verified assertions.

The optimality statement concerns the entire structural step space. It does not assert that the equality witness lies in the finite squarefree atom span. The arithmetic gain-divergence provider needed for RH remains outside this result.
