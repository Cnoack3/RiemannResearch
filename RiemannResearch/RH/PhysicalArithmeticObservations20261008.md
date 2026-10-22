# Physical arithmetic observations: checked finite and geometric completion

Follow-up: `PhysicalSourceLimits20261008.md` supplies the actual unconditional
source limits and identifies the source charge with the actual inverse-Gram
projection. It also proves that the complete normalized signed correction tends
to zero. The nine-module verification below records the earlier finite snapshot;
the follow-up has its own two-module verification manifest. Charge saturation
and the analytic RH reverse remain open.

Date: 2026-10-08. Continuation of `PhysicalMeanOneAdvance20261008.md` and
`CriticalZeroMeanOneAdvance20261008.md`. The latter's stretched-scale
optimizer-tail estimate remains excluded as an RH provider.

This advance closes the finite algebraicity and signed Schur formalization
observations, completes the global-squarefree-to-arithmetic-stage geometry,
and supplies a stronger unconditional finite trial and charge-limit interval.
It does **not** prove the analytic RH-to-squarefree approximation provider or
the unconditional arithmetic endpoint. No RH proof is claimed.

## 1. Actual core and optimizer algebraicity

`ArithmeticCoreAlgebraicity.lean` uses Mathlib's rational-angle sine and cosine
algebraicity, extending from integers to rationals. It then proves algebraicity
of every term in the original signed double-divisor cotangent formula, the
finite arithmetic matrices, determinants, and matrix inverse entries.
The inverse is the total **matrix** inverse; no supplied inverse or
nonsingularity premise is hidden in the algebraicity statements.

The previously checked arithmetic/physical identity transfers the result to
the actual Gram-derived core, its inverse charge and constrained coefficients.
The ordinary-mean optimizer and uniqueness remain the results of
`ArithmeticCoreInertia.lean`: every squarefree divisor stage with `L>2`
discharges the odd-prime inertia premise. Algebraicity does not prove a
limiting value; algebraic numbers can converge to a transcendental real.

`ArithmeticMinimumTranscendence.lean` proves, for algebraic nonzero `C`,

\[
  \operatorname{IsAlgebraic}_{\mathbb Q}(1+4x/C)
  \iff \operatorname{IsAlgebraic}_{\mathbb Q}(x).
\]

Its physical minimum application has `x=π`. The transcendental corollary
explicitly assumes `Transcendental ℚ Real.pi`; this repository advance does
not discharge that separate formal premise. The minimum formula itself has
no such premise.

## 2. Complete signed Schur feedback

`MeanOneSchurCoupling.lean` starts with the complete positive inverse-Schur
form, not scalar sign assumptions on individual summands. For the screened
sources `U,V` and symmetric positive-semidefinite `Z`,

\[
 \Delta A=U^\mathsf TZU,\quad
 \Delta B=U^\mathsf TZV,\quad
 \Delta C=V^\mathsf TZV,\qquad
 (\Delta B)^2\le\Delta A\Delta C.
\]

The mixed update stays signed. A separate theorem specializes directly to the
solved block equations established in `MeanOneBlockSchur.lean`.
`PhysicalSchurReindex.lean` and `PhysicalSchurCoupling.lean` then identify the
actual old, cross and new blocks for nested physical packet sets and discharge
inverse-Schur positivity from the proved physical mean-kernel positivity and
the old negative charge. The full mean-zero tangent matrix is
`S+VVᵀ/C` with `C<0`; the negative signed correction is preserved. This finite
application requires legal conductors and an old odd-prime packet, with no
supplied inverse, supplied positivity, or analytic limit premise.
The same module proves actual finite `A<0`, `B<−π`, and
`T=AC−(2π+B)²>0`. Its defined source-charge scalar `Q=4π(−A)/T` is positive,
and the corrected charge equals `4π/Q` with all finite denominator premises
discharged. This scalar definition does not independently identify `Q` with
an inverse-Gram projection norm. The physical chain bound still displays the
source limits as assumptions.
Under the separately stated limits `A_n→0`, `B_n→−2π`, and `C_n→C∞`,

\[
 (2π+B_n)^2\le(-A_n)(C_\infty-C_n).
\]

If `α_n=−A_n>0`, `D_n=2π+B_n`, `γ_n=−C_n`, this gives

\[
 -C_\infty\le\gamma_n-D_n^2/\alpha_n.
\]

The zero-`α_n` case is handled without division: it forces `D_n=0`.
Under the exact residual projection formula

\[
 Q_n=\frac{4π\alpha_n}{\alpha_n\gamma_n-D_n^2},
 \qquad\gamma_n-D_n^2/\alpha_n=\frac{4π}{Q_n}.
\]

Thus this feedback consequence equals the existing projection bound. It
supplies no independent unconditional estimate tending to the endpoint.

The module includes a fully checked **abstract scalar model**, not physical
arithmetic packets. Set `r_n=1/(n+1)`,
`A_n=−r_n`, `B_n=−2π+r_n`, `C_n=−5π−r_n`.
Its increments are `(δ,−δ,δ)`, `δ=r_n−r_m≥0`, with complete positive form
`δ(x−y)²`. The coupling inequality is an equality; the shifted determinant
is `5πr_n>0`; the unshifted source determinant is negative. Its corrected
charge is `5π`, projection charge `4/5`, and charge limit `−5π`.
This demonstrates the insufficiency of those abstract hypotheses to force
`−4π`. It is not a counterexample for the additional arithmetic structure.

## 3. Actual squarefree geometry and a concrete exhaustive chain

`SquarefreePacketBasis.lean` proves both finite transforms between normalized
residue packets and the original Ramanujan packet dictionary at a common
period. It preserves the complete Hilbert/Pareto error and the ordinary mean.
The `1..L` Cesaro mean and `0..L−1` finite-period mean are connected using the
actual zero endpoint values; they are not silently identified.

`SquarefreeStageExhaustion.lean` constructs `L_n=primorial(n+3)`. These periods
are squarefree, nested by divisibility, contain six, exceed two, and exhaust
every finite squarefree support. The common-period and cofinality hypotheses
are thereby discharged by an actual arithmetic construction.

`SquarefreeArithmeticSaturation.lean` proves the following equivalences with
no assertion that either side holds:

\[
\begin{aligned}
 &\text{centered squarefree approximation}\\
 &\iff\text{squarefree Hilbert packet approximation}\\
 &\iff\text{ordinary mean-one squarefree packet approximation}\\
 &\iff\text{ordinary mean-one arithmetic stage approximation}\\
 &\iff\inf_{L\text{ squarefree},\ L>2}(1+4π/C_L)=0\\
 &\iff E^0_{L_n}\longrightarrow0
 \iff C_{L_n}\longrightarrow-4π.
\end{aligned}
\]

The chain statements also hold for every nested exhaustive squarefree divisor
chain. The checked forward implication from approximation/saturation to RH
uses the existing actual Pareto/Mellin provider. The converse is named
`...of_analytic_reverse` and explicitly requires
`hReverse : RiemannHypothesis → SquarefreeCenteredApproximation`.
All finite-basis, mean repair, common-period and cofinality obligations after
this analytic premise have been discharged.

## 4. Stronger exact physical trial at period thirty

`MeanOneThirtyTrial.lean` evaluates the original complete double-`V` arithmetic
core on conductors `(2,3,5,6)` and uses the rational packet coefficients

\[
 (c_2,c_3,c_5,c_6)=(1/2,1/3,1/5,1/60),\qquad
 \varphi^\mathsf Tc=2.
\]

Writing

\[
 K=797\sqrt3+1224\cot(π/5)+648\cot(2π/5),
\]

the checked complete error is

\[
 E(c)=1-\frac{πK}{10800}
 \approx0.04714217018954558.
\]

This is strictly below the checked `L=6` minimum
`1−π/(2√3)≈0.09310031788289107`. It is a trial upper bound for the actual full
`L=30` constrained minimum, not a claim that these four coefficients are that
full stage's optimizer. The module also retains the earlier screened-six
trial with coefficients `(8/15,1/2,1/30,1/6)` and its exact error formula.

For every physical stage with `30∣L` and `L>2`,

\[
 E_L^0\le1-πK/10800,\qquad C_L\ge-43200/K.
\]

Consequently the actual primorial arithmetic charge converges
unconditionally to a value satisfying

\[
 -43200/K\le C_\infty\le-4π,
 \qquad -43200/K\approx-13.18808558970326.
\]

The exact expressions and inequalities are Lean results. Wolfram independently
checked the totient constraint, the original double-`V` quadratic identity,
and the displayed numerical evaluations; these computations do not substitute
for Lean verification. This narrower interval still does not prove equality
at its upper endpoint.

## 5. Verification and remaining obligations

Nine new modules are exported from `RiemannResearch.lean`. A coherent isolated
check of all 192 public declarations passes, including a transitive axiom audit
restricted to `propext`, `Classical.choice`, and `Quot.sound`. The JSON manifest
`PhysicalArithmeticObservations20261008.verification.json` records the checked
source hashes, public declarations, job ID and compiler result. Publication
additionally validates actual module imports and affected project dependents.

| Observation | Status |
|---|---|
| Actual rational-angle/core/charge/optimizer algebraicity | Established |
| Complete signed Schur Cauchy and source-limit consequences | Established with explicit positivity and limit premises |
| Mean-one repair, both physical basis transforms and stage geometry | Established |
| Concrete squarefree exhaustive chain and charge-limit existence | Established |
| Exact period-thirty trial and stronger unconditional limit interval | Established |
| Actual source limits and inverse-Gram projection identification | Established in `PhysicalSourceLimits20261008.md` |
| RH-to-squarefree analytic approximation provider | **Open** in Lean |
| Unconditional arithmetic endpoint `C∞=−4π` | **Open** |
| Minimum transcendence without a supplied π-transcendence theorem | Separate formal premise |

The missing analytic reverse is not supplied by unconditional half-damped
Möbius convergence or by coefficient support alone. Bagchi's proof uses
RH-controlled Dirichlet partial-sum and Mellin domination estimates before
the small-damping Hilbert limit. The present checked geometric equivalences
isolate that input rather than treating it as proved.

Sources: Mathlib `NumberTheory.Niven` (rational-angle algebraicity proof);
Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733),
Remarks 4 and 8 (analytic reverse proof strategy); the user-directed GitHub
continuation (physical optimization program). The finite thirty-period trial
and formal assembly were developed during this continuation.
