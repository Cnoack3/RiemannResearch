# Complete reciprocal-operator bounds for the actual inverse-square optimizer

9 October 2026. Starting published repository commit:
`6d7fcb2e3de8bc7ddac82adc4eade51299bd401f`, which includes the original
`9f8771d9bd37cfcc7d499ca041499e4b0a9d4698` rational head certificate.

## Verification status

The full base project build passed. All five new module bodies passed one
coherent Lean check using `leanprover/lean4:v4.33.0-rc2`. A transitive axiom
audit of all 73 public theorems passed, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. The actual stage theorem signatures
were printed and contain only the stated stage-index hypotheses.

Coherent source check: `job_beKP9C95W8XOk6QF2Iohqg08PuwINAAE`, exit 0.
Transitive audit: `job_IBXxuWIWAqakdZRNSFX4IOG9dLhufQB1`, exit 0.
Native affected-module validation and publication are performed by the final
repository checkpoint; its result is recorded with the downloadable patch.
There are no remaining unverified reciprocal-bound declarations or supplied
arithmetic bound providers in the stage applications below.

## Actual objects and unconditional stage statements

Every application uses the existing definitions in `RH/ZetaTwoHilbertSpace.lean`
and `RH/ZetaTwoOptimizerStage.lean`: `QHilbert`, `qSequence`, `qResidue`,
`reciprocalD`, `stage`, `optimizer`, `residual`, `error`, `screenedResidual`,
`secondMoment`, `quarticFloor`, `weightedMismatch`, `screening`, and
`signedCorrection`. No replacement Hilbert model or assumed optimizer law is used.

The repository stage index is `n`: stage `n` contains conductors through `n+1`,
with nonsquarefree dictionary entries equal to zero. Thus conductors two and
three are present for `2 ≤ n`; conductor five is present for `4 ≤ n`.

The target declarations have only these ordinary stage-index hypotheses:

| Declaration | Stage condition | Bound |
|---|---:|---:|
| `ZetaTwoReciprocalBound.secondMoment_le_nine_div_fortyNine` | `2 ≤ n` | `m₂(n) ≤ 9/49` |
| `ZetaTwoReciprocalBound.secondMoment_bounds_sharper` | `2 ≤ n` | `0 ≤ m₂(n) ≤ 11449/62500` |
| `ZetaTwoConductorFiveBound.secondMoment_bounds` | `4 ≤ n` | `0 ≤ m₂(n) ≤ 9/64` |
| `ZetaTwoConductorFiveBound.secondMoment_le_margin` | `4 ≤ n` | `m₂(n) ≤ (10745/28906)² < 9/64` |

All namespaces in the table have prefix `RiemannResearch.RH.`.
The final stage declarations do not take a moment bound, infinite-tail bound,
arithmetic cancellation estimate, or RH as a hypothesis. Finite-error positivity
is supplied by the existing actual common-factorial-site proof `error_pos`.

## Complete signed series and weighted Cauchy assembly

Let `v(k) = qSequence f k`, `Z = zetaTwo`, and

\[
 S(f)=\sum_{k\ge1}\frac{v(k)^2}{k^2}=Z\|f\|^2.
\]

All physical pairing series are proved summable using the existing Q-weighted
Hilbert pairings. Orthogonality to the actual `qResidue 2` and `qResidue 3`
proves the complete signed normal equations

\[
 v(1)=\sum_{k\ge3}\frac{-a_kv(k)}{k^2},\qquad
 v(2)=\sum_{k\ge3}\frac{2(a_k-b_k)v(k)}{k^2},
 \quad a_k=k\bmod2,\ b_k=k\bmod3.
\]

For any `1/3 < τ < 1/2`, the exact identity is

\[
 Z\bigl(\tau\|f\|^2-\langle f,Df\rangle\bigr)=T_\tau(f)-J_\tau(f),
\]

where

\[
 T_\tau(f)=\sum_{k\ge3}(\tau-1/k)\frac{v(k)^2}{k^2},\qquad
 J_\tau(f)=(1-\tau)v(1)^2+\frac{1/2-\tau}{4}v(2)^2.
\]

Both negative head squares are retained in `J`, and every positive tail site
is retained in `T`. The complete two-channel Gram pairing includes its signed
off-diagonal entry. It is split exactly at sites 3 through 36, followed by the
entire infinite tail beginning at 37. The finite inverse-square comparison keeps
the terminal term before passage to the complete sum:

\[
 \sum_{i=0}^{M-1}\frac1{(i+37)^2}
 \le\frac1{36}-\frac1{M+36},\qquad
 \sum_{k\ge37}\frac1{k^2}\le\frac1{36}.
\]

`Analysis/InfiniteWeightedCauchy.lean` proves the signed infinite weighted
Cauchy inequality by limits of the exact finite Cauchy inequalities. The
recovery rows supply `J ≤ Λ T`, with internally proved numerical providers:

| Recovery constraints | Threshold `τ` | Complete tail trace cap | Full head-tail `Λ` |
|---|---:|---:|---:|
| 2, 3; original certificate | `3/7` | `37/832` | `4137/4160` |
| 2, 3; sharper same head | `107/250` | `5957/133524` | `33101057/33381000` |
| 2, 3, 5; adjusted signed rows | `3/8` | `1813/18540` | `3329/3708` |

Each coefficient `Λ` is strictly below one. The original retained remainder
is at least `(23/4160) T`; the conductor-five remainder is at least
`(379/3708) T`.

## The additional conductor and the improved remainder

Orthogonality to conductors three and five proves the exact complete zero charge

\[
 \sum_{k\ge3}\frac{(b_k-c_k)v(k)}{k^2}=0,
 \qquad c_k=k\bmod5.
\]

Their residues agree at both head sites, so adding this zero charge changes
neither recovered coordinate. The improved rows are

\[
 w_1(k)=\frac{-5a_k-b_k+c_k}{5},\qquad
 w_2(k)=2a_k-b_k-c_k.
\]

At `τ=3/8` their exact 34-site head satisfies
`H₁₁ ≤ 39/50`, `H₂₂ ≤ 59/100`, and `H₁₂² ≤ 41/10000`.
All thirty residue channels satisfy the trace numerator bound `49/40`.
The signed Young coefficients `1/50` and `41/200`, plus the entire tail,
give `Λ=3329/3708`.

The retained positive remainder also controls the full norm:

\[
 Z\|f\|^2\le\left(24+8\Lambda\right)T
 =\frac{28906}{927}T.
\]

Combining this with `T-J ≥ (379/3708) T` improves the first-moment cap to

\[
 \langle f,Df\rangle
 \le\left(\frac38-\frac{379}{115624}\right)\|f\|^2
 =\frac{10745}{28906}\|f\|^2.
\]

The full head norm and tail norm are both included in this improvement.

## Actual compression and correction squares

For any actual closed subspace `V` and `r ∈ Vᗮ`, put
`s = Dr - V.starProjection (Dr)`. Then `s ∈ Vᗮ` and
`‖s‖² = ⟨s,Dr⟩`. Positivity and symmetry of the existing `reciprocalD`
prove positive-form Cauchy. A first-moment cap `τ` on the same orthogonal
complement therefore gives `‖s‖² ≤ τ² ‖r‖²`. Both `r` and `s` satisfy the
actual residue constraints; this is not a cap applied only to the optimizer.

The existing full signed optimizer identity is reused unchanged:

\[
 e_n m_2(n)=\varepsilon_n+\Gamma_n,\qquad
 \Gamma_n=\delta_n-s_n,
\]

where `δ_n=weightedMismatch n` and `s_n=screening n` are the two actual norm
squares. At stages containing conductor five the resulting bound retains both:

\[
 \Gamma_n\le\left(\frac{10745}{28906}\right)^2 e_n-\varepsilon_n,
 \qquad
 0\le\frac{\Gamma_n^+}{e_n}\le\left(\frac{10745}{28906}\right)^2.
\]

## Remaining research obligation

These are fixed positive unconditional bounds. They prove neither
`secondMoment n → 0` nor cofinal decay of the actual normalized positive signed
correction. The existing RH consumer still needs the explicit moving-stage
provider

\[
 \frac{\max(\mathrm{signedCorrection}(\kappa_j),0)}{\mathrm{error}(\kappa_j)}
 \longrightarrow0,
 \qquad\kappa_j\longrightarrow\infty.
\]

Larger conductor sets can provide further exact zero charges. However,
ZetaTwoReciprocalObstruction.lean now proves universal first-moment caps on
the entire squarefree-stage orthogonal complement are at least 1/3, and
universal compressed-square caps are at least 1/9, at every stage. Such caps
cannot tend to zero, including under RH. The actual target residual's moment
can still vanish; its estimate needs target-specific arithmetic cancellation.
No unconditional proof of RH is claimed. See TargetSpecificReciprocalAdvance20261009.md.

Web documentation was consulted for Mathlib's infinite-sum, Cauchy, and
projection APIs. Wolfram Language exact arithmetic independently checked the
candidate finite rational inequalities; none of its output is a proof input.
