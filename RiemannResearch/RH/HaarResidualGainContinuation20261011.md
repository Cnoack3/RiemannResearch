# Two-seed residual gain: finite zero budgets and joint prime certificates

Source: the user-provided
`RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11 (1).md`,
Sections 5--6 and 12. This continuation strengthens those endpoints with
proofs in the actual Pareto Hilbert space. It assumes neither RH nor a
prime-density estimate.

## Actual dyadic gains impose finite zero-exclusion certificates

Keep the note's dilation cutoff and complete legal family. Let
`D_M = distance M` and
`delta_n = dyadicRelativeGain J n`. The existing strict positivity at finite
cutoffs gives `0 <= delta_n < 1`. The exact identity is

$$
\sum_{n<N}-\log(1-\delta_n)
=\log D_{2^J}-\log D_{2^{J+N}}.
$$

For any hypothetical zero $s$ with $\Re s>1/2$ and $s\ne1$, put
$L_s=(2\Re s-1)/|s|^2>0$. The existing bounded Mellin separator applies
to the actual two-seed fit and yields $L_s\le D_M$ at every finite cutoff.
Consequently, for every $J,N$,

$$
\boxed{
\sum_{n<N}\delta_n
\le \sum_{n<N}-\log(1-\delta_n)
\le \log\frac{D_{2^J}|s|^2}{2\Re s-1}.
}
$$

The entire ordinary and logarithmic gain sequences are summable under that
hypothetical zero, and their total sums obey the same explicit budget.
Thus a **finite** certified gain sum exceeding the displayed budget excludes
the chosen point as a zeta zero. This is stronger as a usable endpoint than
merely requiring an infinite divergent gain schedule.

For positive normalized costs $B_n$ with legal screened witnesses satisfying

$$
w_n\in V_{2^{J+n+1}}\cap V_{2^{J+n}}^\perp,
\quad \langle r_{2^{J+n}},w_n\rangle=D_{2^{J+n}},
\quad \|w_n\|^2\le B_nD_{2^{J+n}},
$$

the existing exact cost equivalence gives $1/B_n\le\delta_n<1$.
Only the first $N$ witnesses are needed. In particular,

$$
\sum_{n<N}-\log(1-1/B_n)
\le\log\frac{D_{2^J}|s|^2}{2\Re s-1}
$$

for every such hypothetical zero. Exceeding this finite cost budget excludes
$s$. The logarithmic charge retains more information than $\sum 1/B_n$.

Principal declarations: `distance_lower_bound_of_zeta_zero`,
`dyadic_log_gain_sum_eq`, `dyadic_log_gain_tsum_le_of_zeta_zero`, and
`zeta_ne_zero_of_dyadic_log_cost` in `RH/DyadicGainZeroBudget.lean`.
Reusable recurrence accounting remains in `Analysis/ResidualGainProduct.lean`;
finite-floor budget lemmas live in `Analysis/ResidualGainBudget.lean`.

## Joint prime constraints give a sharp exact contrast certificate

Let $S$ be any finite set of primes $q>\max(M,3)$, and let
$U_M$ be the closed span of the old budget plus all future seed differences
from Section 12. Let $k_q$ be the actual Riesz representer of the prime
Möbius coordinate $\ell_q$. The proof establishes

$$
\ell_q(f)=f(q)-f(q-1)-f(1),\qquad
\langle k_q,k_r\rangle=
\begin{cases}2(q^2+1),&q=r,\\2,&q\ne r.\end{cases}
$$

The off-diagonal entry 2 comes from the shared physical coordinate 1.
For arbitrary real weights $x_q$, the complete finite Gram form is

$$
\left\|\sum_{q\in S}x_qk_q\right\|^2
=2\left[\sum_{q\in S}q^2x_q^2+
\left(\sum_{q\in S}x_q\right)^2\right].
$$

Put $A_S=\sum_{q\in S}q^{-2}$ and $K_S=\sum_{q\in S}q^{-2}k_q$.
For every $F\in U_M$, retaining the full remainder gives

$$
\boxed{
\|1-F\|^2
=\frac{A_S}{2(1+A_S)}
+\left\|1-F+\frac{K_S}{2(1+A_S)}\right\|^2.
}
$$

The same floor applies to the actual finite-budget distance $D_M$.
A singleton recovers exactly $1/[2(q^2+1)]$. Enlarging a nonempty prime
set strictly increases $A_S/[2(1+A_S)]$.

The model $r_*=-K_S/[2(1+A_S)]$ satisfies every selected constraint
$\ell_q(r_*)=-1$ and attains the floor. For any vector satisfying those
finite constraints, the proof gives the exact identity

$$
\|r\|^2=\frac{A_S}{2(1+A_S)}+\|r-r_*\|^2.
$$

This proves sharpness for the finite affine coordinate system.
It does not claim that $r_*$ is an actual legal optimizer residual.

Principal declarations in `RH/MultiPrimeContrastObstruction.lean`:
`prime_mobiusRiesz_inner`, `weighted_primeRiesz_norm_sq`,
`completedBudget_jointPrime_error_identity`,
`actual_distance_jointPrime_lower_bound`, and `jointPrimeModel_minimizes`.

## Precise remaining obligation

Neither result supplies the actual arithmetic gain lower bound.
The joint-prime certificate diagnoses contrast-only limitations; it does not
obstruct the complete legal family at growing cutoffs. The finite zero
certificate is a proved implication whose legal witnesses and sufficient
cost bounds still need an arithmetic construction.

The actual-zero cancellation inputs needed for the note's end-to-end
Haar/equidistribution formalization are not discharged by this continuation.

## Verification boundary

The two-seed module passed an isolated server Lean check in
`job_oHpGcIeLAq3vXDsfsM8G_3RF9ek-cBwp`.
The joint-prime development passed an isolated server Lean check in
`job_qeJGhDMeJnObv9A3G7zPKK5mFmmhQk-E`, followed by routine proof cleanup.
The main finite zero-exclusion theorem, joint error identity and minimizer
reported only `propext`, `Classical.choice`, and `Quot.sound` in axiom
inspection. These isolated checks are distinct from final publication:
the checkpoint must validate the persisted modules and their affected
dependencies before any push.
