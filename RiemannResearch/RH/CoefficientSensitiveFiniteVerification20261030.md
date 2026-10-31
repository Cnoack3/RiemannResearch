# Coefficient-sensitive finite verification and growing squarefree families

30 October 2026 (America/New_York).

This continuation recovers the candidates accompanying
[397343c](https://github.com/Cnoack3/RiemannResearch/commit/397343c397c36324062a3dbf3d82dd086308c551)
and strengthens their finite head-constraint and right-line normalization interfaces.
The original [paper memorandum](CoefficientSensitiveSignedCorrection20261030.md)
remains the source for the complete contour discussion.

## Verification boundary

Twenty-one added declarations were checked in isolated development jobs with
`#print axioms`. Every axiom report is exactly the standard set
`propext`, `Classical.choice`, `Quot.sound`. There is no added project axiom,
admitted proof, RH assumption, or density assumption in these finite declarations.
Their elementary hypotheses (Hermitian symmetry, head constraints, positive
weights, positive integer indices and nonresonance) remain visible in their types.

These records are development checks, not substitutes for the final source
checkpoint. Publication is permitted only after the checkpoint validates the
installed modules and the required dependents. Its terminal result determines
project acceptance; the earlier documentation-only commit certified none of
these new declarations.

| Development check | Job | Server operation seconds | Result |
|---|---|---:|---|
| Real symmetric row energy | `job_Rr_cU4_lQSqH-5NoTOe1AOJcFfcVpLx4` | 4.050 | verified, exit 0 |
| Complex quadratic and explicit head constraints | `job_AZTLzbYDwrsnF5dzqP-5Z0FUv5IVmVZn` | 4.336 | verified, exit 0 |
| Rational kernel and denominator-preserving weight | `job_4tvxtaZFKD7SV7meekQk4tDcchV-KXU4` | 5.570 | verified, exit 0 |
| Positive weighted rows | `job_g6SdIDS_LWWAMrABdMoRwFtbc1zL8Vcu` | 4.039 | verified, exit 0 |
| Actual Mangoldt finite assembly | `job_KEe54dnMdFVfJam2-JREJ0bFO2hpXiFk` | 5.689 | verified, exit 0 |
| Exact exponential normalization and actual assembly | `job_2jq0QnTcXBpRI6JQN972fNONs2iG8EAE` | 5.578 | verified, exit 0 |
| Installed three modules and all 21 axiom reports | `job_XFLdXAbR8o17On7sf_YuBmMvgDTM9ZdZ` | 18.275 | verified, exit 0 |

The retained-workspace opening request took 80.683 seconds round trip.
Verification queue delays in these six checks were under 0.002 seconds.
Polling was deferred for at least the requested 30 seconds. Server operation
durations include setup and dependency restoration, and are not kernel-only
timings. The two original 240-second timeouts are historical failures, not
refutations; their combined draft was recovered from the preserved ZIP.
Unused-tactic warnings were removed before installation. An existing missing
copyright header was corrected before checkpoint; long-line warnings in
temporary axiom-print commands do not affect the installed declarations.

## 1. Finite row energy and the exact constrained action

Let S be a finite set, B a Hermitian complex matrix on S, and
Q_B(a)=Re(a*Ba). Let A be any finite head matrix with rows indexed by K.
The new matrix pairing theorem proves, without assuming full rank,

\[
 \sum_{i\in S}\overline{h_i}(A^*\lambda)_i
 =\sum_{k\in K}\overline{(Ah)_k}\lambda_k.
\]

Consequently Ah=0 gives the complete identity

\[
 Q_B(a+h)-Q_B(a)
 =2\operatorname{Re}\sum_{i\in S}\overline{h_i}
       (Ba-A^*\lambda)_i+Q_B(h).                 \tag{1}
\]

The declarations are `finite_head_adjoint_pairing`,
`finite_head_adjoint_annihilates`, and
`kernelQuadratic_perturbation_head_constraints`, in namespace
`RiemannResearch.Fourier`.

For any positive weights v_i set

\[
 d_i(v)=\sum_{j\in S}|B_{ij}|\frac{v_j}{v_i}.
\]

The certified row bound and constrained perturbation bound are

\[
 |Q_B(h)|\le\sum_i d_i(v)|h_i|^2,
\]
\[
 |Q_B(a+h)-Q_B(a)|
 \le 2\sum_i|h_i|\delta_i+\sum_i d_i(v)|h_i|^2,
 \qquad |(Ba-A^*\lambda)_i|\le\delta_i.          \tag{2}
\]

These are `kernelQuadratic_abs_le_weighted_row_energy` and
`kernelQuadratic_perturbation_head_weighted_row_bound`. Setting v=1 recovers
the unweighted results. The quadratic remainder is present in every bound.

Paper proof of the row estimate, retaining its exact remainder: for real u
and symmetric nonnegative w,

\[
 \sum_i\left(\sum_jw_{ij}\frac{v_j}{v_i}\right)u_i^2
 -\sum_{i,j}w_{ij}u_iu_j
 =\frac12\sum_{i,j}w_{ij}v_iv_j
       \left(\frac{u_i}{v_i}-\frac{u_j}{v_j}\right)^2\ge0. \tag{3}
\]

Expand the square and interchange i,j in its second diagonal term.
Apply (3) to w_ij=|B_ij| and u_i=|h_i|, after the complex triangle inequality.
The Lean proof obtains the same inequality by rescaling the checked symmetric
row estimate. Equation (3) itself is given here as a paper identity.

## 2. The actual rational mismatch, with its denominator retained

Let n,m,q be positive integers, x=n/m, q<=2x and n!=mq. Both finite interval
endpoints remain arbitrary. The certified estimates are

\[
 |K_{A,B}(\log x-\log q)|\le\frac{4n}{|n-mq|},
\]

and, for every L>=0,

\[
 \frac{x\sqrt{x}}{2\pi}\frac{L}{q^2}
       |K_{A,B}(\log(x/q))|
 \le\frac{2\sqrt m\sqrt n}{\pi}
       \frac{L(x/q)^2}{|n-mq|}.                 \tag{4}
\]

The first is `norm_finitePhaseKernel_rational_gap_le`; the second is
`rightLine_weighted_kernel_gap_le`, in namespace
`RiemannResearch.Analysis.ZeroOrdinate`.
They reuse `rational_log_peak_gap_bound` and the existing finite kernel bound.
`rightLine_weight_gap_exact` proves the weight rearrangement as an equality.

The exact actual-line normalization is also certified:

\[
 \exp(3\log x/2)=x\sqrt x\quad(x>0).
\]

This is `rightLine_exp_weight_eq`. Specializing L=Lambda(q) yields
`weighted_rationalMangoldtNonresonantTerm_gap_le`, stated with the exponential
prefactor used in the actual right-line formula. Its finite coefficient-weighted
sum is `sum_weighted_rationalMangoldtNonresonantTerm_gap_le`.
The two recovered unnormalized Mangoldt bounds are also checked.
No restriction of q to primes is introduced; every nonresonant prime power
is allowed. The resonance is excluded explicitly, rather than estimated by a
division by zero.

These checks do NOT newly formalize the harmonic mismatch summation, the
infinite near/far split, the O(X^(3/2)+X log^2(2X)) envelope, or the complete
Landau contour assembly. Those remain paper deductions in the original memo.
In particular the near bound (4) alone is not a bound on the complete q sum.
For q>2x the separate paper tail bound uses |log(x/q)|>=log 2 and the already
proved summability of Lambda(q)/q^2. Its infinite tail must remain present.

## 3. Application to the actual growing squarefree dictionaries

This section gives rigorous finite-dimensional consequences and conditional
growth criteria on paper; it does not assert new Lean asymptotic providers.

Use every allowed squarefree conductor in the actual stage support S_N,
including composites, and the complete physical-head matrix
A_(k,d)=g_d(k) for 1<=k<=H_N. Let a_N be the actual coefficient vector.
Neither the head H_N nor the number of constraints equals the largest conductor
X_N=max S_N in general.

For nested supports, pad a_N by zero on S_(N+1), put h_N=a_(N+1)-a_N,
and take A to be the OLD H_N head map on the ENLARGED support S_(N+1).
Both vectors meet the old constraints, so Ah_N=0. Apply (1)-(2) with
B=B_(S_(N+1)). Zero padding gives
Q_(B_(S_(N+1)))(a_N)=Q_(B_(S_N))(a_N).
Thus these certified finite inequalities apply across an actual dictionary
enlargement without assuming that the old minimizer remains stationary there.
All newly added edges are included in B, its action defect, and its row energy.
If supports are not nested, the same statement uses their union.

This does NOT justify the physical-energy equality
||h_N||_G^2=E(a_(N+1))-E(a_N): that equality additionally requires stationarity
for the same feasible affine space and the same Gram matrix G. In particular,
the new head constraint is not automatically annihilated by h_N.

For the squarefree covariance B_(m,pm)=-log(p)/(2*pi*sqrt(p)), choose v_n=n^(-tau),
tau>1/2. Its exact row weight is

\[
 d_n(v)=\frac1{2\pi}\left(
 \sum_{\substack{p\mid n\text{ prime}\\n/p\in S}}
       \log p\,p^{\tau-1/2}
 +\sum_{\substack{p\text{ prime}\\np\in S}}
       \frac{\log p}{p^{\tau+1/2}}\right).       \tag{5}
\]

Suppose, as a NEW coefficient hypothesis, |h_n|<=epsilon*n^(-tau). Define

\[
 P_\tau=\sum_p\frac{\log p}{p^{\tau+1/2}}<\infty,
 \qquad D_\tau(a,\lambda)=
 \sum_{n\in S}n^{-\tau}|(Ba-A^*\lambda)_n|.
\]

The exact edge decomposition of the row energy is

\[
 \sum_nd_n(v)|h_n|^2=
 \frac1{2\pi}\sum_{(m,p)\in\mathcal E_S}\frac{\log p}{\sqrt p}
       [p^{-\tau}|h_m|^2+p^\tau|h_{pm}|^2].
\]

Each bracket is at most 2*epsilon^2*m^(-2tau)*p^(-tau).
Enlarging the nonnegative m sum to all integers proves

\[
 |Q_B(a+h)-Q_B(a)|
 \le 2\epsilon D_\tau(a,\lambda)
       +\frac{\epsilon^2}{\pi}\zeta(2\tau)P_\tau. \tag{6}
\]

Both infinite comparison sums converge because tau>1/2. This gives a concrete
weighted alternative to bounding ||Ba||_2. It is consistent with the proven
paper obstruction that ||Ba||_2 diverges for damped Mobius profiles.
That obstruction alone says nothing about D_tau after subtracting A*lambda.
No decay estimate for the actual optimizer increments, or bound on D_tau,
has been supplied here. If the right sides of (6) are summable over stages,
the covariance sequence converges by telescoping; neither that premise nor
an RH consequence of such convergence is being asserted.

## 4. A concrete multiplier construction to investigate

On a fixed finite support let D be a strictly positive diagonal matrix.
For r=Ba-A*lambda, minimizing r*D^(-1)r has the normal equations

\[
 (AD^{-1}A^*)\lambda=AD^{-1}Ba.                 \tag{7}
\]

If A has independent rows, the matrix in (7) is positive definite, so
lambda=(AD^(-1)A*)^(-1)AD^(-1)Ba is well defined. For dependent rows first
choose an independent set spanning the SAME row space; the annihilator is
unchanged. This avoids any unjustified inverse. For every Ah=0,

\[
 |h^*Ba|=|h^*r|\le(h^*Dh)^{1/2}(r^*D^{-1}r)^{1/2}. \tag{8}
\]

Proof: the adjoint pairing removes A*lambda; apply Cauchy--Schwarz to
D^(1/2)h and D^(-1/2)r. Expanding the squared defect around the solution of
(7) leaves the nonnegative term (lambda-lambda_0)*AD^(-1)A*(lambda-lambda_0),
proving optimality. Choosing D_ii>=d_i(v), with a positive regularization
on zero rows, also bounds the quadratic remainder by h*Dh.
Equations (7)-(8) are paper formulas and an explicit finite diagnostic plan,
not certified uniform growth estimates or an inverse of the physical Gram G.

## 5. Separate open obligations

1. **Finite-to-growing coefficient control (Open).** Bound the actual a_N,
   h_N, weighted defect after solving for multipliers, and row remainder.
   Physical G-minimality supplies Ga in range(A*), not Ba in range(A*).
2. **Landau summation (paper-level here).** Retain all nonresonant q, both
   interval endpoints, all contour sides, and coefficient products. For a
   moving family the explicit sufficient budgets remain
   E_right(a_T)=o(T), log^2(T+3) M(a_T)+log(T+3) J(a_T)=o(T), and
   V(a_T)=o(log T), at its actual maximum conductor.
3. **Analytic zero-to-phase input (separate).** The source's
   `UniformSelbergDensity (1/4)` is a deliberately deferred literature
   hypothesis with one constant and threshold for all sufficiently large
   heights and strip thresholds. It is not a new axiom, and these finite
   inequalities do not discharge it. The complete explicit-formula/test
   admissibility hypotheses of any further consumer must likewise stay visible.
4. **RH bridge (Open).** The actual optimizer consumer still requires
   log(1+stageEnergy(denseSchedule,N))/log(N+2)->0 (or its cofinal version).
   Neither bounded signed covariance, convergence of its increments, nor a
   moving-support phase asymptotic alone proves that energy statement.

Sources: the user-requested recovery; the original coefficient-sensitive
memorandum; `HermitianQuadraticPerturbation.lean`, `RationalLogSeparation.lean`,
`FiniteOscillatoryKernel.lean`, `ActualRationalLandauRightLine.lean`,
`ActualZeroSelbergDensity.lean`, and `RH/QCRTOptimizerGrowth.lean`.
No mathematical novelty claim is made.
