# Squarefree signed regularity: finite systems and arithmetic forcing

25 October 2026. Continuation of the user's
`RH_Measure_Change_Regularity_Research_Handoff_2026-10-25(1).md`.
Baseline: `f9aacc3890c763589de22981ee87647447d0b416`.

## Outcome and remaining obligation

This development does **not** prove RH. It supplies exact finite signed
systems, residualized evaluation kernels, matched finite measure-change
projections, stronger Hilbert bounds, and a quantitative arithmetic expansion
of the actual forcing. No constant uniform in both the stage and the growing
physical head has been established.

The primary remaining obligation is still

\[
\exists C\ge0\ \forall N,n\in\mathbb N,\quad
1\le n\le N\implies |b_N(n)|\le C,
\qquad b_N=\Pi_NB(1-\Pi_N1).
\]

The existing theorem `QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound`
concludes Mathlib's `RiemannHypothesis` once this premise is supplied.
None of the new theorems supplies it. All stages use the original masked
squarefree dictionary, with conductors at most N+1; no all-conductor closure
has been substituted.

## A1 and A3: singular finite normal systems

`LinearAlgebra/FiniteHilbertNormalUniqueness.lean` proves uniqueness of the
synthesized vector for arbitrary finite normal systems; coefficient uniqueness
is neither required nor asserted. `RH/QSquarefreeSignedNormal.lean` specializes
this to the actual masked dictionary, retaining its zero columns.

For synthesis S and complete Q matrices G,H,J and moments m,h as in the handoff:

\[
Gc=m,\qquad G\alpha=h-Hc,\qquad Gx=v_n,\qquad Gz=Hx
\]

all have solutions, and their synthesized vectors are respectively
F_N,b_N,k_{N,n},\Pi_NBk_{N,n}. No inverse hypothesis is used.
The exact scalars are

\[
b_N(n)=x^\mathsf T(h-Hc),\qquad
\varepsilon_N=1-m^\mathsf Tc,
\]
\[
\Lambda_{N,n}=x^\mathsf TJx-z^\mathsf TGz,\qquad
[x^\mathsf T(h-Hc)]^2\le
(1-m^\mathsf Tc)(x^\mathsf TJx-z^\mathsf TGz).
\]

Because these are identified with canonical physical values and norm squares,
the scalars are independent of choices of solutions. The Schur difference
is nonnegative. A separate invertible-Gram reindexing was unnecessary.

Key declarations: `exists_signed_system`, `exists_kernel_system`,
`synthesis_choice_independent`, `forcing_choice_independent`,
`correction_physical`, `correction_signed_scalar`, `error_signed`,
`kernelEnergy_signed`, `signed_scalar_sq_le`.

The signed metric formulas also hold, including the complete second-shift
identity. In particular H=G-G_P/zeta(2) and h=m-m_P/zeta(2).
The shifted-weight Gram in the J identity is expressed as the Q inner product
of `(I-B)a_i` and `(I-B)a_j`; physically its weight is
1/(zeta(2)(n+1)^2).

## A2: exact residualized kernels

`Analysis/ResidualizedProjectionKernel.lean` contains the general real Hilbert
geometry. `RH/QSquarefreeCorrectionKernel.lean` supplies actual physical
evaluation vectors and squarefree stages:

\[
k_{N,n}=\Pi_Ne_n,\quad
\ell_{N,n}=(I-\Pi_N)Bk_{N,n},\quad
b_N(n)=\langle r_N,\ell_{N,n}\rangle_Q.
\]

The energy subtraction remains exact:

\[
\Lambda_{N,n}=\|Bk_{N,n}\|_Q^2-\|\Pi_NBk_{N,n}\|_Q^2.
\]

There is also a complementary identity. With beta_n=1/(n+1),

\[
\ell_{N,n}=(I-\Pi_N)(\beta_nI-B)(I-\Pi_N)e_n,
\]
\[
\Lambda_{N,n}\le
\|(\beta_nI-B)(I-\Pi_N)e_n\|_Q^2.
\]

The multiplier difference vanishes at the evaluation site. This isolates an
arithmetic localization problem for the projection kernel; compactness alone
does not control it uniformly.

The theorem `riemannHypothesis_of_head_kernel_product_bound` is a conditional
reduction. Its premise epsilon_N Lambda_N,n <= C^2 remains **Open** and may be
strictly stronger than the signed pairing estimate actually needed.

## A4: quantitative arithmetic forcing

`RH/QSmoothedResidueAsymptotic.lean` defines

\[
t=1-B1,\quad t(n)=\frac n{n+1},\qquad E_d=dBg_d-t.
\]

For every positive conductor d, division with remainder gives exactly

\[
E_d(n)=-\frac{d\lfloor n/d\rfloor}{n+1}.
\]

Thus E_d vanishes at n<d and has absolute value at most one. Applying the
existing complete-tail estimate at cutoff d-1 gives

\[
\boxed{\zeta(2)\|E_d\|_Q^2\le 2/d.}
\]

For every r in H_Q,

\[
d\langle r,Bg_d\rangle_Q-\langle r,t\rangle_Q=\langle r,E_d\rangle_Q,
\]
\[
\boxed{\zeta(2)d
\bigl(d\langle r,Bg_d\rangle_Q-\langle r,t\rangle_Q\bigr)^2
\le2\|r\|_Q^2.}
\]

This is unconditional arithmetic progress, using the full infinite tail.
`QSquarefreeSignedNormal.forcing_rank_one_bound` applies it to the actual
normal forcing rho=h-Hc for each active squarefree conductor. In ordinary
notation, with A_N=<r_N,t>_Q,

\[
\rho_{N,d}=\frac{A_N}{d}+\eta_{N,d},\qquad
|\eta_{N,d}|\le
\sqrt{\frac{2\varepsilon_N}{\zeta(2)}}\,d^{-3/2}.
\]

The square inequality is the formalized statement. The displayed absolute
inequality is its elementary equivalent for positive d. A small forcing
remainder does not by itself control its synthesized correction. The reduced
Gram matrices show substantial numerical conditioning costs at the tested
stages, and the leading and remainder terms may cancel. Keep their signed combination intact.

## B1 and B2: matched finite projections

`RH/QSquarefreeFiniteDisplacement.lean` defines the Pareto stage from the
same masked atom sequence, proves membership agrees after change of
realization, and proves the two stage closures match the intended spaces.
For d_N=F_N^Q-F_N^P,

\[
d_N\longrightarrow d\quad\hbox{in }H_Q,
\qquad d_N-\Pi_NBd_N=b_N.
\]

The finite displacement head criterion now has an explicit checked reduction
to the existing limiting displacement criterion. Its physical bound remains
**Open**; it is not assumed equivalent to the primary finite correction bound.

`RH/QShiftedReciprocalBounds.lean` gives

\[
\|B-\tfrac14 I\|\le\tfrac14,\qquad
\|Bf\|_Q\le\tfrac12\|f\|_Q,\qquad
\|\Pi_NBr_N\|_Q\le\tfrac14\|r_N\|_Q.
\]

The displacement estimates are

\[
8\|d_N\|_Q^2\le\|r_N\|_Q^2,\qquad
\|1-F_N^P\|_Q^2\le\frac98\|r_N\|_Q^2,
\qquad8\|d\|_Q^2\le\|r\|_Q^2.
\]

Proof mechanism: for r perpendicular to d and the metric normal equation,
<d,(B-I/4)(r+d)>=3||d||^2/4; the centered multiplier bound and Pythagoras
give the factor 8. These Hilbert bounds remain compatible with divergent
scaled tails and do not supply physical boundedness.

## Complete-sum numerical diagnostics

These are diagnostics, not Lean proofs or interval-certified bounds. Pairwise
period grouping uses the exact analytic expressions

\[
A=\frac{\psi_1(a/L)}{\zeta(2)L^2},\quad
D=\frac{\psi((a+1)/L)-\psi(a/L)}{\zeta(2)L},\quad
S=\frac{\psi_1((a+1)/L)}{\zeta(2)L^2},
\]
\[
W_0=A,\quad W_1=A-D,\quad W_2=A+S-2D.
\]

Wolfram confirmed the progression formulas and reproduced the conductor-10
calculation with 50-digit working precision. Larger calculations used double
precision. Let Dmax=N+1, so the physical head is n<Dmax.

| Dmax | epsilon_N | max head abs(b_N) | max Lambda | max epsilon_N Lambda |
|---:|---:|---:|---:|---:|
| 10 | 0.01724870 | 0.01055644 | 0.07367949 | 0.00127088 |
| 20 | 0.01151934 | 0.01598633 | 0.09058097 | 0.00104343 |
| 50 | 0.00790767 | 0.02201528 | 0.22978211 | 0.00181704 |
| 100 | 0.00681020 | 0.04214013 | 0.58320242 | 0.00397173 |
| 150 | 0.00615231 | 0.03801919 | 0.50893302 | 0.00313112 |
| 200 | 0.00587223 | 0.05691090 | 1.12031377 | 0.00657874 |

The reduced Gram matrix on distinct active squarefree conductors had numerical
condition number about 55743 at Dmax=200. The masked formal Gram has zero
columns and is singular. No numerical plateau
or fitted growth rate is asserted. The progression formulas have not been
formalized in this development. The exact metric identities and the
elementary complete-tail forcing bound have been formalized.

## Next research steps

1. Study the signed inverse-Gram action on A_N/d+eta_N,d, with the explicit
   d^(-3/2) remainder above. Prove a common bound for the synthesized physical
   scalar on 1<=n<=N. A coefficient norm depending on N does not suffice.
2. Alternatively bound the centered complementary evaluation kernel,
   retaining its vanishing diagonal and low-coordinate leakage. Only an
   epsilon_N-weighted energy bound is needed for the sufficient K certificate.
3. For the displacement route, exploit the exact finite resolvent forcing,
   not just its uniformly bounded inverse in H_Q. The missing step is physical
   regularity, not invertibility in the Hilbert norm.
4. For a complete-tail route, a diagonal N_j,H_j requires approximation
   errors controlled after multiplication by H_j. The new strong convergence
   alone supplies no such cofinal bound. No provider was obtained here.

The abstract logarithmic-annihilator comparison in the original handoff
still rules out inferring RH from compactness, the tail dichotomy, and these
Hilbert estimates alone. Additional squarefree arithmetic is necessary.

## External context and verification boundary

Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
the Riemann hypothesis*, https://arxiv.org/abs/math/0607733, provides the
analytic background. Ehm, *On certain Gram matrices and their associated
series*, https://arxiv.org/abs/2405.06349, concerns Gram formulas and quadratic
form decompositions. These references supply context; no uniform regularity
provider from either has been used.

All seven new modules passed assembled server verification in job
`job_0Y7Y7ui9ZYJvTsrG86U0X41p9LKl7Fc2` (19.078 seconds reported for
the verification job). Axiom inspection of the signed scalar inequality,
actual forcing bound, finite resolvent, finite displacement estimate, and
conditional RH consumers returned only `propext`, `Classical.choice`,
and `Quot.sound`. The final checkpoint result certifies aggregate validation
and publication; the isolated check alone does not certify publication.
The conditional RH declarations still contain explicit open head-bound
hypotheses. No theorem of type RiemannHypothesis without those domain-specific
premises has been produced.


Continuation workspace: `ws_zCyeA026LTyKnPjK1elHwt1yH05NCoqO`.
Project root: `/home/cri_2025/lean-agent-workspaces/ws_zCyeA026LTyKnPjK1elHwt1yH05NCoqO/RiemannResearch`.
Follow any continuation workspace returned by the publication checkpoint.
