# Microscopic source closure and legal LCM packet refits — 9 November 2026

## Status

This continuation discharges Section 11 of the Ramanujan DPP / LCM handoff.
It removes the independent source-decay premise for moving finite families
of distinct positive actual critical-line zeros, under a uniform microscopic
real-row margin. It does not establish the required remainder upper bound
and does not prove RH.

All spaces, norms, and residue weights below are the complete Pareto objects.
The LCM dictionary contains all nontrivial divisors, including prime powers
and mixed conductors. No physical truncation is substituted for the norm.

## Automatic source decay

Let m be the number of positive ordinates, ell = log(N+1), e = criticalSourceError N,
S = relativeCriticalSourceSq gamma N, and C0 = reciprocalConstant = 2 + EulerGamma - log(4*pi).
The existing exact source identity is

S = sum_i |1 - classMellin N (1/2+i gamma_i) (multiples)|^2 / |1/2+i gamma_i|^2.

The existing source-error estimate bounds its difference from sum_i |rho_i|^-2.
The new finite estimates are

2m/ell <= microscopicRealRowBudget gamma N row,
m/ell <= d/2,
S/ell <= C0/(2 ell) + (d/2) e (4+e).

The last two statements include the empty-family case. For the source inequality,
the ordinates are injective and positive and each is an actual critical-line zero.
The count bound itself requires no zeta-zero hypothesis. Its explicit scalar
hypotheses are N>0 and d>=0. The source theorem has no d<1/2 restriction.

For N_j -> infinity, e_j -> 0, so a uniform row bound yields S_j/ell_j -> 0.
Adding d<1/2 and the existing real Gram energy sandwich gives C_j -> 0.
This is conditional on a row bound, not on RH or a reciprocal-derivative moment.

Main declarations in ParetoResidueMicroscopicSource.lean:

- microscopicCrossBudget_one_le
- microscopicRealRowBudget_card_le
- card_div_log_le_of_microscopic
- criticalSourceError_tendsto_zero
- relativeCriticalSourceSq_div_log_le_of_microscopic
- relativeCriticalSourceSq_div_log_tendsto_of_microscopic
- critical_certificate_tendsto_of_microscopic_actual_zeros

## Full LCM assembly

For a cofinal schedule M_j, the checked exact identity remains

E_(M_j) = w_(L_j)(0) + C_j + R_j.

Under the moving-family hypotheses above, both w_(L_j)(0) and C_j vanish.
The new lcm_moving_remainder_tendsto_limit_of_microscopic identifies the limit:

R_j -> ||1 - P_(full legal closure) 1||_P^2.

Thus the row margin removes a vanishing certificate energy; it does not establish
that the remaining projection distance is zero.

The new riemannHypothesis_of_microscopic_remainder_upper needs only a vanishing
upper budget B_j on R_j, in addition to the row margin and actual-zero hypotheses.
The shifted-trial version uses complete legal trials f_j and their exact identity

||errorVector(f_j) - certificateVector_j||^2
  = R_j + ||f_j - lcmBest(M_j)||_P^2.

## A legal finite correction with an exact gain

For an old LCM stage M, put P_M = projection onto its full divisor trial space.
For a Ramanujan packet R_q, define

v = R_q - P_M R_q,
c = <1-F_M, R_q>_P = Lambda(q) - <F_M,R_q>_P,
f = F_M + (c/||v||_P^2) v.

If q is a nontrivial divisor of L_K and M<=K, then f is a legal K-stage trial.
For v != 0, the exact equality is

E_M = E_K + c^2/||v||_P^2 + ||f-F_K||_P^2.

This supplies the finite upper estimate E_K <= E_M - c^2/||v||_P^2.
The residual source c need not vanish for mixed conductors even though Lambda(q)=0.

For possibly different finite families z at M and y at K of actual zeros with
positive real part, away from the pole,

R_y(K) + c^2/||v||_P^2 + ||f-F_K||_P^2
  = R_z(M) + [w_M(0)-w_K(0)] + [C_z(M)-C_y(K)].

The certificate-energy difference is signed and is retained. This avoids assuming
monotonicity of the augmented remainder when the period and zero family change.

## Symbolic and numerical checks (external, not Lean proofs)

Wolfram confirmed the scalar source inequality under its stated sign/count
hypotheses and the scalar square-completion identity for the packet correction.

A simple logarithmically smoothed full-divisor Mobius trial was tested:
a_d = -mu(d)(1-log(d)/log(L)), with f=sum_(d|L,d>1) a_d g_d.
Weights were the complete digamma progression weights
w_L(r) = [digamma((r+1)/L)-digamma(r/L)]/L for 1<=r<=L.

| M | L | Number of nontrivial divisors | Optimum E_M | Trial error |
| --- | --- | --- | --- | --- |
| 2 | 2 | 1 | 0.3068528194 | 1.0000000000 |
| 3 | 6 | 3 | 0.0782932540 | 0.4337268466 |
| 4 | 12 | 5 | 0.0572619221 | 0.4250100114 |
| 5 | 60 | 11 | 0.0333146643 | 0.3697082473 |
| 6 | 60 | 11 | 0.0333146643 | 0.3697082473 |

A separate mixed-packet check at period 6 starts with the prefix span {R_2,R_3}.
The raw target source of R_6 is zero, but its screened source is approximately
0.1742979016, with innovation squared norm 1.7405085468. The resulting gain
0.01745452993 equals the difference between the prefix error 0.09574778393
and the full-divisor error 0.07829325400. This is external numerical evidence
for the exact general refit identity, not a rational certificate for these values.

These finite calculations neither prove nor disprove asymptotic convergence.
They do not supply the missing upper bound.

## Published context and next obligation

- Burnol, A lower bound in an approximation problem involving the zeros of the
  Riemann zeta function, Adv. Math. 170 (2002), 56–70:
  https://arxiv.org/abs/math/0103058. Supports the zero-certificate/lower-bound context.
- Balazard–de Roton, Sur un critere de Baez-Duarte pour l'hypothese de Riemann:
  https://arxiv.org/abs/0812.1689. The global upper rate assumes RH.
- Bettin–Conrey–Farmer, An optimal choice of Dirichlet polynomials for the
  Nyman–Beurling criterion, Theorem 1:
  https://arxiv.org/abs/1211.5191. Its complete classical trial estimate assumes RH
  and a reciprocal zeta-derivative moment bound.
- Hough–Krishnapur–Peres–Virag, Determinantal Processes and Independence:
  https://arxiv.org/abs/math/0503110. Supplies the DPP context, not a remainder estimate.

Open: produce a cofinal family of legal corrections with a quantitative complete
error budget tending to zero, or control accumulated screened packet gains strongly
enough to force the full projection distance to zero. Finite strict improvements,
sparse original source, and the microscopic row margin alone do not provide this.

## Focused verification evidence

- Source module check: `job_UzHdE_uTvA6IPp0w3OTINwZRkGbNWSFc`,
  Bazel / BuildBuddy, succeeded with verified=true; server duration 61.769 seconds.
- Final combined import and guarded transitive axiom audit:
  `job_FZ_LXoov4X_Y0rmkNtaoRjKRJDmdGAY9`, Bazel / BuildBuddy,
  succeeded with verified=true; server duration 80.290 seconds.
  [BuildBuddy audit invocation](https://app.buildbuddy.io/invocation/5c2799c2-10fd-421a-a074-f24abd325841).
- The guarded audit checked these four declarations: the automatic certificate
  theorem, the microscopic remainder RH criterion, the exact refit error
  completion, and the signed remainder transition. Each had exactly
  `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
- Axiom checks do not discharge hypotheses in the theorem types. The row margin
  and the remainder upper budget remain the explicit obligations stated above.
- The final publication checkpoint performs the full `//:RiemannResearch`
  validation. The focused audit alone is not a whole-project build.
