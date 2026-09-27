# Truncation, exponent conditions, and the subhalf arithmetic gap

The compiled power and critical-log modules and the corrected profile module
also passed axiom checks in job_jdm99_Jm71NBWqSqXiYgqs5eiMKRd-7_.

Date: 2026-09-27. Requested continuation: 3d085c93bdf1ab3a46300e4c970c65a5e9ed7f69.
Audited working base: 71373f871760625d9bc48b948b21f4ab3f3265da, which also contains
uniform half-range convergence, normalized subhalf cancellation, and completed
subhalf head-growth results. Those completed results are retained.

## Result and status

The truncation-and-dominated-convergence argument now has:

1. A general signed-profile criterion with no assumed limiting finite energy.
2. A complete strict power criterion, including a constructed integer cutoff.
3. A complete critical logarithmic criterion, including a constructed integer cutoff.
4. Exact algebraic tests for the power and logarithmic exponent thresholds.

These are established analytic implications. Their specialization to an actual
fixed damping below one half remains a **conditional research reduction**:
the required signed prefix and density-tail estimates have no verified
subhalf provider in the audited repository.

No fixed epsilon in (0,1/2) has been established by this audit. RH remains open.

## Definitions and exact truncation

For real arithmetic weights w with w(0)=0, write

~~~math
P(t)=\sum_{1\le d\le t}w(d),\qquad
c_M=\sum_{1\le d\le M}\frac{w(d)}d,\qquad
c=\sum_{d\ge1}\frac{w(d)}d,
~~~

where convergence of the last scalar series is an explicit hypothesis in the
generic theorem. For Mobius weights w(d)=mu(d)d^(-epsilon), epsilon>0,
the checked declaration dampedMobius_density_hasSum supplies it unconditionally,
with c=Re(1/zeta(1+epsilon)).

The finite Hilbert vector and its forced coordinate limit are

~~~math
F_M(n)=-\sum_{d\le M}\frac{w(d)}d(n\bmod d),\qquad
g(n)=\sum_{d\le n}w(d)\lfloor n/d\rfloor-nc.
~~~

The Pareto norm uses positiveWeight(n)=1/[n(n+1)] for n>=1, and weight zero at n=0.
For w_M(d)=w(d)1_{d<=M}, all of the following identities are exact:

~~~math
P_M(t)=P(\min(M,t)),
~~~

~~~math
c_M-\sum_{d\le t}\frac{w_M(d)}d
=
\begin{cases}
0,&M\le t,\\
(c-P_w(t))-(c-P_w(M)),&M>t,
\end{cases}
\qquad P_w(t)=\sum_{d\le t}\frac{w(d)}d.
~~~

Thus a nonnegative increasing prefix envelope U survives truncation with the
same constant, and a nonnegative decreasing density-tail envelope T survives
with a factor at most two. These statements are now independent of any
particular exponent or logarithm.

For 1<=y<=n and q=floor(n/y), the full signed hyperbola decomposition is

~~~math
F_M(n)=
-\sum_{d\le y}\frac{w_M(d)}d(n\bmod d)
+\sum_{k=1}^{q}P_M(\lfloor n/k\rfloor)
-qP_M(y)
-n\left(c_M-\sum_{d\le y}\frac{w_M(d)}d\right).
~~~

If the first, signed residue sum is bounded in modulus by R(n,y), uniformly
in M, an exact valid majorant is

~~~math
H(n,y)=R(n,y)+\sum_{k=1}^{\lfloor n/y\rfloor}U(\lfloor n/k\rfloor)
+\lfloor n/y\rfloor U(y)+2nT(y).
~~~

For any integer cutoff Y(n) with 1<=Y(n)<=n eventually, the hypothesis

~~~math
\sum_{n\ge1}\frac{H(n,Y(n))^2}{n(n+1)}<\infty
~~~

implies existence of a Hilbert vector with coordinates g and full natural-order
norm convergence F_M->g. Finite energy of g is a conclusion, not a premise.
This is arithmeticFloorHilbertPartial_tendsto_of_profiles.

The bound R(n,y)=sum_{d<=y}|w(d)| is available unconditionally. It is deliberately
not required: a genuinely signed residue-head estimate can replace it.

## Strict power criterion

Consider the unresolved range 0<epsilon<=1/2; larger dampings already have
unconditional convergence. Put p=1-epsilon. Assume nonnegative W,B,D and

~~~math
|w(d)|\le Wd^{-\varepsilon},\qquad
|P(t)|\le Bt^a,\qquad
|c-P_w(t)|\le Dt^{-d_0},
\quad 0\le a<1,\quad d_0\ge0.
~~~

The proved conductor-uniform bound, for every M and 1<=y<=n, is

~~~math
|F_M(n)|\le
\frac{W}{1-\varepsilon}y^{1-\varepsilon}
+B\left(1+\frac1{1-a}\right)ny^{a-1}
+2Dny^{-d_0}.
~~~

Let r=min(1-a,d_0). If r>p, choose

~~~math
y=\left\lfloor n^{1/(p+r)}\right\rfloor,\qquad
\beta=\frac{p}{p+r}.
~~~

The integer-cutoff theorem proves, eventually and uniformly in M,

~~~math
|F_M(n)|\le
\left[\frac{W}{1-\varepsilon}
+2^r\left(B\left(1+\frac1{1-a}\right)+2D\right)\right]n^\beta.
~~~

Since beta<1/2, its full Pareto square is summable. Consequently,

~~~math
\boxed{a<\varepsilon,\qquad d_0>1-\varepsilon}
~~~

suffice for full norm convergence. The Möbius specialization is
dampedMobius_cutoffs_converge_of_prefix_density_powers.

Sharpness here has a precise limited meaning. Lean proves that a power cutoff
y=n^t, 0<t<=1, can make all three majorant exponents strictly below one half
if and only if the displayed conditions hold. This is not a necessary
condition for actual convergence, because cancellation was lost between the
three majorant terms.

## Critical logarithms

At the double boundary a=epsilon, d_0=1-epsilon, take a logarithmic shift c_0
with c_0>=6 and b<=epsilon*c_0. This deterministic choice is always possible
when epsilon>0. Assume

~~~math
|P(t)|\le\frac{Bt^\varepsilon}{(c_0+\log t)^b},
\qquad
|c-P_w(t)|\le
\frac{D}{t^{1-\varepsilon}(c_0+\log t)^b},
\qquad b>1.
~~~

The exact derivative of x^epsilon/(c_0+log x)^b is

~~~math
x^{\varepsilon-1}(c_0+\log x)^{-b}
\left(\varepsilon-\frac b{c_0+\log x}\right).
~~~

The shift condition makes this nonnegative for x>=1. Hence the original
signed prefix estimate, not an additional uniform-conductor assumption,
supplies the truncated prefix estimate. The density profile is decreasing.

After truncation and comparison with L(n)=6+log n, the hyperbola bound has
the form A y^p+B_0 n/[y^p L(y)^b], where

~~~math
p=1-\varepsilon,\qquad A=W/p,\qquad
B_0=B(1+1/p)+2D.
~~~

The formal proof chooses the actual integer

~~~math
y=\left\lfloor
\left(\frac{n}{L(n)^b}\right)^{1/(2p)}
\right\rfloor.
~~~

For log n>=64(b+1)^2+100 it proves, with x=(n/L(n)^b)^(1/(2p)),

~~~math
1\le y\le n,\qquad x/2\le y\le x,\qquad L(y)\ge L(n)/4,
~~~

and therefore

~~~math
|F_M(n)|\le (A+B_0\,2^p4^b)\frac{\sqrt n}{L(n)^{b/2}}
\quad\hbox{for every }M.
~~~

The squared envelope is summable because b>1. This proves
arithmeticFloorHilbertPartial_tendsto_of_critical_log_bounds and its actual
Möbius specialization dampedMobius_cutoffs_converge_of_critical_log_bounds.
At epsilon=1/2, b=3/2, c_0=6, this has exactly the 3/4 physical logarithmic
saving of the established endpoint.

Independent critical logarithmic exponents b and e are also formalized:
arithmeticFloorHilbertPartial_tendsto_of_critical_two_log_bounds uses
b_0=min(b,e)>1 and physical saving b_0/2.

For the broader power/log ansatz the exponent bookkeeping is:

| Prefix/tail powers | Logarithmic condition on the critical terms |
|---|---|
| a<epsilon and d_0>1-epsilon | No logarithmic saving is needed |
| a=epsilon and d_0>1-epsilon | Prefix logarithmic exponent >1 |
| a<epsilon and d_0=1-epsilon | Density logarithmic exponent >1 |
| a=epsilon and d_0=1-epsilon | Both logarithmic exponents >1 |
| a>epsilon or d_0<1-epsilon | Fixed logarithmic powers cannot repair this majorant |

The pure-power and double-critical analytic implications are directly
formalized. The one-critical rows follow analytically by absorbing a logarithm
into the other term's strict power margin; they are not advertised as additional
named arithmetic corollaries in this change. The general profile theorem
does not impose any power/log restriction.

Lean also proves the exact single- and double-critical logarithmic feasibility
inequalities. These are sharp within the pure logarithmic-power scale.
At the exponent-one boundary, additional iterated-log savings can still make
a profile summable; the general profile criterion permits this.

## Audit of verified arithmetic inputs

| Verified declaration/module | What it supplies | Subhalf gap |
|---|---|---|
| dampedMobius_half_prefix_log_bound | a=1/2, logarithmic saving 3/2 at epsilon=1/2 | No subhalf prefix provider |
| dampedMobius_half_density_tail_log_bound | d_0=1/2, logarithmic saving 3/2 at epsilon=1/2 | No subhalf critical tail provider |
| dampedMobius_density_tail_le | For every epsilon>0, density error <=M^(-epsilon)/epsilon | d_0=epsilon<1-epsilon below half |
| DampedMobiusUniformHalfRange | Uniform approximation and signed bounds for all epsilon>=1/2 | Its decreasing-weight transfer does not descend below half |
| DampedMobiusSubhalfNormalization | ||F_epsilon,M||/(M+1)^(1/2-epsilon)->0; normalized energy and signed heads also vanish | The normalization grows; no fixed power improvement or unnormalized bound |
| DampedMobiusCenteredHeadGrowth | Actual completed-conductor head energy divided by (H+1)^(1-2epsilon) tends to zero | Still compatible with unbounded actual energy |
| dampedMobius_cutoffs_converge_of_raw_signed_growth | Raw signed norm exponent theta gives convergence when theta<epsilon | The norm-growth estimate remains a hypothesis |
| DampedMobiusSparseHeadDichotomy | Frequently bounded signed moving heads suffice for finite energy | The signed bound itself remains open; membership is not full norm convergence |

The benchmark pair a=1-epsilon, d_0=epsilon is the elementary/PNT-shaped power
scale, not a claim that this audit found a named general-epsilon logarithmic
prefix theorem. The actual general-epsilon density provider and the actual
half-prefix provider above were inspected separately.

No audited verified provider supplies either new subhalf criterion.
The existing normalized limits do not contradict failure of finite energy.

## Smallest missing estimates and logical strength

Within the three-positive-majorant power method, improve the benchmark pair by
a common delta:

~~~math
a=1-\varepsilon_0-\delta,\qquad d_0=\varepsilon_0+\delta.
~~~

Lean proves the exact feasibility condition

~~~math
\boxed{\delta>1-2\varepsilon_0.}
~~~

At equality, a critical logarithmic saving greater than one in both inputs
suffices. Thus the deficit is 1-2epsilon_0 in both exponents, with a strict
power margin or the stated boundary logarithmic improvement. These are still
arithmetic obligations. A prefix-only claim must additionally supply the
corresponding Abel density-tail transfer; the formal theorem keeps both inputs.

An alternative signed route already in the repository needs, for a fixed
epsilon_0>0,

~~~math
\boxed{
\exists C\ge0,\ \exists\theta<\varepsilon_0,\quad
\forall M\ge1,\quad \|F_{0,M}\|\le CM^\theta .
}
~~~

The actual raw provider only proves ||F_0,M||/sqrt(M+1)->0. Replacing this with
any fixed positive power saving would permit some fixed damping below half.
No such provider was found. This estimate concerns the complete signed Hilbert
vector, including its infinite physical tail.

For finite energy alone, the existing frequently-bounded signed moving-head
criterion is a more direct target. It must not be confused with full
natural-order strong convergence.

These scalar prefix criteria should not be pursued as equivalent conditions
at all small dampings. Inverse Abel summation converts a prefix exponent a
for mu(d)d^(-epsilon) to a Mertens exponent a+epsilon. In particular the strict
condition a<epsilon at epsilon<=1/4 asks for an exponent below one half.
At epsilon=1/4 the critical logarithmic condition similarly forces
M(x)/sqrt(x)->0. Such behavior conflicts with known unconditional
square-root oscillations of M(x). This limitation is an analytic audit
observation, not a newly formalized lower-bound theorem. It explains why
the general criterion leaves the signed residue head R available for
cancellation instead of requiring absolute coefficient mass.

One fixed positive damping with finite energy is not identified here with RH.
The checked BurnolFixedDampingObstruction theorem gives shifted-zero
propagation; common shifted zeros have not been excluded.
Finite energy at positive dampings approaching zero is RH-strength, as the
existing riemannHypothesis_of_centered_damped_square_summable theorem proves.
The energy constants need not be uniform in damping. That hypothesis remains
**Open**.

## Files, verification, and provenance

The generic components extend ParetoDominatedConvergence and
ArithmeticFloorTruncationBounds. New modules:

- Analysis/HyperbolaExponentOptimization.lean
- Analysis/HyperbolaLogOptimization.lean
- Analysis/PowerLogProfiles.lean
- RH/ArithmeticFloorHyperbolaPowerBounds.lean
- RH/ArithmeticFloorProfileCriterion.lean
- RH/ArithmeticFloorPowerConvergence.lean
- RH/ArithmeticFloorLogConvergence.lean

All are exported from RiemannResearch.lean. Source proof checks passed with
exit_code=0 and verified=true. The main power, general-profile, critical-log,
two-log, and exponent-gap declarations have only propext, Classical.choice,
and Quot.sound in their axiom reports. Their substantive arithmetic hypotheses
are visible in the declaration types; an axiom report does not discharge them.
The final checkpoint performs module and reverse-dependent validation before
publication.

Decisive source checks:
job_NEz6U1D8uqtYe1SSHsH5ElAOmyzKsU2b (power/profile),
job_XoGbqoUpuUrcytr_2I6EuO8eCCTVj9fR (full critical logarithms),
job_R5byshOk7Lrvw2ZVaaXliiQa0K8SH_gx (independent logarithms and exact gap).

The proof strategy abstracts the existing endpoint proof at commit 3d085c93
and the classical Dirichlet hyperbola decomposition. No novelty claim is made.
For the underlying damping/finite-energy context see J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann Zeta function and a
Theorem of Baez-Duarte", Section 4, https://arxiv.org/abs/math/0202166.
For the external square-root Mertens obstruction used only in the analytic
audit, see N. Ng, "The distribution of the summatory function of the Mobius
function", Introduction, especially pp. 4-5,
https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf.
Neither reference is used as an unproved Lean axiom.
