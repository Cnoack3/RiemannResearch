# Complete-source double-log upper budget
7 October 2026 (UTC).

Starting main: f40547638efa74cf3df88fb4dcbb15f4abf973b9.
The requested d8945bd was superseded before this task began by the
complete-tail Mobius head-repair commit. The new repair was reused.

## Exact data and scope

At spectral stage n the ENTIRE legal stage is V_(n+3), with physical
cutoff n+4. Its constructed full eigenbasis, literal
compactSpectrumWeight w_(n,i), and compactSpectrumEigenvalue lambda_(n,i)
are retained. Put

Phi(x) = log(1+log(1+x)),
B_n = sum_i w_(n,i),
T_n = sum_i w_(n,i) lambda_(n,i)/(1+lambda_(n,i)),
S_n = sum_i w_(n,i) lambda_(n,i)/(1+lambda_(n,i))^2,
M_n = sum_i w_(n,i) Phi(lambda_(n,i)).

The already proved exact correction identity remains T_n=J_n+S_n,
with BOTH complete nonnegative squares J_n and S_n present.
The existing actual limits give T_n->delta and S_n->0, where delta
is compactProjectionDefect. No RH premise is used below.

## Unconditional arithmetic eigenvalue cap

The published Mobius interpolation gives ||f||<=12H||Q_Hf||
for every f in the full H-dimensional legal stage.
Nested physical cutoffs imply ||Q_Hf||<=||Q_Nf|| when H<=N.

For each unit head eigenvector b_i, its actual full lift f_i has
||f_i||^2=1+lambda_i. The head square ONE is retained before estimating
the full lift. Thus, for every i and every N>=H+1,

0<=lambda_(H,N,i)<=144 H^2-1.

In the actual sequence this discharges the cap

L_n = compactSpectrumConductorCap n = 144(n+3)^2-1.

Declarations:
- stageHeadLift_norm_le_conductor
- stageEigenvalue_le_conductor_cap
- compactSpectrumEigenvalue_le_conductor_cap

No maximum eigenvalue, spectrum truncation, or stage-conditioning
hypothesis is supplied to the actual application.

## Exact source mass

twoThreeDual has physical values 14,-12,-12 on sites 1,2,3 and
zero thereafter. Hence its full squared Pareto norm is
196/2+144/6+144/12=134.

The existing head-projection identity is specialized EXACTLY:

B_n=134-e_n,
e_n=||twoThreeDual-P_(stageHeadSpace(n+3,n+4))twoThreeDual||^2.

The established actual head-error limit gives e_n->0. Thus B_n<=134
and B_n->134, with no arithmetic approximation assertion.

Declarations:
- twoThreeDual_norm_sq_eq_134
- compactSpectrum_mass_eq_134_sub_headError
- compactSpectrum_mass_le_134
- compactSpectrum_mass_tendsto_134

## Exact complete-source contrast

Set t_(n,i)=w_(n,i)lambda_(n,i)/(1+lambda_(n,i)) and define

P_n = sum_i w_(n,i) Phi(lambda_(n,i))/(1+lambda_(n,i)),
C_n = sum_i t_(n,i)[Phi(L_n)-Phi(lambda_(n,i))].

The PRIMARY result is the exact equality

M_n = Phi(L_n)T_n - C_n + P_n.

Every eigenvalue and source weight occurs in both complete sums.
C_n>=0 because the arithmetic cap applies to EVERY eigenvalue.
This equality is proved BEFORE any upper estimate. The contrast C_n
is retained even in the strongest displayed upper inequality.

Generic declarations in Analysis/FiniteSpectralMomentUpper.lean:
- moment_eq_correctionDoubleLog_add_remainder
- moment_eq_cap_correction_sub_contrast_add_remainder
- doubleLogCapContrast_nonneg

Actual declaration:
- compactSpectrum_doubleLog_exact_contrast

## Cap-independent vanishing remainder

The scalar inequalities are proved:
Phi(x)<=x and Phi(x)^2<=x for x>=0.
For the second, Real.log_one_add_le_sqrt proves log(1+x)<=sqrt(x)
without derivative instances: exp r>=1+r and an exact nonnegative
sixth-degree polynomial at r=sqrt(x)/6 give 1+x<=exp(sqrt(x)).

Weighted Cauchy--Schwarz, keeping all weights, gives

0<=P_n,  P_n^2<=B_n S_n<=134 S_n.

Thus P_n<=sqrt(134 S_n)->0 unconditionally, independently of the
conductor cap and without a rate for S_n. Also, the finite sharper
alternatives P_n<=T_n and P_n<=(1+Phi(L_n))S_n are proved.

Consequently the literal complete moment obeys

M_n <= Phi(L_n)T_n - C_n + sqrt(134 S_n).

The leading coefficient is the ACTUAL correction T_n rather than
the total source mass 134. The source contrast and full tail square
are retained. This improves the crude M_n<=134 Phi(L_n).

Actual declarations:
- compactSpectrumDoubleLogRemainder_le_sqrt_tail
- compactSpectrumDoubleLogRemainder_tendsto_zero
- compactSpectrum_doubleLog_upper_with_contrast

## Natural conductor-scale endpoint

Let A_n=log(1+log(n+3)).
The actual cap satisfies the explicit finite inequalities

A_n<=Phi(L_n)<=A_n+log(3+log144).

Thus Phi(L_n)/A_n->1. The complete actual moment obeys an unconditional
eventual upper floor: for every c>delta, eventually M_n/A_n<c.
No limit of M_n/A_n is postulated.

This is the coefficient-one ENDPOINT, with delta as coefficient.
The already proved canonical normalized lower floor is for
D_n=log(1+log(1/sigma_n)), sigma_n=S_n+1/(n+1).
No decay rate relating S_n to n is assumed. Decreasing a polynomial
eigenvalue-cap exponent cannot give a fixed fractional saving on an
outer-log scale: Phi(n^a)/loglog n->1 for every fixed a>0.

Declarations:
- compactSpectrum_conductor_cap_doubleLog_bounds
- compactSpectrum_cap_doubleLog_scale_ratio_tendsto_one
- compactSpectrum_doubleLog_conductor_upper_floor

## SINGLE sharp unresolved arithmetic estimate

The literal canonical envelope sigma_n=S_n+1/(n+1) is reused.
The scale D_n tends to infinity, and the new proof gives P_n/D_n->0.

The remaining estimate is a concrete LOWER bound for the complete
cap contrast, along a cofinal sequence k_n:

C_(k_n) >= [Phi(L_(k_n))-theta D_(k_n)]T_(k_n)
             -D_(k_n) epsilon_n,

for some fixed theta<1 and epsilon_n->0.

This is precisely the source-weighted cap-deficit quadratic form:

sum_i [w_(k_n,i)lambda_(k_n,i)/(1+lambda_(k_n,i))]
  [Phi(L_(k_n))-Phi(lambda_(k_n,i))].

It is NOT a substituted unspecified tightness provider.
With E_n=epsilon_n+P_(k_n)/D_(k_n)->0, the exact identity yields

M_(k_n)/D_(k_n)<=E_n+theta T_(k_n),

and feeds the EXISTING actual canonical-feedback RH theorem.
The new consumer riemannHypothesis_of_actual_compactSpectrum_cofinal_contrast
constructs this error internally and leaves only the displayed
arithmetic contrast estimate, cofinality, and theta<1.

For any positive D, the exact finite equivalence is also proved:

M/D<=E+theta T
iff
C>=(Phi(L)-theta D)T+P-D E.

Declaration: doubleLog_feedback_iff_cap_contrast.
Hence the retained contrast is a sharp algebraic reformulation, with
the exact positive remainder visible. It is not a new estimate pretending
to discharge the arithmetic gap. The contrast LOWER bound remains OPEN.

## A more concrete sufficient mean estimate

There is also an unconditional finite Jensen upper bound. Define
A=sum_i t_i log(1+lambda_i), T=sum_i t_i>0.
The outer-log tangent cancellation proves

M <= T log(1+A/T)+P.

All correction-weighted first-log source components are retained.
A sufficient arithmetic estimate would be

A <= T[(1+log(1/sigma))^theta-1], 0<=theta<1.

This would give the required strict budget with error P/D.
It is STRONGER than the sharp contrast estimate because Jensen loses
distribution information. It is presented as an arithmetic attack target,
not as an additional proved provider or an extra required RH hypothesis.

Declarations:
- sum_mul_log_one_add_le_log_average
- correctionLogMoment
- doubleLog_moment_le_correction_log_mean_add_remainder

## Why the cap alone cannot close the strict fraction

An INFORMAL finite-spectrum model, not actual conductor arithmetic,
places weight delta>0 at lambda=n and the remaining mass 134-delta
at lambda=n^-2. It retains both positive eigenvalues and all weights.
It has B=134, T->delta, S->0, and highMass(R)->delta for every fixed R>0.
Its eigenvalues obey the polynomial conductor cap.

The canonical envelope is asymptotic to (delta+1)/n, and M/D->delta.
Thus these scalar laws alone permit the exact coefficient-one barrier.
This is not a counterexample to RH or to the actual arithmetic source.
A strict estimate has to use further properties of its source weights.

## Literature and computation

Werner Ehm, On certain Gram matrices and their associated series,
https://arxiv.org/abs/2405.06349, supplies Gram formulas and quadratic-form
decompositions in the NB setting. This supports the arithmetic quadratic-form
perspective; it is not used as a provider of the contrast lower bound.

Bettin--Conrey--Farmer, An optimal choice of Dirichlet polynomials for
the Nyman--Beurling criterion, https://arxiv.org/abs/1211.5191, assumes
RH and a reciprocal zeta-derivative moment bound for its sharp approximation
asymptotic. That conditional result cannot be used here to assert an
unconditional strict complete-source budget.

Wolfram returned True for the derivative polynomial identity and the
exact source/correction/remainder scalar decomposition, and 1 for the
single-weight escape model's normalized moment limit. These calculations
supported development only. The new proofs are checked by Lean.

## Verification and next task

The coherent core passed isolated job_GZixC140ybje4pz5oCDuHbchu_thPGrF
with exit 0 and no output or warnings. The final conductor-scale extension and seven decisive axiom audits passed
job_uh26pB7vH9844ZuGz0e95Jyf4APd4Urh, exit 0, with no compiler warnings.
Every audited declaration depends only on propext, Classical.choice and
Quot.sound. There are no incomplete proofs or project-local axioms in the
added modules. The final repository checkpoint
validates the saved modules and affected dependents before publication.
Only the terminal checkpoint publication is reported as a pushed commit.

Continue by attacking the displayed LOWER bound on the actual complete
cap contrast C_n, using the literal conductor head Gram, full infinite
tail Gram and the compact two--three source. Preserve the exact equality
M_n=Phi(L_n)T_n-C_n+P_n and T_n=J_n+S_n. Do not introduce a maximum-eigenvalue
or remainder provider: these are now discharged. Do not infer a strict
fraction from a polynomial cap, PNT cancellation or scalar tail decay.
