# Actual hyperbolic lower bounds and the signed bad-row provider

Follow-up: [LandauHilbertSchmidt20261005.md](LandauHilbertSchmidt20261005.md)
verifies the 1/3 support strengthening and logarithmic gain, updating the
earlier paper-only status. [ActualZeroOptimizedDensity20261005.md](ActualZeroOptimizedDensity20261005.md)
records the checked count consumer and its separate Open analytic provider.

Research date: 2026-10-05.
Base: 9c8940313d0ff4d49065e4c3902fb677b6b53f6a.

## Exact object and sign

Let N=Ncount(0,T), and enumerate every copy of every actual nontrivial zeta zero
rho=beta+i gamma with 0<gamma<=T. Analytic multiplicities are unchanged.
Coordinates are n=1,...,d, including composites. Put a_rho=beta-1/2 and
x_n=log n-(log d)/2. The repository operator has entries

H_nm = N^(-1) sum_rho cosh(a_rho(log n-log m))
                           exp(+i gamma(log n-log m)).

The concrete analysis rows use M_rho,n=N^(-1/2) exp(-i gamma log n).
This negative row phase makes the generic scalar form agree with the standard
complex operator quadratic convention <f,Hf>. Positive row phases instead
evaluate that operator on conjugated coefficients. The transpose bridge is
explicit, not a tacit change of convention.

Write C_rho,n=cosh(a_rho x_n)M_rho,n and
S_rho,n=sinh(a_rho x_n)M_rho,n. The exact identity is

$$
\operatorname{Re}\langle f,Hf\rangle=\|Cf\|^2-\|Sf\|^2.
$$

No simplicity, distinct-ordinate, density or RH premise occurs.

## Full arithmetic decomposition and unconditional lower estimate

Keep the complete arithmetic operator A: diagonal zero; for n<m its entry is
Lambda(m/n)/sqrt(m/n) if n divides m and zero otherwise; reflect symmetrically.
Pairs where either endpoint is composite are included. Put tau=T/(2 pi N).
The original signed residual is E=H-I+tau A, hence

$$
H[f]=\|f\|^2-\tau A[f]+E[f].
$$

The reindex bridge from Ioc(0,d) to Fin d is proved explicitly before using the
existing arithmetic Schur estimate. For T>=0,

$$
H[f]\ge
\left(1-\frac{T(\log d+\log4+4)}{2\pi N(T)}-\|E\|\right)\|f\|^2.
$$

This discharges the FULL hyperbolic-form lower bound whenever the displayed
finite scalar coefficient is nonnegative. It does not identify a phase Gram
or a physical Pareto Gram with H.

A stronger exact ground-state identity retains the arithmetic graph square.
With w_n=n^(-1/2), define R_d(n)=log n+sum_{q<=d/n}Lambda(q)/q. Then

$$
A[f]=\sum_{n\le d}R_d(n)|f_n|^2
-\sum_{\substack{mq\le d\\q\ge2}}\frac{\Lambda(q)}{mq}
 \left|\sqrt{mq}f_{mq}-\sqrt m f_m\right|^2.
$$

Consequently H is its diagonal term PLUS tau times this complete nonnegative
graph square PLUS the signed residual form. Estimating only the residual gives
a coefficientwise lower bound. The formal finite graph expression uses one
half of the full ordered-pair sum, equivalent to the displayed divisibility
edge sum; it preserves every edge and all complex coefficients.

The existing actual residual theorem gives ||E||->0 at
log d<=a+(2/7)log(T+3). The existing sharp zero-count normalization gives every
eventual N>=c T log T with c<1/(2 pi). Thus for any
0<=theta<=2/7, log d<=a+theta log(T+3), and h<1-theta, eventually

$H[f]\ge h\|f\|^2\qquad\text{uniformly for every coefficient vector }f.$

In particular every h<5/7 is valid at d=O(T^(2/7)). At
log d=O(sqrt(log T)), every h<1 is valid. Neither statement needs density.

The leading logarithmic arithmetic loss is sharp. The harmonic Schur vector
w has exact Rayleigh quotient 2 sum_(n<=d)(log n)/n / sum_(n<=d)1/n;
it is log d+O(1). Combined with the existing arithmetic upper bound,
lambda_max(A)=log d+O(1). Use the full count asymptotic
N(T)~T log T/(2 pi), including its matching upper bound, for the next conclusion. At d asymptotic to a positive constant times T^theta,
0<theta<=2/7, the exact Hermitian perturbation estimate gives
lambda_min(H)->1-theta. These spectral asymptotics are paper consequences
unless listed as checked declarations below.

## Full form versus a shrinking good-zero mask

The improved centered support theorem uses rows with |a_rho|<=delta(T).
The global actual bound is only |a_rho|<1/2. One cannot insert a shrinking
delta into the all-copy theorem. Define H_bad using the strict boundary
|a_rho|>delta and the ORIGINAL full N normalizer. Then exactly

$$
H_{\mathrm{good}}=H-H_{\mathrm{bad}},\qquad
H_{\mathrm{bad}}[f]=\|C_{\mathrm{bad}}f\|^2-\|S_{\mathrm{bad}}f\|^2.
$$

H_bad is generally indefinite. In particular it is not legitimate to delete
its negative sinh term, assume positivity, or replace H_bad by the
existing badCorrection: badCorrection=H_bad-G_bad.

The weakest exact missing provider for a prescribed h_minus is

$$
\forall f,\qquad
H_{\mathrm{bad}}[f]\le H[f]-h_-\|f\|^2.
$$

The formal surplus equivalence states precisely this condition.
The concrete good-row matrix keeps every original row slot, zeroes strict-bad
rows, and zeroes their irrelevant displacement. Its exact hyperbolic form is
H_good; its centered-frame theorem consumes the signed provider directly. A useful
independent sufficient provider is the one-sided estimate H_bad<=B I, giving

    H_good >= (h_full-B) I,
    h_full=1-tau(log d+log4+4)-||E||.

For a positive centered frame gap it suffices that
h_full-B > ((cosh(delta*b)-1)/2)^2 ||V_good||^2, b=(log d)/2.
No RH-strength condition is being inferred from this reduction. An actual
zero-density specialization is one possible provider, and remains explicitly
open in Lean.

## Sharper signed rank-two tail budget (paper proof)

For one zero copy, remove only its 1/N normalization and write
u_n=exp(a x_n)exp(+i gamma log n), v_n=exp(-a x_n)exp(+i gamma log n).
Its hyperbolic form is Re(<u,f> conjugate(<v,f>)). Its exact C/S difference is
unchanged. The two possible nonzero eigenvalues are

$$
\lambda_\pm=\frac{d\pm\sqrt{S_d(2a)S_d(-2a)}}2,
\qquad S_d(t)=\sum_{n\le d}n^t.
$$

Proof: the sum/difference channels are a rank-two form; their trace is d,
and their determinant on their span is minus
(||c||^2||s||^2-|<c,s>|^2). The discriminant equals
(sum exp(2a x_n))(sum exp(-2a x_n)).
Equivalently rescale u,v to equal norms and use orthogonal sum/difference
directions. The negative eigenvalue is retained explicitly. Coordinate
translation and the phase cancel from this discriminant.

Set W_d(t)=(d+sqrt(S_d(2t)S_d(-2t)))/2. It is increasing for t>=0:
the product is d+2 sum_(n>m)cosh(2t log(n/m)). Cauchy gives it at least d^2.
For |a|<1/2,

$$
W_d(|a|)\le W_d(1/2)
=\frac{d+\sqrt{d(d+1)H_d/2}}2=O\!\left(d\sqrt{\log d+1}\right),
\qquad H_d=\sum_{n\le d}\frac1n.
$$

Thus a sufficient, substantially simpler scalar provider is

$$
\frac{\mathrm{strictTail}(T,\delta)}{N(T)}\,W_d(1/2)\le B.
$$

The finer sufficient budget is
N^(-1) sum_bad multiplicity*W_d(|beta-1/2|). Lean also proves the fully finite
budget using the actual normalized exponential-vector norms and cross inner
product: sum_bad (||u|| ||v||+Re<u,v>)/2. Identifying this cap with the closed
power sums and harmonic upper cap is a paper calculation here. The uniform cap improves the
old elementary O(d^(3/2)) per-zero bound while preserving the negative square.
For arbitrary coefficients this is a valid upper bound on the signed form,
The explicit eigenvalues give lambda_plus>=|lambda_minus| because d>=0;
applying the triangle inequality therefore gives the same absolute tail-norm
budget. This absolute claim uses the per-row spectral calculation, not the
one-sided provider alone.

For d>=1 and 0<=delta<=1/2, the exact strict-tail layer-cake formula for the differentiable W_d is

 B_weighted = N^(-1)[W_d(delta) strictTail(T,delta)
             + integral_delta^(1/2) W_d'(t) strictTail(T,t) dt].

The upper endpoint and the strict-boundary convention are retained. A density
law K exp(-q t)+E yields an additive remainder E W_d(1/2)/N, not an
unweighted E and not zero.

## What published density can supply, and what remains in Lean

Chourasiya--Simonic, arXiv:2507.15184v2, Corollary 1 gives a uniform
unconditional near-line density bound on closed sigma intervals, with
N(1/2+s,T) <= C T exp[-4s log(T)/(3-2s)] (log T)^3 plus logarithmic
remainders. Reflection gives exactly strictTail(T,delta)=2 #copies{beta>1/2+delta},
hence strictTail(T,delta)<=2 N(1/2+delta,T). The published count uses beta>=sigma,
so equality at its closed threshold is not asserted. The fixed finite-height certificate can alternatively be retained as
a fixed additive initial count.

Let L=log T and ell=log d=O(sqrt L), and choose
delta=(3/4)(ell+4 log L)/L. Since 4s/(3-2s)>=4s/3, the count-only budget above
is O(sqrt(ell+1)/L^2), plus an exponentially small fixed/logarithmic-count
remainder; hence H_bad tends to zero. Together with H-I->0 this gives
H_good->I at paper level. Also delta*(ell/2)->3c^2/8 when ell~c sqrt L,
so the established centered constant is consistent with this provider.
This uses an unconditional density theorem; it is not an RH assumption.
It is not an actual-zeta Lean provider merely by citation.

More precisely H_good->I supplies h_minus=1-eta for any eta>0 eventually.
Writing z=cosh(3c^2/8), applying the existing finite moment argument to the good mask gives
||V_good|| <= (1+o(1))/sqrt(2-z^2) when z<sqrt 2. The centered row transfer
then gives

    liminf s_min(V_good) >= [2-(z-1)/sqrt(2-z^2)]/(1+z).

This is positive precisely when z<7/5, hence c<centeredSupportConstant.
Adding back the complementary phase rows can only increase phase energy.
This completes the paper-level actual centered-frame application from a known
unconditional density estimate, while its analytic Lean provider remains Open.

Remaining formal analytic obligation: provide a strict-tail count (or,
more weakly, the signed form surplus) strong enough for the displayed finite
budget. Fully screened physical Pareto transfer remains a different open
obligation.

## Provenance and verification scope

The exact finite identities and their assembly are developed here using the
repository's actual zero definitions, arithmetic Schur/Mertens results,
Landau residual and zero-count providers. Primary analytic sources:
[Gonek (1985), Theorem 1](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf)
[Ford--Zaharescu, Lemmas 1--2](https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf)
[Chourasiya--Simonic, Corollary 1](https://arxiv.org/html/2507.15184v2)

The citations support analytic strategy/known density, not added axioms.
Paper spectral/tail consequences are separated above from checked declarations.

The following principal declarations passed a coherent Lean run and individual
`#print axioms` audits:

- `ZeroSamplingQuadratic.weighted_groundState_identity`
- `CenteredHyperbolicFrames.rankTwoCross_form_upper`
- `ActualZeroPhaseMoments.actualHyperbolic_rows_eq`
- `ActualZeroPhaseMoments.landauGram_form_lower_graph`
- `ActualZeroPhaseMoments.eventually_landauGram_lower_power_support`
- `ActualZeroPhaseMoments.actual_full_centered_frame_lower`
- `ActualZeroPhaseMoments.signedBadHyperbolic_form_exact`
- `ActualZeroPhaseMoments.goodHyperbolic_lower_iff_signed_surplus`
- `ActualZeroPhaseMoments.actual_good_centered_frame_lower_of_signedBad`
- `ActualZeroPhaseMoments.signedBadHyperbolic_upper_budget`

Each audit lists only `propext`, `Classical.choice` and `Quot.sound`.
The masked-frame theorem's signed-tail hypothesis remains visible in its type;
an axiom audit does not discharge the application's small-tail inequality.
The complete base project was built successfully before checking these proofs.
Publication acceptance additionally builds the saved modules and their affected
local dependents. No paper spectral asymptotic, closed harmonic cap, actual
density theorem or screened physical Pareto transfer is being relabeled as a
Lean-verified result.
