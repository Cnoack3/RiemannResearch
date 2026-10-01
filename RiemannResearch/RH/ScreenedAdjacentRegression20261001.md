# Screened-gap continuation: exact adjacent-weight regression and odd-charge contrasts

Date: October 1, 2026 UTC.
Research base: `78e1dcaa2a0acdb7aa117425a6231cc1c95442b1`.
Verification-record base and workspace HEAD before edits:
`869793eec9c75340d53c48c56240616960c6195f`.

## Outcome and status

This continuation proves an additional unconditional lower certificate for the
ACTUAL screened scatter. It replaces inverse Schur-pivot weights by explicit
full-tail adjacent-residue weights, keeping the actual signed numerators and
both comparison remainders. The new certificate has its own complete binary
tree and fixed-base/moving-CRT summability transfer. Its moving numerator is
exactly a finite inverse-Gram screening of one explicit odd reciprocal-square
charge, with every old dictionary row retained.

No positive lower bound for the actual pooled gap, no divergent signed
certificate series, no capacity divergence and no proof of RH is established.
The nonsummability and finite unbounded-budget hypotheses below remain **Open**.
These are new checked repository assemblies of elementary regression and
existing arithmetic identities; no mathematical-priority claim is made.

## Exact unconditional comparison

Put p=n+3, a_n=factorialPrimeDelta(n)>0, eta_n=schurEta(n+1),
w_n=primeSchurWeight(n), and t_n=adjacentSchurTrial(n). The repository proves

K_n=||t_n||^2=[H_(p-1)-(p-1)/p+R_(p-1)]/p^2,
0<=R_(p-1)<= (p-1)/p, and 0<sigma_(n+1)<=K_n.

Here R is the literal infinite adjacentResidueRemainder, not a deleted tail.
Define v_n=1_(p prime)/K_n and h_n=1_(p prime)*p^2/H_(p-1).
All three weights are proved to satisfy 0<=h_n<=v_n<=w_n.

For a block I=[N,N+k), let U_v=sum_I v_n*a_n^2,
Z_v=sum_I v_n*a_n*eta_n and

V_v(I)=sum_I v_n*(eta_n-(Z_v/U_v)*a_n)^2.

The actual original scatter uses b_n=factorialPrimeError(n), X_w=sum w*a*b
and U_w=sum w*a^2. Its survivor slope is lambda_w=1+X_w/U_w.
The new exact identity is

S_w(I)=V_v(I)+U_v*(lambda_w-Z_v/U_v)^2
       +sum_I (w_n-v_n)*(eta_n-lambda_w*a_n)^2.

No absolute value is taken before centering, and both remainder squares stay
in the equality. Consequently V_h(I)<=V_v(I)<=S_w(I).
The analogous exact identity for h is also proved.

The new adjacent-weight bound and the older harmonic source floor times the
ORIGINAL w-weighted pooled gap are distinct lower certificates. No pointwise
domination between those two certificates is asserted: their pooled slopes
use different weights. The proved hierarchy concerns centered scatter under
h, v and w, with the same actual signed eta rows.

Declarations: primeBlockVariance_eq_adjacentSurvivor_remainders,
harmonicPrimeSurvivorVariance_le_adjacent,
adjacentPrimeSurvivorVariance_le, and
adjacentPrimeRegressionWeight_eq_full_tail.
The reusable zero-source regression completion and weight-remainder identities
live in Analysis/WeightedScalarEnergy.lean.

## Actual adjacent moments and complete split accounting

The exact actual signed numerator is
eta_n=-inner(t_n,tailMinimum(n+1)).
Thus V_v is a regression of actual adjacent moment pairings; screening in
tailMinimum has not been replaced by a raw CRT expression.

For the original pooled slope,
X_w/U_w=(sum_I w_n*a_n*eta_n)/U_w-U_w/U_w.
The last quotient is explicitly retained at zero-source blocks. In two
positive-source children the two constant quotients cancel, identifying
the original gap G with the difference of actual pooled survivor slopes.
primeBlockSlope_eq_adjacent_moment formalizes this identity without positivity
hypotheses and without losing the zero-source boundary term.

For consecutive children, the new scatter has the full merge identity

V_v(parent)=V_v(left)+V_v(right)
 +U_left*U_right/(U_left+U_right)
   *(Z_right/U_right-Z_left/U_left)^2.

It remains valid for empty prime children. Singletons have zero scatter.
adjacentPrimeSurvivorVariance_eq_tree resolves every internal split exactly.

The initial capacity and every remaining channel stay in the equality

C_(2^J+1)=C_1+meanMismatch_(2^J)
 +sum_(j<J) adjacentTree(2^j,j)
 +sum_(j<J) regressionRemainder(2^j,2^j)
 +sum_(j<J) historicalDrift(2^j,2^j)+nonprimeGainBudget(2^J).

Both terms inside regressionRemainder are nonnegative and explicitly defined.
The original scatter can grow through these remainders even if the new
adjacent scatter is summable. The sufficient new criterion is not declared
necessary for RH.

## Source floors support weights, not signs

The new source budgets satisfy the same finite harmonic lower floor:

sum_(n in I,p prime) 1/(4H_(p-1)) <= U_h(I) <= U_v(I).

The first comparison uses the actual checked delta_n>=1/(2p).
harmonicPrimeBlockSourceFloor_le_adjacent_source proves the finite floor.
adjacentPrimeSurvivorVariance_ge_floor_gap gives the corresponding finite
reduced-floor bound for the NEW v-weighted signed pooled gap.

The previous note's ordinary PNT/Dusart count calculation therefore also
supplies its dyadic source scale for this new model. Its eventual numerical
rate assembly remains ordinary mathematics, not a newly installed Lean PNT
provider. A prime-density estimate supplies no lower bound on either gap.

## Moving CRT contrast becomes a screened odd charge

Take any block test f and source-center it under v:
c_n=f_n-(sum v*a*f/U_v)*a_n. Then sum v*a*c=0.
Let D=sum v*c^2 and L=sum v*c*b.
Exact source cancellation gives L=sum v*c*eta, and L^2/D<=V_v.

Writing B=sum v*c*inner(tailInnovation(n+1),base), the moving off-diagonal
CRT numerator A=sum v*c*sum_(m<n) factorialPrimeCrossGram(n,m) satisfies L=A+B.
The complete signed square is retained:

L^2/D=A^2/D+2AB/D+B^2/D.

Bessel and v<=w show sum_j B_j^2/D_j<infinity for every fixed Hilbert vector,
with arbitrary changing tests on disjoint dyadic blocks. Therefore

Summable(A_j^2/D_j) iff Summable(L_j^2/D_j).

No growing vector or packet is declared fixed. The new sum comparison uses
the ACTUAL innovations and retains their screening.

Source centering also cancels the diagonal of the full CRT row, so exactly

A=sum_(n in I) v_n*c_n*
 [q_(n+1)-sum_(i<n+1) inverseCoeff(n+1,i)*q_i],

where q_i=coprimeObservationDefect(2,i+2) is explicitly

q_i=0 if i+2 is even,
q_i=pi^2/[(pi^2-8)*(i+2)^2] otherwise.

This is adjacentPrimeMovingCRTContrastPairing_eq_screened_charge.
Every inverse coefficient on the old full dictionary is kept. In particular
odd composite rows cannot be replaced by prime rows. Summability of the raw
q_i (whose exact sum is pi^2/8) is not a bound on its screened innovations.

## Weakest explicit remaining arithmetic provider

For any selected changing balanced tests, define E_j=A_j^2/D_j with real
division giving zero at D_j=0. The finite aggregate requirement is exactly

for every real B, there exists J with sum_(j<J) E_j>B.

riemannHypothesis_of_adjacentMovingCRTContrast_unbounded proves that this
explicit hypothesis suffices for RH. It is the weakest aggregate requirement
for the selected new nonnegative contrast series: it asks only that its
prefixes be unbounded. Its truth is not proved.

For the ORIGINAL G_j criterion, the outstanding requirement remains

sup_J sum_(17<=j<J) 2^j*G_j^2/(j+3)^2=infinity.

A concrete stronger arithmetic inequality that would suffice is
|G_j|>=epsilon*sqrt((j+3)/2^j), with fixed epsilon>0, on an index set E having
sum_(j in E) 1/(j+3)=infinity. This permits exponentially small gaps and does
not require a fixed nonzero separation. The same threshold applies to the new
pooled gap once the ordinary harmonic source-rate assembly is used.
Neither inequality is asserted or added as an axiom.

## Primary-source investigation and applicability

The investigation used GitHub source and commit reads, Lean declaration
search, primary-paper searches through both web engines, and Wolfram symbolic
regression/determinant checks. A separate Deep Research callable tool was not
available in this session. Wolfram returned zero for the tested algebraic
remainders; the Lean kernel is the proof evidence.

1. Werner Ehm, [On certain Gram matrices and their associated series,
arXiv:2405.06349v2](https://arxiv.org/html/2405.06349v2), Theorem 2.1,
Proposition 8.2 and Section 8.1: inspected the raw Gram representation,
signed Mobius convolution and exact quadratic-form decomposition. Section
8.1 explicitly leaves the inversion error aside and explains why vanishing
centered moments alone do not control their products with growing moments.
These formulas do not bound the moving full-dictionary inverse screening
in the new charge certificate. No unproved screening transfer is imported.

2. Sandro Bettin and Sary Drappeau, [On quantum modular forms of non-zero
weights, arXiv:2210.07854](https://arxiv.org/pdf/2210.07854), Corollary 1.14
and Section 4.3; published in Compositio Mathematica 161 (2025), available
online in January 2026. The primary text proves limiting distributions and
diffuseness for appropriately normalized generalized cotangent sums over
coprime residue classes. Those raw distribution results do not by themselves
give lower bounds for adaptively screened inverse-Gram pooled contrasts.
Applying them would require a quantitative transfer controlling the actual
screening; that transfer remains Open.

3. Baez-Duarte, Balazard, Landreau and Saias,
[Sur l'autocorrelation multiplicative de la fonction partie fractionnaire,
arXiv:math/0306251](https://arxiv.org/pdf/math/0306251), Propositions 89--92:
inspected exact cotangent/autocorrelation and local rational-point identities.
They are legitimate raw-kernel sources; no reverse lower singular-value
estimate for the moving screened rows follows automatically.

The repository's additive/multiplicative large-sieve modules were also
inspected. Their energy estimates are upper bounds with explicit spacing
conditions. They cannot be reversed into the signed lower budget above.

## Verification scope

A coherent full proof candidate returned Lean exit code 0. Its ten key
axiom inspections, including the exact full-tail weight comparison, tree,
capacity, Bessel transfer, screened-charge identity and conditional RH
endpoint, reported only propext, Classical.choice and Quot.sound.
The successful candidate job was job_K8_v4HVIn35ik6tWDj-lpyUFmriXBden,
with code SHA-256
d1443de583191848c5bea2fc7c6278322966e69fcf7ecfbb24e422f4ada168a2.

The project source is split into ParetoFirstSiteAdjacentRegression.lean and
ParetoFirstSiteAdjacentContrasts.lean, with root exports and catalog entries.
Final changed-module and reverse-dependent validation, source auditing and
publication are performed by the single publication checkpoint; its actual
terminal result must be assessed separately from these isolated checks.
No historical or queued build is relabeled as a successful full rebuild.
