# Green–Pareto–Schur: GitHub continuation and four stronger results

6 October 2026. Repository: https://github.com/Cnoack3/RiemannResearch
Inspected starting commit: 8d8fd58a88ac8676b74c227aa70b113ac419ad31.

## Outcome and scope

The latest suggested GitHub task was recovered from the continuation and the
four-improvement archive, then executed against the actual Lean repository.
The results strengthen all four directions. They do not establish RH.

| Direction | New result | Status |
|---|---|---|
| Cumulative signed gaps | Negative prefixes allowed, with an exact residual-variation penalty; actual RH consumer assembled | Lean checked; arithmetic budget and normalized smallness Open |
| Canonical affine trials | Fixed-head approximation iff actual closure; arbitrary positive error budgets; cofinal bounded exact heads iff closure; canonical complete-error ceiling 4N+1/(N+1) | Lean checked; historical upper-witness target closed |
| Full conductor spectrum | Actual head restriction inverted; full-tail spectrum constructed; actual projection, correction squares and mass identified | Finite geometry Lean checked; asymptotic specialization still to be formalized |
| Retained Mellin signature | Full complex signature and head square retained; positive weighted signature growth only on unbounded indices suffices | Lean checked conditional RH consumer; signature/growth providers Open |

The explicit Möbius head-repair estimate and sharper optimized-error comparison
in Section 3 are paper proofs, not new Lean declarations. The normalized
double-log lower obstruction in Section 4 is also a paper proof.

## 1. Audit corrections before adding results

The earlier report understated existing results at the starting commit.
Reciprocal-charge nonvanishing, complete canonical affine exhaustion, conductor
triangularity, continuous exact-head repair, and the all-legal full-tail norm
minimum were already formalized.

Relevant existing files are RH/MobiusReciprocalNonvanishing.lean,
RH/CanonicalMobiusTriangular.lean, RH/CanonicalMobiusWindowMinimum.lean and
RH/CanonicalMobiusHeadRepair.lean. The existing norm minimum is distinct from
the constrained approximation-error minimum: minimizing ||f||² cannot replace
minimizing ||1-f||², which includes the complete signed mean term.

The old isolated verification process was recovered as interrupted with no
live worker. All verification submissions for this continuation were serialized.
An accepted job was never counted as a successful proof check.

## 2. Arbitrary negative cumulative prefixes

Let V_n denote the actual finite legal stages and v the actual compact
two–three dual target. In the theorem's indexing,

\[
D_i=\|v-P_{V_{i+2}}v\|^2,\qquad D_i\downarrow\delta\ge0.
\]

For any legal trial u_i in V_{i+2}, the existing exact normal equation at
physical cutoff i+3 gives

\[
D_i=H_i+L_i,
\]

where H_i is the complete signed head pairing and L_i the full infinite
optimizer/trial tail pairing. No unequal conductor interaction is omitted.

Define

\[
A_M=\sum_{i<M}a_i,\quad
\Delta D_i=D_i-D_{i+1},\quad
P_M=\sum_{i<M}\max(-A_{i+1},0)\Delta D_i.
\]

Finite Abel summation retains the terminal boundary:

\[
\sum_{i<M}a_iD_i
=A_MD_M+\sum_{i<M}A_{i+1}\Delta D_i.
\]

The exact repaired identity is

\[
\sum_{i<M}a_iD_i+P_M
=A_MD_M+\sum_{i<M}\max(A_{i+1},0)\Delta D_i.
\]

The second displayed repaired equality follows algebraically from the checked
Abel identity and the negative-part definition; the checked consumer uses its
lower-bound consequence. Thus, if the complete signed budget satisfies

\[
\sum_{i<M}\bigl[L_i-(1-a_i)D_i\bigr]\le Z_M,
\]

then

\[
A_MD_M\le\sum_{i<M}H_i+Z_M+P_M.
\]

It is enough to supply endpoints M_k tending to infinity, eventually positive
A_{M_k}, the budget at those endpoints, and

\[
\frac{\sum_{i<M_k}H_i+Z_{M_k}+P_{M_k}}{A_{M_k}}\longrightarrow0.
\]

The actual Lean theorem discharges residual monotonicity, limiting defect
nonnegativity, projection convergence and the compact-target-to-RH implication
internally. Neither individual gaps nor intermediate prefixes must be positive.
No separate head-convergence or nonnegative Z premise is imposed.

If all intermediate prefixes satisfy A_j≥-C, C≥0, then the checked finite
estimate gives

\[
P_M\le C(D_0-D_M),\qquad
(A_M+C)D_M\le\sum_{i<M}H_i+Z_M+CD_0.
\]

The penalty measures negative cumulative mass at actual residual-energy drops;
it is not a physical-tail norm.

A strict abstract comparison example has A_0=0, A_{2m}=-m,
A_{2m+1}=(m+1)^2 and D_i=1/(i+1), with H_i=a_iD_i and
L_i=(1-a_i)D_i. At M=2r+1 the repaired numerator is

\[
1+\tfrac34r+\tfrac14\sum_{m=1}^r(2m+1)^{-1},
\]

while A_M=(r+1)^2. The normalized numerator tends to zero despite unbounded
negative prefixes. This example is a paper diagnostic, not an arithmetic
provider for the actual Pareto family.

New modules: Analysis/CumulativeSignedGap.lean and
RH/ParetoCumulativeSignedGap.lean.
Actual consumer: riemannHypothesis_of_cofinal_cumulative_signed_trial_variation.
Open: construct actual trials, cumulative signed budgets and normalized
smallness meeting these hypotheses.

## 3. Exact heads: closure, a closed historical target and a quantitative repair

### Checked closure statements

For a fixed head N and target z, arbitrarily accurate finite legal vectors
matching z at every physical site 1 through N exist if and only if z belongs
to the actual closed legal span. This equivalence does not add an RH-to-density
converse.

Once z is in that closed span, every prescribed positive complete-error budget
can be met along exact growing heads with unrestricted finite supports.

For z=1, even a common complete-error bound at arbitrarily large exact heads
is equivalent to closure membership, by the existing cofinal residual theorem.
The support schedule is unrestricted. This is a closure characterization,
not an unconditional quantitative arithmetic estimate.

New statements include fixedHeadApproximation_iff_mem_closedSpace,
exists_legal_exact_head_arbitrary_error_budget and
finiteCofinalBoundedExactHeads_iff_one_mem_closedSpace.
The generic exact-repair estimate is also checked:

\[
\|y+R(b-Ly)-z\|\le(1+\|R\|\|L\|)\|y-z\|,\qquad Lz=b.
\]

### Checked unconditional canonical ceiling

For an exact head f(j)=1, 1≤j≤N, and a complete pointwise bound |f(j)|≤C,

\[
\|1-f\|^2
=\sum_{j>N}\frac{(1-f(j))^2}{j(j+1)}
\le\frac{(C+1)^2}{N+1}.
\]

The canonical competitor is

\[
U_N=-\sum_{2\le d\le N}\mu(d)g_d
+(N+1)m(N)g_{N+1},\qquad
m(N)=\sum_{d\le N}\frac{\mu(d)}d.
\]

Its existing bound |U_N(j)|≤2N therefore gives

\[
\boxed{\|1-U_N\|^2\le
\frac{(2N+1)^2}{N+1}=4N+\frac1{N+1}.}
\]

N=0 is handled by the zero legal vector. This supplies
linearExactHeadUpperWitness and closes LinearExactHeadUpperWitnessTarget in
RH/ResidualEnergyHistoricalTargets.lean. It improves the former 8N+2 ceiling.
No optimality of the constant, subpower bound or RH consequence is claimed.

### New paper estimate: explicit Möbius interpolation with O(H) cost

For H≥1 prescribe y_1,...,y_H, set y_0=0 and Δy_k=y_k-y_{k-1}. Define

\[
c_d=-\sum_{k\mid d}\mu(d/k)\Delta y_k\quad(2\le d\le H),
\]
\[
s_H=\sum_{k=1}^H\frac{\Delta y_k}{k}m(\lfloor H/k\rfloor),
\qquad c_{H+1}=(H+1)s_H,\qquad
T_Hy=\sum_{d=2}^{H+1}c_dg_d.
\]

Divisor regrouping yields the exact boundary equality

\[
s_H=y_1-\sum_{d=2}^H c_d/d,\qquad
\sum_{d=2}^{H+1}c_d/d=y_1.
\]

Using g_d(j)=j/d-floor(j/d) and finite Möbius inversion,

\[
T_Hy(j)-T_Hy(j-1)
=y_1-\sum_{\substack{d\mid j\\d\ge2}}c_d=\Delta y_j
\quad(1\le j\le H).
\]

Hence T_Hy matches every prescribed head value. The boundary conductor H+1
and every composite conductor are retained.

Write e²=Σ_{k=1}^H|y_k|²/[k(k+1)]. The complete norm satisfies ||g_d||²≤2/d.
With B=Σ_{k=1}^H|Δy_k|/k, Cauchy gives B≤2sqrt(2H)e. The interior sum is bounded
by 2sqrt(2H)B≤8He. Using the existing unconditional |m(n)|≤1, the boundary
term is at most sqrt(2(H+1))B≤4sqrt(H(H+1))e. Thus

\[
\boxed{\|T_Hy\|\le C_He,\qquad
C_H=8H+4\sqrt{H(H+1)}\le12H+4.}
\]

These inequalities bound the whole infinite tail, after proving the exact
signed interpolation and boundary equalities.

### Stronger paper comparison with unconstrained projection error

Here V_M=span(g_2,...,g_M) uses conductor-budget indexing. Set

\[
p_M=P_{V_M}1,\quad \delta_M=\|1-p_M\|^2,\quad
e_{H,M}=\|Q_H(1-p_M)\|,
\]
\[
E_{H,M}=\inf_{\substack{f\in V_M\\Q_Hf=Q_H1}}\|1-f\|^2.
\]

For H≥1 and M>H the feasible set is nonempty. Every feasible f=p_M+t has t∈V_M and
Q_Ht=Q_H(1-p_M). Orthogonality retains the exact full-error square:

\[
\|1-f\|^2=\delta_M+\|t\|^2.
\]

Head contraction gives ||t||²≥e_{H,M}². The legal choice
t=T_H(Q_H(1-p_M)) stays in V_M because its conductors are at most H+1. Therefore

\[
\boxed{\delta_M+e_{H,M}^2
\le E_{H,M}
\le\delta_M+C_H^2e_{H,M}^2
\le[1+(12H+4)^2]\delta_M.}
\]

This strengthens the earlier triangle-inequality ceiling (12H+13)²δ_M.
For any η>0, a certificate δ_M≤η/[1+(12H+4)²] gives an exact-head complete
error certificate E_{H,M}≤η. It supplies a transfer cost, not a decay rate
for δ_M or an effective support schedule M(H). Formalizing this explicit
operator and comparison is a useful next finite task.

## 4. Literal full-conductor spectrum and sharper escape

For the actual full finite stage V_n and cutoff N≥n+1, compact coefficient
duals prove that Q_N restricted to V_n is injective. Define the literal head
image E=Q_NV_n and construct its inverse lift ell:E→V_n.

Let J:E→H be inclusion and A=ell-J=(I-Q_N)ell, the complete infinite tail.
The real operator A* A is positive and symmetric. Its full orthonormal
eigenbasis is constructed, with λ_i≥0; no spectrum or injectivity premise is
supplied by the caller.

For a target v supported within this cutoff, set
w_i=|<Je_i,v>|² and e=||v-P_Ev||². The checked finite identities identify the
spectral fit with the actual stage projection, and give

\[
S=\sum_iw_i\frac{\lambda_i}{(1+\lambda_i)^2}
=\|(I-Q_N)P_{V_n}v\|^2,
\]
\[
J_{\rm disp}=\sum_iw_i\left(\frac{\lambda_i}{1+\lambda_i}\right)^2
=\|Q_NP_{V_n}v-P_Ev\|^2,
\]
\[
T=S+J_{\rm disp}
=\sum_iw_i\frac{\lambda_i}{1+\lambda_i},\qquad
\|v-P_{V_n}v\|^2=e+T,
\]
\[
\sum_iw_i=\|P_Ev\|^2=\|v\|^2-e.
\]

The two correction squares remain explicit. These are actual finite Hilbert
identities; no new literal inverse-matrix identity is claimed.

For any sequence of nonnegative spectral data with T_n→δ and S_n→0, put
B_n(R)=Σ_{λ_i≥R}w_i. The finite bound is

\[
|B_n(R)-T_n|
\le\max(1+R,(1+R)/R)\,S_n\quad(R>0).
\]

The checked strengthened scalar consumers give:

* B_n(R)→δ at every fixed R>0.
* At any fixed positive threshold, B_n(R)→0 iff δ=0.
* Eventual source tightness at infinity is equivalent to δ=0.
* If R_n≥1 and (1+R_n)S_n→0, then B_n(R_n)→δ.

Thus tightness describes the escaped defect exactly. An untruncated moment
condition can be stronger than the required tightness condition.

Paper consequence: if 0<σ_n<1, S_n≤σ_n→0, choose R_n=σ_n^{-α}, 0<α<1.
Then B_n(R_n)→δ. For Φ(x)=log(1+log(1+x)), nonnegative weighted Markov gives

\[
\liminf_n
\frac{\sum_iw_i\Phi(\lambda_i)}
{\log(1+\log(1/\sigma_n))}\ge\delta.
\]

The threshold ratio Φ(σ_n^{-α})/log(1+log(1/σ_n)) tends to one. This paper
argument improves a merely sufficient vanishing-moment condition into a
quantitative obstruction under positive defect.

Formal limitation: the finite actual construction and scalar sequence consumer
are checked separately. A complete actual sequence-to-RH tightness theorem is
not yet assembled. For the compact dual target, remaining unconditional geometric formalization
steps are Q_Nf→f, actual optimizer-tail decay S_n→0, and head-projection error e_n→0.
The last can use the compact corrected trial, a sharper conductor-membership
bound, and the explicit reciprocal charge
14m(N)-13m(floor(N/2))+3m(floor(N/4))→0 by the existing PNT machinery.
Then the exact identity gives T_n→δ.

These are formalization tasks, distinct from the mathematically open arithmetic
tightness or source-moment estimate for this literal full family. The repository's
RH-to-density converse hypothesis also remains explicit.

New modules: Analysis/FiniteHeadTailSpectralRealization.lean,
RH/ParetoActualHeadSpectrum.lean and Analysis/FiniteSpectralEscape.lean.

## 5. Retain the entire complex Mellin head signature

For an actual legal f, let r=1-f, h=Q_{n-1}r and
α(s)=1/s-M_s(h). At a hypothetical zero s with β=Re(s)>1/2 and s≠1,
the checked exact localization yields

\[
\boxed{(2\beta-1)|\alpha(s)|^2 n^{2\beta-1}
\le\|r\|^2-\|h\|^2.}
\]

It retains the complete complex phase and the full head square. It follows
from M_s(r)=1/s, exact Mellin linearity, the zero initial head of r-h,
tail Cauchy and head/tail Pythagoras.

The improved actual RH consumer assumes n_i→∞, legal f_i, C_i≥0,

\[
\|1-f_i\|^2\le1+C_i,\qquad
\frac{\log(1+C_i)}{\log n_i}\to0,
\]

and at each hypothetical zero 1/2<β<1 some c,ε>0 such that on unbounded
indices

\[
c n_i^\varepsilon
\le|\alpha_i(s)|^2 n_i^{2\beta-1}.
\]

This forces a positive-power lower floor only on unbounded indices, which
already contradicts subpolynomial complete-error growth. The signature may
decay almost at the critical rate. A fixed positive signature lower bound
only on unbounded indices is a checked special case. No head-norm limit is
required.

New module: RH/LocalizedMellinHeadSignature.lean.
Consumers: riemannHypothesis_of_legal_subpolynomial_cofinal_weighted_signature
and riemannHypothesis_of_legal_subpolynomial_cofinal_head_signature.
Open: actual complete-energy and signature noncancellation providers.
The hypothesis depends on each hypothetical zero; it is not established by
algebraic retention of the signature alone.

## 6. Verification and publication protocol

Successful isolated checks were recorded for the Mellin obstruction and
consumers, cumulative signed criterion, closure/repair results, canonical
ceiling and historical witness, source escape, and actual finite spectrum.

Representative successful jobs:
* job_35IMTWo2bZM_lhCJ43hJTHIWgYKbCh5N: coherent core check, exit 0.
* job_fu1ygwFFmGmYnjpGDxKLPzH0RBeB9-Qt: generic and actual spectrum, exit 0.
* job_kcjG6WIr7qSuc6B48pS3HOHOD_0pvLqy: improved Mellin, exit 0.
* job_yFaH1S9TW2q4zOfOv_AZQeBw4I62I2kL: narrowed imports, canonical ceiling
  and final actual source-mass identity, exit 0; standard axiom audit.

Decisive theorem axiom audits reported only propext, Classical.choice and
Quot.sound. No added proof holes or extra mathematical axioms were used.
Routine parser and elaboration errors were repaired before successful checks.
Finite Wolfram algebra/interpolation tests are diagnostics, not proof authority.

Publication uses one final push-enabled checkpoint, which audits and validates
affected modules and their reverse dependents before committing and pushing.
Its terminal result is recorded in the delivered report. This continuation does
not claim a separate full-project build.

## 7. Primary-source search: what it supports and what it does not supply

The web search checked relevant primary literature against the missing providers:

* Báez-Duarte, A strengthening of the Nyman–Beurling criterion:
  https://arxiv.org/abs/math/0202141 .
  Classical closure equivalence context; it does not supply a new quantitative
  estimate for this chosen trial or support schedule.
* Báez-Duarte, A strengthening of the Nyman–Beurling criterion for the
  Riemann hypothesis, 2:
  https://arxiv.org/abs/math/0205003 .
  The quantitative damped approximation theorem assumes RH.
* Burnol, A lower bound in an approximation problem involving the zeros of
  the Riemann zeta function:
  https://arxiv.org/abs/math/0103058 .
  Lower-bound context; not the missing upper provider.
* Bettin–Conrey–Farmer, An optimal choice of Dirichlet polynomials for the
  Nyman–Beurling criterion:
  https://arxiv.org/abs/1211.5191 .
  Its approximation asymptotic uses RH and a reciprocal zeta-derivative moment
  hypothesis; it cannot be imported as an unconditional resolution.
* Alouges–Darses–Hillion:
  https://arxiv.org/abs/2006.02953 .
  Distinguishes approximation from the additional coefficient-control problem.
* Carvill:
  https://arxiv.org/abs/2510.18132 .
  Mellin-smoothed ladder Gram estimates concern the smoothed dyadic setting;
  they were not taken as an unsmoothed full-conductor inverse/source bound.
* Maier–Rassias:
  https://arxiv.org/html/1806.05070v1 .
  Möbius-weighted cotangent-sum estimates are relevant arithmetic context,
  but not an identified provider for this complete mixed Pareto error.

No searched result was found to discharge the actual signed budget,
unrestricted-family spectral tightness, or optimized subpower error estimate.

## 8. Improved GitHub prompt for the next continuation

The useful next prompt should begin with the actual audited state, retain
literal complete errors, and name one provider or formal gap at a time:

    Continue Cnoack3/RiemannResearch from its current published commit.
    Read AGENTS.md and RH/GreenParetoGitHubAdvance20261006.md first.
    Use bounded searches of the relevant THEOREM_CATALOG.md entries.
    Inspect actual declarations;
    do not repeat the stale claim that affine exhaustion is unproved.

    First close the remaining finite/geometric integration:
    (1) Formalize the explicit Möbius head interpolation T_H, its boundary
        equality and C_H=8H+4sqrt(H(H+1)) complete norm bound.
    (2) Use the exact residual orthogonality identity to prove
        delta_M+e_HM^2 <= E_HM <= delta_M+C_H^2 e_HM^2 for M>H.
    (3) Formalize Q_N f -> f; sharpen the compact corrected trial's conductor
        membership; prove its reciprocal charge tends to zero using the
        existing PNT provider. Assemble e_N -> 0, S_N -> 0, T_N -> delta
        for the literal full-conductor spectrum.
    (4) Specialize the checked scalar tightness consumer to that actual
        sequence and the existing compact-target-to-RH implication.
        Keep the RH-to-density converse gap explicit.

    Then attempt one concrete arithmetic provider with a stated support
    schedule. Either:
    * estimate the full optimized exact-head error, including every signed
      mixed Gram entry, sufficiently to obtain cofinal bounded errors; or
    * prove a complete cumulative signed budget and normalized
      head+budget+negative-prefix-variation smallness; or
    * prove tightness for the literal spectral source constructed in
      ParetoActualHeadSpectrum, or a rigorously sufficient moment estimate.

    Use primary-source web search; state assumptions of cited theorems.
    Smoothed or conditional estimates must not be substituted for the actual
    unsmoothed unconditional provider. Retain terminal boundaries, complex
    Mellin phase, all conductors and complete infinite-tail norm squares.

    Root alone submits serialized Lean jobs. Record terminal success and
    axiom audits before calling results checked. Keep focused imports and
    publication architecture. Perform one final push-enabled checkpoint.
    Update the theorem catalog and an exact continuation report. If a
    provider remains open, state the precise unresolved inequality instead
    of claiming RH or stopping at a numerical experiment.
