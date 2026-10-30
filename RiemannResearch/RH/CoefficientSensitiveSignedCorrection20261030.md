# Coefficient-sensitive signed covariance and rational Landau remainders

30 October 2026. Source snapshot: Cnoack3/RiemannResearch, workspace base
457c5f379c82218b2a2b5797b89b5b2d2bc24fb4. This continues the finite results
of commit 7ef8da56e63a27a6f52c335d9b1cb0c38022b241.

## Conclusion and status

There are three useful developments.

1. The actual right-line remainder admits a coefficient-weighted bound retaining
   the exact integer mismatch and the necessary factor (n/(mq))^2.
   Summing the mismatches improves its uniform entrywise envelope from
   O(X^(5/2)) to O(X^(3/2)+X log^2(2X)).
2. For feasible changes of an exact-head coefficient vector, the relevant mixed
   term is controlled by Ba-A*lambda, not necessarily by the entire action Ba.
   A sparse row-energy remainder supplements the existing perturbation theorem.
3. Explicit damped Mobius families have bounded signed covariance for exponent
   sigma>1/2, but their full action norm diverges on growing squarefree support.
   Neither their bounds nor the finite constraint reduction control the actual
   full-squarefree optimizer.

The complete analytic assembly and growth deductions below are paper proofs.
The finite Lean development and publication status are recorded at the end.
No RH proof, optimizer coefficient estimate, or unconditional discharge of the
repository's explicit Selberg-density hypothesis is asserted.

## 1. Which coefficients are actually in the source?

The coefficient families must not be conflated.

| Source | Coefficients and role |
|---|---|
| Analysis/ActualDirichletPolynomialGram.lean | Arbitrary finite complex a_n in P_a(t)=sum a_n n^(it), sampled at actual zeta ordinates with multiplicity. It does not select an optimizer. |
| Analysis/ActualMobiusZeroDetector.lean | The actual finite mollifier M_X(s)=sum_{1<=n<=X} mu(n) exp(-s log n). On a fixed vertical line this has magnitudes |mu(n)|n^(-sigma). |
| Analysis/SquarefreeSignedCovariance.lean | The full squarefree family mu(n)f(n), including composite vertices and every active edge. |
| Analysis/PrimeTowerMovingBudget.lean | Reciprocal and inverse-square profiles on pure prime towers, with exact frequency-spread formulas. These supports contain non-squarefree prime powers. |
| RH/QCRTOptimizerGrowth.lean and its imports | The actual legal exact-head minimum-energy element in L^2(Q), with a conditional subpolynomial-energy consumer implying RH. Its atom Gram matrix G is different from the arithmetic covariance B. |

For the mollifier, P_a(-t)=M_X(sigma+it) when a_n=mu(n)n^(-sigma).
Since these a_n are real, |P_a(-t)|=|P_a(t)|. A vertical translation gives the
complex profile a_n=mu(n)n^(-sigma+i tau), with the exact convention
P_a(-t)=M_X(sigma+i(t-tau)).

The independently used cutoff growingMollifierCutoff(T)=ceil(T)+37 in
ActualMollifierRightBoundary.lean is designed for a right-boundary logarithmic
estimate. It is not within the sub-quarter-log frequency band used below.
A phase-sampling result for X=T^c, c<1/4, cannot silently be applied to that cutoff.

## 2. Exact signed covariance on squarefree support

Let S be a finite set of positive squarefree integers. Put

\[
 w_p=\frac{\log p}{\sqrt p},\qquad
 {\cal E}_S=\{(m,p):p\text{ prime},\ m,pm\in S\}.
\]

The source's Hermitian matrix has B_(m,pm)=-w_p/(2 pi), its transpose has the
same entry, and all other entries are zero. Therefore the complete equality is

\[
 Q_S(a)=\operatorname{Re}(a^*B_Sa)
 =-\frac1\pi\sum_{(m,p)\in{\cal E}_S}
       w_p\operatorname{Re}(\overline{a_m}a_{pm}).                 \tag{2.1}
\]

Each unordered edge occurs once. Every composite squarefree vertex is retained.

Its actual action is

\[
 (B_Sa)_n=-\frac1{2\pi}\left[
 \sum_{\substack{p\mid n,\ p\ {\rm prime}\\n/p\in S}}w_pa_{n/p}
 +\sum_{\substack{p\ {\rm prime}\\np\in S}}w_pa_{np}\right].       \tag{2.2}
\]

These formulas describe precisely where coefficient cancellation must occur.
The already checked Mobius anticommutation and perturbation theorems are reused.

### A finite edge-defect inequality

Fix positive numbers r_p. Define
\[
 e_{m,p}=a_{pm}+r_pa_m,\quad
 H=\sum_{{\cal E}_S}w_pr_p|a_m|^2,\quad
 J=\sum_{{\cal E}_S}\frac{w_p}{r_p}|e_{m,p}|^2.
\]
The exact equality and Cauchy--Schwarz give
\[
 \boxed{\pi Q_S(a)=H-
 \operatorname{Re}\sum_{{\cal E}_S}w_p\overline{a_m}e_{m,p}},
 \qquad
 \boxed{|\pi Q_S(a)-H|\le\sqrt{HJ}}.                            \tag{2.3}
\]

Proof: substitute a_(pm)=-r_pa_m+e_(m,p) into (2.1), then apply Cauchy--Schwarz
to sqrt(w_pr_p)a_m and sqrt(w_p/r_p)e_(m,p).
Thus H>0 and J<H imply Q_S(a)>0. In particular, a nonpositive correction
requires J>=H. Small multiplicative defects around a Mobius profile do not
produce a favorable nonpositive sign.

For a_n=mu(n)n^(-sigma), take r_p=p^(-sigma). Then e_(m,p)=0 exactly, so
all prime-ratio terms have the same sign:
\[
 Q_S(a)=\frac1\pi\sum_{{\cal E}_S}
       \frac{\log p}{p^{\sigma+1/2}m^{2\sigma}}\ge0.             \tag{2.4}
\]
This is strict when the support contains an edge.

For the shifted complex profile mu(n)n^(-sigma+i tau), the exact formula is
\[
 Q_S(a)=\frac1\pi\sum_p\frac{\log p\cos(\tau\log p)}
                                    {p^{\sigma+1/2}}
       \sum_{\substack{m,pm\in S}}m^{-2\sigma}.                 \tag{2.5}
\]
Cancellation across primes is now an actual cosine-weighted arithmetic sum,
not a consequence of Mobius signs alone.

## 3. The exact nonresonant expansion

For 1<=m<n, write x=n/m>1 and u=log x. The repository uses
\[
 K_{A,B}(v)=\int_A^B e^{itv}\,dt,\qquad
 K_{A,B}(0)=B-A,\qquad
 K_{A,B}(v)=\frac{e^{iBv}-e^{iAv}}{iv}\quad(v\ne0).
\]
Hence
\[
 |K_{A,B}(v)|\le\min\{|B-A|,2/|v|\}.
\]

On Re(s)=2, the exact right-line nonresonant term is
\[
 R_{nm}(A,B)=
 -\frac{x^{3/2}}{2\pi}
 \sum_{\substack{q\ge1\\n\ne mq}}\frac{\Lambda(q)}{q^2}
               K_{A,B}\!\left(\log\frac n{mq}\right).          \tag{3.1}
\]
This is the existing rightLandauLine_rational_eq_main_nonresonance identity,
after removing the exact resonance. The q sum includes every prime power.
Squarefree endpoints force PRIME exact ratios, but do not remove nonresonant
prime powers from (3.1).

Absolute convergence of (3.1) is already supplied by the source's
summable_rationalMangoldtNonresonantTerm. Let
\[
 S_2=\sum_{q\ge1}\frac{\Lambda(q)}{q^2}<\infty.
\]

### The denominator-preserving bound

For q<=2x and n!=mq, the checked logarithmic theorem gives
\[
 \frac1{\sqrt x\,|\log(x/q)|}\le\frac{2\sqrt{mn}}{|n-mq|}.
\]
Multiplying by the ACTUAL right-line weight gives
\[
 \frac{x^{3/2}}{2\pi}\frac{\Lambda(q)}{q^2}
 |K_{A,B}(\log(x/q))|
 \le\frac{2\sqrt{mn}}{\pi}
       \frac{\Lambda(q)(x/q)^2}{|n-mq|}.                       \tag{3.2}
\]
The factor (x/q)^2 is essential and cannot be dropped for small q.

For q>2x, |log(x/q)|>=log 2. Consequently
\[
 \boxed{
 |R_{nm}|\le
 \frac{2\sqrt{mn}}{\pi}
 \sum_{\substack{1\le q\le2x\\n\ne mq}}
      \frac{\Lambda(q)(x/q)^2}{|n-mq|}
 +\frac{x^{3/2}}{\pi\log2}\sum_{q>2x}\frac{\Lambda(q)}{q^2}.
 }                                                            \tag{3.3}
\]

For any finite coefficient support S, the paired right-line error is
\[
 {\cal R}_{\rm right}(a)=
 2\operatorname{Re}\sum_{\substack{m,n\in S\\m<n}}
                \overline{a_m}a_nR_{nm}.                      \tag{3.4}
\]
Multiply the right side of (3.3) by 2|a_ma_n| and sum over m<n.
This is an explicit finite-support, coefficient-sensitive inequality.
It retains the entire q tail, every actual coefficient, and every mismatch.

### A useful harmonic summation

Let g=gcd(m,n), K=floor(2x), and H_K=sum_(j=1)^K 1/j. Then
\[
 \sum_{\substack{1\le q\le2x\\n\ne mq}}\frac1{|n-mq|}
 \le \frac2g+\frac{2H_K}{m}.                                 \tag{3.5}
\]
On each side of x, the first nonzero mismatch is at least g.
Subsequent mismatches increase by m. Each side contributes at most
1/g+H_K/m. This proof also covers integral x, where the zero mismatch is
excluded.

Split (3.1) into x/2<=q<=2x and its complement. In the middle interval,
(x/q)^2<=4 and Lambda(q)<=log q<=log(2x). Outside it, the inverse logarithm
is at most 1/log 2. Therefore
\[
 \boxed{
 |R_{nm}|\le
 \frac{S_2 x^{3/2}}{\pi\log2}
 +\frac{8\sqrt{mn}}{\pi}\log(2x)
             \left(\frac2g+\frac{2H_K}{m}\right).
 }                                                            \tag{3.6}
\]
The far sum was bounded by S_2 only at this last step; (3.3) retains more
coefficient-specific arithmetic information; no universal numerical ordering
between (3.3) and (3.6) is asserted.

For 1<=m<n<=X this is O(X^(3/2)+X log^2(2X)), uniformly in both endpoints.
Only the right-line component has been improved at this stage.

## 4. Where signed mismatch cancellation could improve the bound

Define the logarithmic mean
\[
 L(n,mq)=\frac{n-mq}{\log(n/(mq))}>0 \quad(n\ne mq).
\]
Before taking absolute values, (3.1) is exactly
\[
 R_{nm}=-\frac1{2\pi i}
 \sum_{q:n\ne mq}
 \frac{x^{3/2}\Lambda(q)L(n,mq)}{q^2(n-mq)}
 \left[e^{iB\log(n/(mq))}-e^{iA\log(n/(mq))}\right].             \tag{4.1}
\]

For each nonzero integer k, let
\[
 F_k=\!\!\sum_{\substack{m,n\in S,\ m<n,\ q\ge1\\n-mq=k}}
 \overline{a_m}a_n\frac{(n/m)^{3/2}\Lambda(q)L(n,mq)}{q^2}
 \left[e^{iB\log(n/(mq))}-e^{iA\log(n/(mq))}\right].
\]
Each F_k is a finite sum. Absolute convergence of (3.1) justifies regrouping:
\[
 {\cal R}_{\rm right}
 =-\frac1\pi\operatorname{Re}\left[
     \frac1i\sum_{k\ge1}\frac{F_k-F_{-k}}{k}\right],\qquad
 |{\cal R}_{\rm right}|
 \le\frac1\pi\sum_{k\ge1}\frac{|F_k-F_{-k}|}{k}.                \tag{4.2}
\]
This retains all unmatched boundary contributions. In particular, F_k=0 for
sufficiently large positive k, while negative mismatches still contain the
infinite q tail.

A useful cancellation provider would prove that the last sum is o(T) for
the actual moving coefficient family. Neither (3.2) nor the Mobius symmetry
proves that provider. An absolute denominator bound cannot be treated as a
signed Hilbert-transform estimate without controlling its actual numerator,
cutoffs, endpoint phases, and boundary terms.

## 5. Complete contour and phase budgets

For good contour endpoints A and B chosen as in ActualUniformRationalLandau,
the exact source identity is
\[
 \operatorname{Lan}_T(u)+T\,\operatorname{Main}(n,m)
 =\operatorname{Lan}_A(u)+H_{A,B}(u)-L_{A,B}(u)+R_{nm}
  -(\operatorname{Lan}_B(u)-\operatorname{Lan}_T(u))
  +(A+T-B)\operatorname{Main}(n,m).                            \tag{5.1}
\]
Here H is bottom minus top, L is the upward left side, and
Main(n,m)=Lambda(n/m)/(2 pi sqrt(n/m)) when m divides n, zero otherwise.
Every endpoint and contour side remains present.

Inspection of the separate component bounds in the existing proof gives,
for some absolute C and ell=log(T+3), T>=9, a bound for the terms in (5.1)
OTHER than R_nm of the form
\[
 C\left[x^{3/2}\ell^2+(1+1/\log x)\ell\right].                \tag{5.2}
\]
For example the initial fixed-height, horizontal, and short-height terms
are bounded by multiples of x^(3/2)ell^2; the left side by
(1+1/log x)ell; and the endpoint main term by a multiple of x^(3/2).
This deduction uses the existing component estimates, not a subtraction
from the old absolute-value bound.

Define
\[
 {\cal M}(a)=\sum_{m<n}|a_ma_n|(n/m)^{3/2},\qquad
 {\cal J}(a)=\sum_{m<n}|a_ma_n|(1+1/\log(n/m)),
\]
and let E_right(a) be the sum of 2|a_ma_n| times either (3.3) or (3.6).
Then the complete paired Landau error obeys the paper-level bound
\[
 |{\cal R}_{\rm Landau}(a)|\le
 E_{\rm right}(a)+2C[\ell^2{\cal M}(a)+\ell{\cal J}(a)].        \tag{5.3}
\]
The negative-frequency terms are paired using the actual zeta reflection
identity landauSum_neg. The diagonal is exactly N(T)sum |a_n|^2.

Now retain the repository's explicit density hypothesis with exponent
delta>0 and band |log(n/m)|<=theta delta log T, 0<=theta<1.
With
\[
 V(a)=\sum_{n,m}|a_n||a_m|(\log n-\log m)^2
\]
the already checked density-band consumer gives
\[
 \left|\frac{D_T(a)-N(T)\|a\|_2^2}{T}-Q_S(a)\right|
 \le
 \frac{E_{\rm right}(a)+2C[\ell^2{\cal M}(a)+\ell{\cal J}(a)]}{T}
 +\frac{2C_D}{\delta^2(1-\theta^2)}\frac{V(a)}{\log T}.         \tag{5.4}
\]
This assembly is a paper consequence; it has not been newly checked in Lean.
The density premise is deliberately deferred in ActualZeroSelbergDensity.lean.

For a moving family, a sufficient explicit budget is
\[
 E_{\rm right}(a_T)=o(T),\quad
 \ell^2{\cal M}(a_T)+\ell{\cal J}(a_T)=o(T),\quad
 V(a_T)=o(\log T),
\]
with eventual band membership and one fixed C_D>=0 supplying the displayed
density input for all sufficiently large T.
There is no fixed-support-to-moving-support inference here.

## 6. Does the estimate survive growing support?

### Damped squarefree profiles

If |a_n|<=C_0 n^(-sigma), sigma>1/2, then (2.1) gives the support-uniform bound
\[
 |Q_S(a)|\le
 \frac{C_0^2\zeta(2\sigma)}{\pi}
       \sum_p\frac{\log p}{p^{\sigma+1/2}}<\infty.             \tag{6.1}
\]
The last prime sum converges by comparison with the integer log-weighted
p-series. No cancellation or RH is used.

For sigma>1, the absolute coefficient mass and its log-squared moment
are uniformly bounded, hence V(a)=O_sigma(1). For sigma>1/2, (3.6), keeping
its logarithms inside the sums, yields
\[
 E_{\rm right}(a)=
 \begin{cases}
 O_{\sigma,C_0}(X^{5/2-\sigma}),&1/2<\sigma<5/2,\\
 O_{C_0}(\log(2X)),&\sigma=5/2,\\
 O_{\sigma,C_0}(1),&\sigma>5/2.
 \end{cases}                                                \tag{6.2}
\]
Here S is any squarefree subset of [1,X].

Details: the far term is bounded by a constant times
(sum n^(3/2-sigma))(sum m^(-3/2-sigma)).
In the middle term use g>=1 and H_floor(2x)<=1+log(2x).
For sigma>3/2 the resulting logarithm-weighted half-moments converge.
For 1/2<sigma<3/2 its largest power is X^(3-2sigma), with logarithmic
factors; this is strictly smaller than X^(5/2-sigma).
At sigma=3/2 the middle contribution is polylogarithmic.
These comparisons prove (6.2), including its endpoint cases.

For sigma>1, J(a) is uniformly bounded: when n>=2m, 1/log(n/m)<=1/log2;
when m<n<2m, use 1/log(n/m)<=n/(n-m) and sum the resulting
m^(1-2sigma)H_m. Thus (5.4) is effective, for example, for
\[
 a_n=\mu(n)n^{-3/2},\quad S=\{n\le X:n\ {\rm squarefree}\},\quad X=T^c,
 \qquad 0<c<1/4.
\]
Choose theta with 4c<theta<1 and delta=1/4. Then E_right=O(X),
M=O(X), J=O(1), V=O(1), so
\[
 \text{normalized error}
 =O(T^{c-1}\log^2T)+O(1/\log T)\longrightarrow0.              \tag{6.3}
\]
This is conditional on the repository's stated density provider, and is an
example of actual mollifier coefficients, not an optimized legal approximation.

The critical-line profile sigma=1/2 does not satisfy the uniform covariance
bound (6.1). Its positive edge sum already diverges on the edges 1--p.
A sufficient phase-spread bound is V=O(X), so X=o(log T) makes the
phase comparison small; the complete contour budget is then also small.
For an explicit proof, A_0<=2 sqrt(X) and, since the summand is decreasing,
\[
 \sum_{n\le X}n^{-1/2}\log^2(X/n)
 \le\int_0^X t^{-1/2}\log^2(X/t)\,dt=16\sqrt X.
\]
Centering the exact spread identity at log X gives V<=64X.
The same upper bound applies to any squarefree subset.
This only approximates a possibly growing Q_S(a), and gives no RH conclusion.

### A rigorous action-norm obstruction

For a_n=mu(n)n^(-sigma), fix a squarefree m with a_m!=0 and exhaust all
squarefree integers by S_X. At every vertex pm, p prime not dividing m,
all nonzero summands in (2.2) have the same Mobius sign. Hence
\[
 |(B_{S_X}a)_{pm}|\ge\frac{\log p}{2\pi\sqrt p}|a_m|,\qquad
 \|B_{S_X}a\|_2^2\ge\frac{|a_m|^2}{4\pi^2}
       \sum_{\substack{p\le X/m\\p\nmid m}}\frac{(\log p)^2}{p}
       \longrightarrow\infty.                              \tag{6.4}
\]
The divergence follows already from Euler's divergent prime reciprocal sum.
It holds for every sigma, including sigma>5/2. If frequency 1 is excluded,
use m=2. Thus bounded Q(a) does not imply bounded full action.

Weighted overlap can nevertheless remain finite. If
|a_n|<=C_0 n^(-sigma), |h_n|<=epsilon n^(-tau), sigma,tau>1/2, and
P_s=sum_p log(p)/p^(s+1/2), then
\[
 |Q(a+h)-Q(a)|
 \le\frac{C_0\epsilon}{\pi}\zeta(\sigma+\tau)(P_\sigma+P_\tau)
      +\frac{\epsilon^2}{\pi}\zeta(2\tau)P_\tau.               \tag{6.5}
\]
Proof: use the existing perturbation identity, bound the two orientations
of each mixed edge, and apply (6.1) to h.
This is uniform in support. Such decay for the optimizer perturbation
has not been proved.

## 7. The relevant defect for an actual constrained optimizer

Let A be the complete physical-head map on a fixed coefficient support.
If Aa=b and A(a+h)=b, then Ah=0. For every multiplier lambda,
\[
 \boxed{
 Q_B(a+h)=Q_B(a)+2\operatorname{Re}
        \langle h,Ba-A^*\lambda\rangle+Q_B(h).
 }                                                          \tag{7.1}
\]
This follows directly from the already checked perturbation equality because
<h,A*lambda>=<Ah,lambda>=0.

For d_i=sum_j |B_ij|, symmetry and 2uv<=u^2+v^2 give
\[
 |Q_B(h)|\le\sum_i d_i|h_i|^2.
\]
Consequently, if |(Ba-A*lambda)_i|<=delta_i,
\[
 \boxed{
 |Q_B(a+h)-Q_B(a)|
 \le2\sum_i|h_i|\delta_i+\sum_i d_i|h_i|^2.
 }                                                          \tag{7.2}
\]
The sums retain the actual sparse prime-ratio rows. More generally, any
positive weights v_i allow d_i(v)=sum_j |B_ij|v_j/v_i in the same formula.

The smallest Euclidean action defect is
\[
 \inf_\lambda\|Ba-A^*\lambda\|_2=\|P_{\ker A}Ba\|_2.
\]
The divergence in (6.4) does not prove divergence of this projected defect.

If the complete physical-energy Gram matrix G is positive definite, define
\[
 \delta_{G,A}(a)=
 \inf_\lambda\|G^{-1/2}(Ba-A^*\lambda)\|_2.
\]
For a G-energy minimizer a on THIS support and THESE head constraints,
Ga is in range(A*), and every feasible perturbation satisfies
\[
 \|h\|_G^2=E(a+h)-E(a)=\Delta E.
\]
If additionally |h*Bh|<=kappa h*Gh on ker A, then
\[
 |Q_B(a+h)-Q_B(a)|
 \le2\delta_{G,A}(a)\sqrt{\Delta E}+\kappa\Delta E.             \tag{7.3}
\]
No uniform kappa or defect estimate is supplied. If G is singular, pass to
an injective coefficient representation or its justified quotient; do not
write an unjustified inverse.

An old-dictionary optimizer is not automatically stationary in an enlarged
dictionary. Applying (7.3) across that enlargement without checking the new
tangent space would be an error.

## 8. Exact remaining research obligations

- Coefficient provider: bound the actual optimizer's M, J, V, and the
  mismatch-weighted right-line sum at its actual maximum conductor.
  Its physical head size is not its maximum squarefree conductor.
- Constrained-action provider: find explicit multipliers lambda_H and bounds
  on B a_H-A_H*lambda_H, together with the complete perturbation quadratic
  remainder. G-stationarity alone supplies no B-action estimate.
- Signed cancellation provider: control the actual prime-edge correlations
  (2.1), or the signed mismatch differences (4.2), without discarding their
  phases, nonresonant prime powers, or unmatched boundary terms.
- RH bridge: connect such control to the actual legal closure/optimizer
  growth consumer or a test family detecting each individual off-line zero.
  A moving-support phase asymptotic by itself does not make this connection.
- Analytic premise: keep the intentionally deferred density provider visible
  in the theorem type. Finite algebra and denominator separation do not prove it.

These are distinct obligations; none has been replaced by an assumption
named as a theorem.

## 9. Lean development and source references

**No new Lean theorem was verified in this continuation.** Two serialized
development jobs ended in terminal wall timeouts:

| Job | Terminal result | Server operation time | Diagnostic output |
|---|---|---|---|
| job_qzRcDHJ3bQg4YtZCphmM2ZV9X1lMr9Yz | failed; wall_timeout; verified=false; exit -9 | 240.064 seconds | Dependency-unpacking messages only; no theorem diagnostics. |
| job_2vjnuZtTo8g9ID5ikmJwAzbbVdSeUey8 | failed; wall_timeout; verified=false; exit -9 | 240.037 seconds | Empty. |

The second check isolated the general finite quadratic results. These timeouts
do not refute any statement. They also do not certify the source drafts.
No further verification was submitted after these terminal results.
A server diagnostics request returned "Unknown tool".

Workspace-opening latency was not separately instrumented. Server queue start
delays were below 0.001 seconds; polling intervals were 30 or 60 seconds.
Operation times are not kernel-only checking times. The final combined draft
also contains later actual-Mangoldt candidates and a static norm_sum_le repair;
that combined file was not submitted and is explicitly labelled UNVERIFIED.

**Publication scope: documentation only.** No Lean source or dependency change
is installed or published. The final checkpoint may therefore skip Lean.
The proof candidates and verification record are preserved separately for
resumption in the retained workspace. The estimates in this memorandum remain
paper results, apart from the previously checked results cited as inputs.

The finite candidates extend the existing owning modules:
- Analysis/HermitianQuadraticPerturbation.lean: symmetric row energy and
  action defects modulo an annihilator, reusing the exact perturbation theorem.
- Analysis/FiniteOscillatoryKernel.lean: the rational mismatch kernel bound,
  reusing RationalLogSeparation.rational_log_peak_gap_bound.
- Analysis/ActualRationalLandauRightLine.lean: actual Mangoldt-weighted finite
  nonresonant bounds and their coefficient-weighted finite assembly.

Primary project sources:
- [Prior complex stability](https://github.com/Cnoack3/RiemannResearch/blob/7ef8da56e63a27a6f52c335d9b1cb0c38022b241/RiemannResearch/RH/SignedQuadraticComplexStability20261030.md).
- [Actual right-line series](https://github.com/Cnoack3/RiemannResearch/blob/457c5f379c82218b2a2b5797b89b5b2d2bc24fb4/RiemannResearch/Analysis/ActualRationalLandauRightLine.lean).
- [Complete signed contour and component estimates](https://github.com/Cnoack3/RiemannResearch/blob/457c5f379c82218b2a2b5797b89b5b2d2bc24fb4/RiemannResearch/Analysis/ActualUniformRationalLandau.lean).
- [Actual mollifier coefficients](https://github.com/Cnoack3/RiemannResearch/blob/457c5f379c82218b2a2b5797b89b5b2d2bc24fb4/RiemannResearch/Analysis/ActualMobiusZeroDetector.lean).
- [Density-band quadratic consumer](https://github.com/Cnoack3/RiemannResearch/blob/457c5f379c82218b2a2b5797b89b5b2d2bc24fb4/RiemannResearch/Analysis/ActualDirichletPolynomialDensityBand.lean).
- [Actual optimizer growth consumer](https://github.com/Cnoack3/RiemannResearch/blob/457c5f379c82218b2a2b5797b89b5b2d2bc24fb4/RiemannResearch/RH/QCRTOptimizerGrowth.lean).

Provenance: user-requested continuation and the cited project identities.
The finite inequalities use elementary quadratic identities, Cauchy--Schwarz,
and harmonic summation. No novelty claim is made.
