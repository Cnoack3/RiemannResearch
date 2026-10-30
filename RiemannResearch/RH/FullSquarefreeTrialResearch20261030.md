# Full-squarefree optimizer research continuation — 30 October 2026

## Result and scope

Continue with the actual minimum complete-Q energy optimizer over the ENTIRE
squarefree dictionary. The full-source signed cancellation route remains the
best-developed route in this project. This is a research judgment, not a
calibrated probability of proving RH.

This continuation establishes exact trial identities, a concrete arithmetic
trial estimate, and a cofinal growth consumer. It does NOT prove the arithmetic
growth estimate or RH.

The explicit pair below is one test of the full update. It does not replace
the optimizer by a prime-only, two-conductor, or fixed finite subdictionary.
All squarefree composite conductors remain available.

Source inspected before development:
8ddb3eb7563d6e1583626be2bcec744add44e5be on main. The connected GitHub branch
read agreed with the Lean workspace base.

## 1. Definitions and full squarefree exhaustion

For n≥1 put

$$
Q(n)=\frac1{\zeta(2)n^2},\qquad
g_d(n)=\frac{n\bmod d}{d},\qquad
\langle f,g\rangle_Q=\sum_{n\ge1}Q(n)f(n)g(n).
$$

All norms include the entire infinite tail. Write

$$
L_i=\operatorname{primorial}(2i+2),\qquad
U_i=\operatorname{span}_{\mathbb R}\{g_d:1<d\mid L_i\},
$$
$$
V=\overline{\operatorname{span}_{\mathbb R}
\{g_d:d\ge2,\ d\text{ squarefree}\}}^{L^2(Q)}.
$$

Primorial is indexed by a prime cutoff. Every divisor of L_i is squarefree,
including products of arbitrarily many distinct primes as i grows.

The new module [QCRTSquarefreeExhaustion](QCRTSquarefreeExhaustion.lean) proves:

- Every squarefree conductor d≥2 is in the actual scheduled dictionary for all i≥d.
- Every finite set of squarefree conductors is contained in all sufficiently late dictionaries.
- The algebraic supremum of the scheduled divisor spaces is exactly the full algebraic squarefree span.
- Its closure is exactly V.

In repository notation, qSquarefreeCRTSpan is the ALGEBRAIC squarefree span;
the closed space is its topologicalClosure. These must not be conflated.

These statements prove exhaustiveness, not constant approximation.

Define the actual minimum-energy exact-head optimizer and energy by

$$
F_i=\arg\min\{\|F\|_Q^2:F\in U_i,\ F(n)=1\ (1\le n\le i+1)\},
\qquad E_i=\|F_i\|_Q^2.
$$

Also define the actual OLD-dictionary minimum with the next head imposed:

$$
\widehat F_i=
\arg\min\{\|F\|_Q^2:F\in U_i,\ F(n)=1\ (1\le n\le i+2)\},
\qquad
C_i^{\mathrm{old}}=\|\widehat F_i\|_Q^2-E_i\ge0.
$$

This next-head feasibility is used for i>0. It is a different moving vector
from the enlarged-dictionary old-head optimizer Z_i in the original handoff.

## 2. Exact certificates for the FULL innovation basis

Retain the original handoff definitions:

$$
a_i=1-F_i(i+2),\qquad K_i=\|k_i\|_Q^2,
$$
$$
M_i=B_i+c_ic_i^\top/K_i,\qquad
s_i=f_i-a_ic_i/K_i.
$$

The actual coefficient indices are ALL added squarefree conductors, not only
primes or selected pairs. The existing independence theorem and the new
head shear prove that the adjusted family y_(i,d) is independent, even when
the index set is empty. At every post-initial squarefree observation site,
old-capacity positivity is proved by the existing arithmetic provider.

For ANY coefficient vector t_i on the complete added-conductor set define

$$
\mathcal C_i(t_i)=
\frac{a_i^2}{K_i}-2t_i^\top s_i+t_i^\top M_i t_i.
$$

The new exact identity is

$$
\boxed{\mathcal C_i(t_i)-(E_{i+1}-E_i)
 =\left\|m_i-\sum_d t_{i,d}y_{i,d}\right\|_Q^2\ge0,}
$$

where m_i is the actual minimum vector representing source s_i in the
adjusted basis. Equivalently, its coefficients are M_i^(-1)s_i.

The right side is the exact loss of the chosen trial. No spectral conditioning
bound or approximate Gram matrix is substituted.

Files and declarations:

- [FiniteGramTrialCertificate](../Analysis/FiniteGramTrialCertificate.lean):
  capacity_eq_inverseGram, inverseGram_trial_completion,
  inverseGram_trial_lower, inverseGram_direction_lower.
- [QCRTTrialCertificate](QCRTTrialCertificate.lean):
  jointFamily_independent, jointFamily_gram, dense_trial_completion,
  dense_step_le_trialCertificate, dense_direction_gain_lower.

The elementary dual inequality already existed in capacity form; this
continuation supplies its literal matrix version and the actual full-family
RH application. No novelty claim is made for the variational identity.

## 3. Preserve signed cancellation across stages

For an arbitrary family of FULL-basis coefficient vectors t_i, define a
complete stage certificate c_i:

- At i=0 use the exact increment E_1−E_0.
- At post-initial squarefree observation sites use $\mathcal C_i(t_i)$.
- At nonsquarefree observation sites use the exact negative dictionary gain −G_i.

Let ell_i be the squared trial loss at eligible squarefree sites and zero
at the other sites. Lean proves the exact telescope

$$
\boxed{E_N=E_0+\sum_{i<N}c_i-\sum_{i<N}\ell_i,\qquad \ell_i\ge0.}
$$

Thus all favorable signs survive, including negative increments and all
discarded trial-loss squares. Coefficient supports with disjoint indices
are not treated as orthogonal Hilbert directions.

Declarations: fullCertificate, fullLoss, dense_full_completion,
dense_trial_telescope, dense_energy_le_trial_sum.

## 4. The genuinely cofinal RH consumer

It is enough to control a sequence of physical heads S_m→∞:

$$
\frac{\log(1+E_{S_m})}{\log(S_m+2)}\longrightarrow0.
$$

The new theorem
riemannHypothesis_of_cofinal_subpolynomial_stageEnergy in
[QCRTOptimizerGrowth](QCRTOptimizerGrowth.lean) proves this implication to RH
by applying the existing exact-head Mellin-zero consumer directly to
F_(S_m). Bounds at intervening heads are unnecessary for THIS theorem.

Consequently, the new
riemannHypothesis_of_cofinal_trial_budget in
[QCRTTrialCertificate](QCRTTrialCertificate.lean) proves RH from:

$$
E_0+\sum_{i<S_m}c_i\le B_m,\qquad B_m\ge0,\qquad
\frac{\log(1+B_m)}{\log(S_m+2)}\longrightarrow0.
$$

These are explicit OPEN arithmetic premises. They are not supplied by
exhaustion, finite invertibility, or the trial identity.

A practical full-family target is S_m=2^m and a signed block estimate

$$
\sum_{i=2^m}^{2^{m+1}-1}c_i
\le \frac{A}{m+1}E_{2^m}+B
$$

for fixed A,B≥0, after absorbing finitely many initial terms.
The exact telescope then gives the corresponding dyadic recurrence.
Ordinary discrete Gronwall yields a polynomial bound in m, for example
E_(2^m)=O((m+1)^(A+1)), which is subpolynomial in the PHYSICAL head 2^m.

This last displayed arithmetic block estimate is a proposed sufficient
target, not a proved estimate or a new unconditional theorem. The checked
cofinal consumer removes the interpolation obligation that the older
all-stage formulation would otherwise require.

## 5. An explicit arithmetic trial and its exact energy constant

For any positive p define

$$
h_p=g_p-2g_{2p}.
$$

The refinement identity gives

$$
h_p(n)=-\bigl(\lfloor n/p\rfloor\bmod2\bigr),\qquad h_p(n)=0\quad(n<p).
$$

Equivalently h_p is the floor dilation of −2g_2. Its old-anchor terms
cancel exactly before screening. The binary base has exact Q norm square
3/4. The sharp complete-Q floor-dilation inequality therefore gives

$$
\boxed{\|h_p\|_Q^2\le\frac{3}{4p}.}
$$

All these claims are formalized in
[QCRTPrimePairTrial](QCRTPrimePairTrial.lean), including the sequence,
head vanishing, anchor cancellation, and divisor-stage membership.

When p=2i+3 is prime and i>0, both p and 2p are legal newly admitted
squarefree conductors. Since i+2<p, h_p vanishes on the EXTENDED head.
Put

$$
S_i(p)=\langle\widehat F_i,h_p\rangle_Q,\qquad
Y_i(t)=\widehat F_i-t h_p.
$$

Then Y_i(t) is a genuine competitor for the full enlarged-dictionary
minimum F_(i+1). The minimum completion identity gives

$$
\boxed{
C_i^{\mathrm{old}}-2tS_i(p)+t^2\|h_p\|_Q^2
 -(E_{i+1}-E_i)
 =\|Y_i(t)-F_{i+1}\|_Q^2.}
$$

Choose t=4pS_i(p)/3. The norm bound yields the unconditional finite-stage estimate

$$
\boxed{
E_{i+1}-E_i\le
 C_i^{\mathrm{old}}-\frac{4p}{3}S_i(p)^2.}
$$

The exact favorable remainder is the sum of the displayed competitor loss
and t^2[3/(4p)−||h_p||²]. No positivity of the physical values of the moving
optimizer is assumed.

This is formalized in
[QCRTPrimePairCertificate](QCRTPrimePairCertificate.lean):
primePair_completion, primePair_step_le_cost_sub_source_sq,
dense_new_prime_pair_bound.

This result does not claim that one pair captures enough of the FULL gain
to prove subpolynomial growth.

## 6. A full-family arithmetic coordinate system

At a new prime p=2i+3, retain EVERY old divisor d|L_i, including composite d.
The complete newly admitted conductors have the form p*d.

Write D_p f(n)=f(floor(n/p)) and

$$
t_{p d}=g_{p d}-\frac{L_i}{pd}g_{L_i}.
$$

The exact arithmetic refinement is

$$
\boxed{
t_{p d}=D_p g_d+\frac1d\,t_p\qquad(d>0).}
$$

After the ACTUAL Q projection away from the old tangent,

$$
\boxed{
(I-P_{T_i})t_{p d}
=(I-P_{T_i})D_p g_d+\frac1d(I-P_{T_i})t_p.}
$$

Thus the full family is organized by the complete old squarefree divisor
dictionary and one compensated prime direction. Taking d=1 retains the
extra direction because g_1=0. This is a change of coordinates for the
whole family, not a restriction to prime atoms.

The equalities are formalized as rawDirection_floor_block and
screenedDirection_floor_block in
[QCRTPrimeInnovation](QCRTPrimeInnovation.lean). Their algebra is valid for
every d>0; identifying legal new conductors uses the primorial arithmetic.
The finite indexing classification itself is an elementary prime-factor
argument, not a new independently formalized divisor-enumeration theorem here.

The appropriate next construction is a coefficient rule using this FULL
family, with the actual joint source and adjusted complete Gram form.
A dyadic estimate should sum its gains over prime-enlargement stages while
also paying costs at squarefree head stages having no dictionary enlargement.

## 7. Numerical diagnostics and their limits

The diagnostic source in the appendix uses complete-period weights

$$
w_L(r)=\frac{\psi_1(r/L)}{\zeta(2)L^2},\qquad1\le r\le L.
$$

There is no physical-coordinate cutoff. However, trigamma evaluation and
matrix solves are DOUBLE-PRECISION NUMERICS, without interval certification.
The numbers below are exploratory, not kernel-checked bounds.

| New p | Old extension cost | Full head-first gain J | Numeric value of (4p/3)S² |
|---:|---:|---:|---:|
| 5 | 0.252249679 | 0.185261485 | 0.071936592 |
| 7 | 0 | 0.011138126 | 0.000940723 |
| 11 | 0.028414821 | 0.005948926 | 0.000332933 |
| 13 | 0.025895710 | 0.002964434 | 0.000140592 |
| 17 | 0 | 0.003569322 | 0.000205240 |

The zero old extension costs at p=7 and p=17 follow exactly from the
nonsquarefree next-head redundancy; floating-point noise there is not
a mathematical cost.

The single pair is too weak to explain useful cancellation at the tested
p=11 and p=13 stages. Larger floor-dilated old-dictionary blocks, after
screening away the extended old tangent, captured approximately 79%, 85%,
83%, and 91% of J at p=5,7,11,13. This motivates investigating the full
arithmetic coordinate system. It is not evidence of a uniform capture
fraction, and a fixed fraction of J need not itself imply RH.

The new Gram condition numbers in these small diagnostics grow from about
123 at p=5 to 4.18 million at p=17; maximum head residual was below
4.7e−15. Neither statistic certifies the computed gains.

The script solves complete-period normal equations using floating-point
pseudoinverses for redundant head constraints. Reproduce its results before
making a numerical inference, and use rigorous enclosures before promoting
a finite numerical claim into a certificate.

## 8. Primary-paper connection and safeguards

Werner Ehm, *On certain Gram matrices and their associated series*,
arXiv:2405.06349v2, Section 8:
https://arxiv.org/html/2405.06349v2

The paper decomposes classical Nyman–Beurling Gram forms and constructs
moment-adjusted coefficients. It explicitly leaves difficult inversion-error
estimates unresolved. It is useful as a design source for full-family moment
conditions; its classical continuous kernels are not a proved substitute
for this moving squarefree Q optimizer.

Manzur–Noor's Hardy-space operator criterion,
https://arxiv.org/html/2610.03568v1, remains a separate alternative.
No Hardy closure assumption, RH-dependent spectral theorem, or unproved
intertwining map is used in the Lean results here.

Avoid these shortcuts:

- Replacing the full squarefree dictionary by primes, a selected pair, or a fixed conductor set.
- Conflating the old-head enlarged-dictionary minimum Z_i with the next-head old-dictionary minimum widehat F_i.
- Treating legal exact-head agreement as a bound on complete energy.
- Assuming that actual minimum-energy sequences are pointwise nonnegative.
- Adding gains of coefficient blocks without their Gram cross terms.
- Measuring subpolynomial growth in the primorial period instead of the physical head.
- Treating finite numerical capture as an all-stage arithmetic estimate.

## 9. Verification ledger

Serialized isolated verification included:

- job_GDB5Pf7hgyFldirLhkF8EjBEiaHY80rt:
  exact actual full-family trial identities, success.
- job_ruHDm8oqDx-6K2CN5q6Y8eTdzxY5GqbU:
  improved prime-pair arithmetic application, success.
- job_dNX3t9eMTc9_pDjexj3ZPTtyIH5o2b0e:
  full squarefree exhaustion and selected axiom checks, success.
- job_5yiMw6Df2HEac2b34ki1e1nUIvGID7IP:
  full floor-block decomposition before and after screening, success.

The selected exact trial identity, cofinal RH implication, prime-stage
inequality, and full squarefree closure identity depend only on propext,
Classical.choice, and Quot.sound in the reported audits.

A standard-axiom audit does not discharge the arithmetic hypotheses in the
conditional RH theorem. Saved-source validation and publication are gated
by the final server checkpoint; the checkpoint result and published commit
are reported with delivery. Isolated checks are not described as a build
of the whole repository.

## 10. Research agenda, in execution order

1. Keep the entire squarefree dictionary and use the proved exhaustive schedule.
2. Express the FULL adjusted innovation family in floor-block plus compensated-prime coordinates.
3. Develop explicit moment-adjusted coefficient rules over all old squarefree divisors,
   preserving the joint-source correction and every Gram cross term.
4. Bound a signed dyadic block of actual certificates. Include squarefree head costs
   between prime-enlargement stages.
5. Seek the proposed dyadic recurrence, or directly a subpolynomial cofinal
   signed-certificate budget. A bound in the head index is the required output.
6. Feed a proved provider into riemannHypothesis_of_cofinal_trial_budget.
7. Only after that exact theorem specializes without an open arithmetic
   premise is RH obtained.

The unresolved item is Step 4/5: a sufficiently strong estimate for the
moving full-squarefree sources and their signed cumulative cancellation.
The finite algebra and full-family exhaustion are now explicit verified
infrastructure for that estimate.


## Appendix: reproducible numerical diagnostic source

Run this locally with Python, NumPy and SciPy. It prints exploratory JSON;
it supplies no interval certificate and is not part of Lean verification.

```python
"""Uncertified full-period Q diagnostics; no physical-coordinate truncation.

Q-period weights use trigamma(r/L)/(zeta(2)*L**2). Linear algebra is
double precision. These data do not establish an all-stage estimate.
"""
import json
from math import prod
import numpy as np
from scipy.linalg import solve
from scipy.special import polygamma

ZETA2 = np.pi**2 / 6


def divisors(primes):
    out = [1]
    for p in primes:
        out += [p*d for d in out]
    return np.array(sorted(out)[1:], dtype=np.int64)


def full_gram(L, ds):
    G = np.zeros((len(ds), len(ds)))
    for start in range(1, L+1, 8192):
        r = np.arange(start, min(L+1, start+8192), dtype=np.int64)
        X = (r[:, None] % ds[None, :]) / ds[None, :]
        w = polygamma(1, r/L) / (ZETA2*L**2)
        G += X.T @ (w[:, None]*X)
    return G


def optimizer(ds, G, H):
    A = (np.arange(1, H+1)[:, None] % ds[None, :]) / ds[None, :]
    C = solve(G, A.T, assume_a='pos')
    N = A @ C
    c = C @ (np.linalg.pinv(N, rcond=1e-12) @ np.ones(H))
    return c, float(c@G@c), int(np.linalg.matrix_rank(A)), float(np.max(np.abs(A@c-1)))


for p, oldps in [(5,[2,3]), (7,[2,3,5]), (11,[2,3,5,7]),
                 (13,[2,3,5,7,11]), (17,[2,3,5,7,11,13])]:
    L = prod(oldps)
    oldds, newds = divisors(oldps), divisors(oldps+[p])
    Gnew = full_gram(p*L, newds)
    idx = {int(d): j for j,d in enumerate(newds)}
    oldidx = np.array([idx[int(d)] for d in oldds])
    Gold = Gnew[np.ix_(oldidx,oldidx)]
    Hold = (p-1)//2
    n = Hold+1
    cold,Eold,rankold,errold = optimizer(oldds,Gold,Hold)
    ch,Eh,rankh,errh = optimizer(oldds,Gold,n)
    cn,En,rankn,errn = optimizer(newds,Gnew,n)
    chnew = np.zeros(len(newds)); chnew[oldidx]=ch
    Aext=(np.arange(1,n+1)[:,None]%oldds[None,:])/oldds[None,:]
    oldGinv=solve(Gold,np.eye(len(oldds)),assume_a='pos')
    oldC=oldGinv@Aext.T
    tangentInverse=oldGinv-oldC@np.linalg.pinv(Aext@oldC,rcond=1e-12)@oldC.T

    def screened_gain(R, B, source):
        cross=Gnew[np.ix_(oldidx,np.arange(len(newds)))]@R
        screened=B-cross.T@tangentInverse@cross
        value=float(source@solve(screened,source,assume_a='pos'))
        return value
    rawpair = np.zeros(len(newds)); rawpair[idx[p]]=1; rawpair[idx[2*p]]=-2
    S = float(chnew@Gnew@rawpair)
    D = float(rawpair@Gnew@rawpair)
    record = dict(p=p,oldPeriod=L,newPeriod=p*L,oldHead=Hold,nextSite=n,
                  Eold=Eold,EoldExtendedHead=Eh,EnewNextHead=En,
                  cost=Eh-Eold,J=Eh-En,source=S,pairNormSq=D,
                  coarseCapturedGain=p*S*S,rawCapturedGain=S*S/D,
                  conditionNewGram=float(np.linalg.cond(Gnew)),
                  maxHeadError=max(errold,errh,errn),headRanks=[rankold,rankh,rankn])
    # Small structured block, plus all odd-divisor binary pairs.
    odddivs=[1]+[int(d) for d in oldds if d%2]
    for tag, selected in [('smallOddPairs',[d for d in odddivs if d<=7]),
                          ('allOddPairs',odddivs)]:
        R=np.zeros((len(newds),len(selected)))
        for j,d in enumerate(selected):
            R[idx[p*d],j]=1; R[idx[2*p*d],j]=-2
        B=R.T@Gnew@R
        source=chnew@Gnew@R
        rawgain=float(source@solve(B,source,assume_a='pos'))
        adjusted=screened_gain(R,B,source)
        record[tag]=dict(d=selected,gain=rawgain,captureFraction=rawgain/(Eh-En),
                         screenedGain=adjusted,screenedCapture=adjusted/(Eh-En))
    # Entire floor-dilated old residue dictionary, a valid raw trial family.
    R=np.zeros((len(newds),len(oldds)))
    for j,d in enumerate(oldds):
        R[idx[p*int(d)],j]=1; R[idx[p],j]=-1/d
    B=R.T@Gnew@R
    source=chnew@Gnew@R
    rawgain=float(source@solve(B,source,assume_a='pos'))
    adjusted=screened_gain(R,B,source)
    record['fullFloorBlock']=dict(dim=len(oldds),gain=rawgain,captureFraction=rawgain/(Eh-En),
                                 screenedGain=adjusted,screenedCapture=adjusted/(Eh-En))
    print(json.dumps(record),flush=True)
```
