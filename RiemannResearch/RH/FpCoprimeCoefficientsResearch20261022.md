# Explicit coprime coefficients and legal Gram comparison

22 October 2026, Pacific time.

Source: the user's requested continuation of commit
[f8284c0d39e8ae1817bd24297da9a24f984c23bc](https://github.com/Cnoack3/RiemannResearch/commit/f8284c0d39e8ae1817bd24297da9a24f984c23bc).
The coefficient calculations below use the existing divisor wavelets and exact Q-dilation law.
No RH hypothesis is used.

## 1. Objects and scope

Let \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\) on positive integers,
\(F_p(n)=\lfloor\log_p n\rfloor\), and \(g_d(n)=(n\bmod d)/d\).
The auxiliary zero coordinate is zero.
Let H be the closed real span of squarefree \(g_d\), \(d>1\), and let
\(C=\overline{H+\mathbb R1}\).

The ambient divisor basis is
\[
 V_t=\sum_{d\mid t}\mu(t/d)d^2\,1_{d\mid n},\qquad
 B_t=\frac{V_t}{\sqrt{J_2(t)}},\qquad
 J_2(t)=t^2\prod_{\ell\mid t}(1-\ell^{-2}).
\]
It is a complete basis of the ambient Q Hilbert space. It is not a legal basis of H or C.
The cofactor coefficient is \(\alpha_{p,t}=\langle F_p,B_t\rangle_Q\) when \(t>1\) is coprime to p.

The new Lean declarations prove the finite signed coefficient formula, prime-power difference formula,
summability, literal head-tail identities, coefficient bounds, two stronger ambient residual bounds,
and a single-mode non-preservation counterexample.
The level-set evaluations, numerical tables, and finite-dimensional minimizations below are
ordinary calculations, not additional Lean-certified numerical statements.

## 2. The exact arithmetic coefficient

Define the complete dilated mean
\[
 M_p(d)=\frac1Z\sum_{n\ge1}\frac{F_p(dn)}{n^2}.
\]
The weighted series is summable for every \(d>0\).
Dilation gives \(\langle F_p,1_{d\mid n}\rangle_Q=d^{-2}M_p(d)\).
Consequently
\[
 \boxed{\alpha_{p,t}
  =\frac1{\sqrt{J_2(t)}}\sum_{d\mid t}\mu(t/d)M_p(d).}
\]
This formula applies to every positive conductor, including conductors outside the cofactor support.
Every signed term remains present.
The factors \(d^2\) and \(d^{-2}\) cancel exactly.

The checked declarations are qTarget_inner_basis_moebius and
qTarget_scaled_divisor_mean in QPrimePowerCoprimeCoefficients.lean.
The general Q-Hilbert version is normalizedDivisorWavelet_inner_dilation
in QDivisorDilationCoefficients.lean.

The exact p-power dilation is
\[
 M_p(p^k d)=M_p(d)+k,\qquad M_p(1)=\mu_p.
\]
For any prime q and \(k\ge1\),
\[
 \boxed{\alpha_{p,q^k}
   =\frac{M_p(q^k)-M_p(q^{k-1})}{\sqrt{J_2(q^k)}}.}
\]
These identities still concern the floor logarithm, not the valuation.

## 3. Evaluate the means without discarding infinite tails

Put \(T(m)=\sum_{n=m}^{\infty}n^{-2}\) for \(m\ge1\).
For integer m this is \(Z-H_{m-1}^{(2)}\), equivalently the trigamma value \(\psi_1(m)\).
Expanding the floor logarithm into its threshold indicators and summing nonnegative terms gives
\[
 \boxed{M_p(d)=\frac1Z\sum_{j\ge1}
          T\!\left(\left\lceil\frac{p^j}{d}\right\rceil\right).}
\]
Thus all the displayed coefficients are explicit convergent arithmetic series.
No reduction to a finite combination of familiar constants is claimed.

For a prime-power coefficient, write \(a=q^k\), \(b=q^{k-1}\).
There is a particularly transparent positive interval formula:
\[
 \boxed{\alpha_{p,q^k}
 =\frac1{Z\sqrt{J_2(q^k)}}\sum_{j\ge1}
   \sum_{n=\lceil p^j/a\rceil}^{\lceil p^j/b\rceil-1}\frac1{n^2}.}
\]
An interval with upper endpoint below its lower endpoint contributes zero.
The infinite sum over j is essential.

For example, define
\[
 C_{p,d}=\frac1Z\sum_{j\ge0}
  \sum_{n=\lceil p^{j+\ell+1}/d\rceil}^{p^{j+1}-1}\frac1{n^2},
 \qquad \ell=\lfloor\log_p d\rfloor.
\]
Then \(M_p(d)-M_p(1)=\ell+C_{p,d}\), with \(0\le C_{p,d}\le1\).
In particular
\[
 \alpha_{2,3}=\frac{1+C_{2,3}}{\sqrt8},\quad
 \alpha_{2,5}=\frac{2+C_{2,5}}{\sqrt{24}},\quad
 \alpha_{3,2}=\frac{C_{3,2}}{\sqrt3},\quad
 \alpha_{3,5}=\frac{1+C_{3,5}}{\sqrt{24}}.
\]

There is an elementary geometric tail bound.
The integral comparison gives \(T(m)\le m^{-1}+m^{-2}\), hence
\[
 0\le M_p(d)-\frac1Z\sum_{j=1}^{K}T(\lceil p^j/d\rceil)
 \le \frac1Z\left[
 \frac{d}{(p-1)p^K}+\frac{d^2}{(p^2-1)p^{2K}}\right]=:\tau_{p,d,K}.
\]
This is valid for every \(K\ge0\), \(p>1\), and \(d>0\).
For a signed divisor coefficient the remaining tail belongs to
\[
 \left[-\frac{\sum_{\mu(t/d)<0}|\mu(t/d)|\tau_{p,d,K}}{\sqrt{J_2(t)}},
        \frac{\sum_{\mu(t/d)>0}\mu(t/d)\tau_{p,d,K}}{\sqrt{J_2(t)}}\right].
\]
This retains the signs instead of identifying the finite sum with the full coefficient.
The analytic tail bound does not certify floating-point rounding.

## 4. First coprime conductors

In each row \(M=M_p\) for that row's target.
The exact expressions instantiate the checked general coefficient formula.
The decimals are numerical exploration using 80 threshold levels, not Lean or interval certificates.

| Target | Conductor | Exact expression | Approximate coefficient |
|---|---:|---|---:|
| F2 | 3 | \((M(3)-M(1))/\sqrt8\) | 0.400895638890 |
| F2 | 5 | \((M(5)-M(1))/\sqrt{24}\) | 0.414561057413 |
| F2 | 7 | \((M(7)-M(1))/\sqrt{48}\) | 0.313728219091 |
| F2 | 9 | \((M(9)-M(3))/\sqrt{72}\) | 0.220757521977 |
| F2 | 11 | \((M(11)-M(1))/\sqrt{120}\) | 0.285183949546 |
| F2 | 13 | \((M(13)-M(1))/\sqrt{168}\) | 0.244532826373 |
| F2 | 15 | \((M(15)-M(5)-M(3)+M(1))/\sqrt{192}\) | 0.001464300581 |
| F3 | 2 | \((M(2)-M(1))/\sqrt3\) | 0.143396036656 |
| F3 | 4 | \((M(4)-M(2))/\sqrt{12}\) | 0.226316922534 |
| F3 | 5 | \((M(5)-M(1))/\sqrt{24}\) | 0.247430209194 |
| F3 | 7 | \((M(7)-M(1))/\sqrt{48}\) | 0.187353624802 |
| F3 | 8 | \((M(8)-M(4))/\sqrt{48}\) | 0.039584174871 |
| F3 | 10 | \((M(10)-M(5)-M(2)+M(1))/\sqrt{72}\) | 0.063945272737 |
| F3 | 11 | \((M(11)-M(1))/\sqrt{120}\) | 0.184034612573 |

The very small conductor-15 coefficient for F2 illustrates substantial signed cancellation.
No general sign rule for composite conductors is assumed.
Independent physical sums through 300,000 provide a second numerical check; their omitted tails remain nonzero.

## 5. Checked bounds and complete residuals

The elementary multiplicative floor-log inequality is
\[
 \lfloor\log_p q\rfloor
 \le F_p(qn)-F_p(n)
 \le \lfloor\log_p q\rfloor+1\qquad(n>0).
\]
Averaging after any positive integer dilation yields
\[
 \boxed{\frac{\lfloor\log_p q\rfloor}{\sqrt{J_2(q^k)}}
 \le \alpha_{p,q^k}
 \le \frac{\lfloor\log_p q\rfloor+1}{\sqrt{J_2(q^k)}}.}
\]
These statements are checked in log_mul_bounds, dilatedTargetMean_mul_bounds,
and qTarget_inner_primePower_bounds.

The new exact finite-mode error identity, for arbitrary actual Q-Hilbert f and g, is
\[
 \boxed{\|f-g\|_Q^2
 =\sum_{t\in S}(\langle f,B_t\rangle_Q-\langle g,B_t\rangle_Q)^2+
 \left\|f-g-\sum_{t\in S}
  (\langle f,B_t\rangle_Q-\langle g,B_t\rangle_Q)B_t\right\|_Q^2.}
\]
The entire remainder is retained.
It gives the corresponding finite-mode lower bound without a sign assumption on trial data.

Applying the coefficient bounds at conductor 3 for F2 and conductor 5 for F3 gives
\[
 \boxed{\|R_2\|_Q^2\ge\frac18,\qquad \|R_3\|_Q^2\ge\frac1{24}.}
\]
These improve the earlier ambient bounds \(1/(10Z)\) and \(1/(17Z)\).
They are not distance bounds for H or C.
The actual residual energies are numerically about 1.043253458779 and 0.399352071311.
Combining further distinct coprime modes gives additional Bessel lower bounds by the same checked finite identity.

## 6. Compare the actual legal Gram projections

For a finite squarefree dictionary D, with or without the physical constant, write
\[
 G_{de}=\langle g_d,g_e\rangle_Q,\qquad
 b_d=\langle F_p,g_d\rangle_Q.
\]
For an arbitrary signed coefficient vector c the exact error is
\[
 \boxed{\|F_p-\sum_{d\in D}c_dg_d\|_Q^2
 =\|F_p\|_Q^2-2c^\mathsf Tb+c^\mathsf TGc.}
\]
When the selected vectors are independent, the exact minimum is
\(\|F_p\|_Q^2-b^\mathsf TG^{-1}b\).
The computational experiment uses this complete quadratic form, retaining every cross term.

The bridge to the ambient coordinates is also exact:
\[
 \beta_{t,d}:=\langle g_d,B_t\rangle_Q
 =\frac1{\sqrt{J_2(t)}}\sum_{k\mid t}\mu(t/k)
     \mathbb E_Q[g_d(kN)].
\]
The Lean theorem normalizedDivisorWavelet_residue_coefficient expresses this
using the existing qResidueDivisorCoefficient and twisted residue means.
Each twisted mean is a finite trigamma sum over a complete residue period.

Thus, for any finite signed legal trial,
\[
 \|F_p-\sum_dc_dg_d\|_Q^2
 =\sum_{t\ge1}\left(\langle F_p,B_t\rangle_Q-\sum_dc_d\beta_{t,d}\right)^2.
\]
Both the discrepancy on the target's support and every off-support legal mode are required.
Keeping only selected t gives a lower bound, not a certified upper bound for legal approximation.
An upper bound requires an actual legal trial and its complete remainder.

The following are floating-point minimum squared errors, using all squarefree conductors \(2\le d\le N\).
H_N excludes the constant and C_N includes it.
Gram entries use full-period trigamma formulas; target moments use threshold sums with controlled analytic tails.

| N | F2: H_N | F2: C_N | F3: H_N | F3: C_N |
|---:|---:|---:|---:|---:|
| 2 | 1.8966816045 | 1.1543645699 | 0.6076673819 | 0.5194146480 |
| 6 | 0.8770669282 | 0.8080902062 | 0.3250742533 | 0.3039123856 |
| 15 | 0.3669130760 | 0.3661036038 | 0.1469791671 | 0.1468443283 |
| 30 | 0.1844418063 | 0.1821814685 | 0.0788788428 | 0.0770980422 |

The largest reported Gram condition number is about 2,000.
At N=30 an independent physical residual sum through 300,000 lies below each full-formula value,
and the difference lies within the elementary integral bound for the remaining physical tail.
This is a numerical consistency check, not an interval or Lean certificate.
The observed decrease supplies no limit-zero theorem.

## 7. A checked obstruction to ambient mode selection

Let \(\Pi_3f=\langle f,B_3\rangle_Q B_3\), and set \(m_3=\mathbb E_Q[g_3]>0\).
The exact identities are
\[
 B_3=(9\,1_{3\mid n}-1)/\sqrt8,\qquad
 \langle g_3,B_3\rangle_Q=-m_3/\sqrt8.
\]
Every f in C obeys the square-jump equation
\[
 L_2(f):=f(4)-f(3)-f(2)+f(1)=0.
\]
The new calculation gives
\[
 \boxed{L_2(\Pi_3g_3)=9m_3/8>0.}
\]
Therefore \(g_3\in H\subset C\) while \(\Pi_3g_3\notin C\).
This is checked by residue_three_single_mode_defect and
ambient_single_mode_not_legal_preserving in QDivisorModeLegality.lean.

This counterexample concerns a single-mode cut.
It does not itself identify the behavior of a cut onto an entire infinite conductor family.
In particular, no preservation theorem for the full coprime cofactor support is used.

## 8. What the expansion does and what remains for RH

The ambient coefficient map is an isometry.
For any exhaustion of the legal squarefree dictionaries, replacing vectors by their full divisor coordinates
therefore gives an equivalent approximation problem. It is not a stronger membership criterion.
The explicit arithmetic coefficients are useful computational and structural information;
they do not provide the missing uniform legal-tail estimate.

Unconditional, checked conclusions:

- Every conductor coefficient has the finite signed dilation formula.
- Prime-power conductors have exact adjacent-mean differences and explicit bounds.
- The physical means are summable and split into an exact finite head and complete infinite tail.
- Selected signed coefficient discrepancies have a complete orthogonal error remainder.
- The ambient cofactor energies satisfy the stronger bounds 1/8 and 1/24.
- A concrete ambient single-mode projection fails to preserve even C.

Open:

- Prove or disprove the target membership of F2 or F3 in the actual legal closure required by the existing RH consumer.
- Prove legal Parseval saturation, or supply legal trials whose complete-Q error tends to zero.
- Control omitted legal modes uniformly as the dictionary grows.
- Obtain interval-certified numerical Gram bounds; floating-point tables are not such certificates.
- Formalize the threshold/trigamma coefficient algorithm and its geometric tail bound in Lean.

The existing domain-specific target-membership obligation is not discharged.
No unconditional RH claim is made.

## 9. Research agenda

1. Use the exact beta columns to solve finite legal coefficient fits with the full Gram form.
   Keep separate records of selected-mode error and complete complementary error.
2. Turn selected-mode comparisons into useful uniform estimates by controlling the complementary legal Gram block.
   Exact arithmetic of alpha alone does not control this block.
3. Use the positive prime-power interval formulas to obtain sharper cofactor-energy bounds and conductor-tail estimates.
   Preserve signed cancellation at composite conductors such as 15.
4. Formalize coprime conditional expectation under the independent valuation/cofactor law.
   Finite residue-cycle averages give concrete test cases for the behavior of whole-support projections;
   the single-mode theorem should not be overinterpreted as proving that result.
5. Construct bounds for actual squarefree legal trials, possibly with the previously developed exact-head constraints.
   A uniform bounded-head provider or a complete-error limit is still the relevant RH bridge.
6. Treat increasing finite dictionary experiments as diagnostics, not as evidence that the infinite residual vanishes.

## Verification and reproduction

Saved-source audit job_KKzufSXky1fZEHuoYg_hE31wTjIgZjzv succeeded (exit 0; server-reported verification duration 13.819 seconds).
All 16 inspected declarations depend only on propext, Classical.choice, and Quot.sound.
The audit imported all three saved modules. No unresolved RH-domain hypothesis is used by these declarations.
The measured audit queue delay was below 0.001 seconds. Polling delay is separate from verification duration.
The workspace-opening round trip was not separately timed and is not counted as proof-checking time.
The final checkpoint is the publication gate for the exact saved modules and their aggregate consumer.
No Lean declaration contains a placeholder proof, project-local axiom, or unsafe shortcut.

The following Python experiment requires NumPy and SciPy.
It reports floating-point exploration explicitly and retains analytic tails separately from rounding.

```python
# Copyright (c) 2026 Christian Noack. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Numerical exploration only: NumPy/SciPy rounding is not interval certified.
import math
import json
from functools import lru_cache
import numpy as np
from scipy.special import polygamma

Z = math.pi**2 / 6
K = 80

def divisors(t):
    return [d for d in range(1,t+1) if t%d == 0]

def mobius(t):
    s = 1
    p = 2
    while p*p <= t:
        if t%p == 0:
            t //= p
            s = -s
            if t%p == 0:
                return 0
        p += 1
    return -s if t>1 else s

def jordan(t):
    return sum(mobius(t//d)*d*d for d in divisors(t))

@lru_cache(None)
def mean(p,d):
    return math.fsum(float(polygamma(1, float((p**k+d-1)//d)))/Z for k in range(1,K+1))

def alpha(p,t):
    return math.fsum(mobius(t//d)*mean(p,d) for d in divisors(t))/math.sqrt(jordan(t))

def mean_tail_bound(p,d):
    # psi_1(ceil(p^k/d)) <= d/p^k + d^2/p^(2k).
    return (d/((p-1)*p**K)+d*d/((p*p-1)*p**(2*K)))/Z

def physical_alpha(p,t,N=300000):
    # Independent check, using bounded signed increments after cancellation of log n.
    n=np.arange(1,N+1,dtype=np.int64)
    def fl(a):
        r=np.zeros(N,dtype=np.int64)
        power=p
        while power <= a*N:
            r += a*n >= power
            power *= p
        return r
    vals=sum((mobius(t//d)*fl(d) for d in divisors(t)),np.zeros(N,dtype=np.int64))
    return float(np.sum(vals/n.astype(float)**2)/Z/math.sqrt(jordan(t)))

def gram(d,e):
    L=math.lcm(d,e)
    return math.fsum((r%d)/d*(r%e)/e*float(polygamma(1,r/L)) for r in range(1,L+1))/(Z*L*L)

def residue_mean(d):
    return math.fsum((r%d)/d*float(polygamma(1,r/d)) for r in range(1,d+1))/(Z*d*d)

@lru_cache(None)
def b(p,d):
    return math.fsum(math.fsum((r%d)/d*float(polygamma(1, (r+d*max(0,(p**k-r+d-1)//d))/d)) for r in range(1,d+1))/(Z*d*d) for k in range(1,K+1))

def energy(p):
    return math.fsum((2*k-1)*float(polygamma(1,float(p**k)))/Z for k in range(1,K+1))

def project(p,N,constant=True):
    ds=[d for d in range(2,N+1) if mobius(d)!=0]
    G=np.array([[gram(d,e) for e in ds] for d in ds])
    B=np.array([b(p,d) for d in ds])
    if constant:
        ms=np.array([residue_mean(d) for d in ds])
        G=np.block([[np.ones((1,1)),ms.reshape(1,-1)],[ms.reshape(-1,1),G]])
        B=np.r_[mean(p,1),B]
    c=np.linalg.solve(G,B)
    E=energy(p)-float(B@c)
    return dict(p=p,N=N,constant=constant,dimension=len(B),error_squared=E,condition=float(np.linalg.cond(G)),coefficients=c.tolist(),conductors=ds)

def physical_trial_check(row,N=300000):
    p=row['p']; n=np.arange(1,N+1,dtype=np.int64)
    f=np.zeros(N)
    cs=row['coefficients']
    if row['constant']:
        f += cs[0]
        cs=cs[1:]
    for c,d in zip(cs,row['conductors']):
        f += c*(n%d)/d
    target=np.zeros(N)
    power=p
    while power<=N:
        target += n>=power
        power*=p
    head=float(np.sum((target-f)**2/n.astype(float)**2)/Z)
    B=sum(abs(c) for c in row['coefficients']); L=math.log(N); lp=math.log(p)
    tail=((L*L+2*L+2)/(lp*lp)+2*B*(L+1)/lp+B*B)/(Z*N)
    return dict(head=head,analytic_tail_upper=tail,head_cutoff=N,
                formula_minus_physical_head=row['error_squared']-head)

if __name__=='__main__':
    rows=[]
    for p,ts in [(2,[3,5,7,9,11,13,15]),(3,[2,4,5,7,8,10,11])]:
        for t in ts:
            v=alpha(p,t)
            rows.append(dict(p=p,t=t,jordan=jordan(t),alpha=v,physical_head=physical_alpha(p,t),geometric_tail_bound=math.fsum(abs(mobius(t//d))*mean_tail_bound(p,d) for d in divisors(t))/math.sqrt(jordan(t))))
    projections=[project(p,N,c) for p in [2,3] for N in [2,3,5,6,10,15,20,30] for c in [False,True]]
    for row in projections:
        if row['N']==30:
            row['independent_physical_check']=physical_trial_check(row)
    targets=[dict(p=p,mean=mean(p,1),energy=energy(p),cofactor_energy=energy(p)-mean(p,1)**2-p*p/(p*p-1)**2) for p in [2,3]]
    print(json.dumps(dict(status='Floating-point exploration, not a Lean or interval certificate',level_cutoff=K,targets=targets,coefficients=rows,projections=projections),indent=2))
```

## Checked threshold decomposition (22 October 2026, Pacific time)

QPrimePowerThresholdSeries.lean now proves the threshold-series identity
above, including its summability justification under the actual integer Zipf
law. Set c(p,d,j) = (p^(j+1)-1)/d + 1, using natural division. For d>0 this
is exactly ceil(p^(j+1)/d). With w(n)=positiveQWeight(n), define
A(p,d,j) = sum over n>=c(p,d,j) of w(n). Then
M_p(d) = sum over j>=0 of A(p,d,j), with a proved convergent nonnegative series.

For K levels, the exact remainder is sum_j A(p,d,j+K), not zero.
qTarget_basis_threshold_error_exact retains the signed coefficient error
as the finite divisor sum of mu(t/d) times these tails, divided by sqrt(J_2(t)).
No absolute-value replacement or deletion of negative terms is made.

For prime q and k>=0, primePowerThresholdTerm is the finite sum
  sum_{c(p,q^(k+1),j) <= n < c(p,q^k,j)} w(n) / sqrt(J_2(q^(k+1))).
qTarget_primePower_threshold_hasSum proves that its infinite sum is exactly
the coefficient of F_p at conductor q^(k+1). Each term is nonnegative.
The finite threshold heads converge to the coefficient, and
qTarget_primePower_threshold_head_tail retains the complete remaining series.
This specializes to F_2 and F_3 without identifying either with a valuation.

The candidate passed job_sE262lEumMs6e9EXL0mk4e18ygw_PjaJ (exit 0,
7.808 seconds). Saved-source audit job_oTO6qC6_CMPG0m8nNqSFWrFRBbsTPQza
passed (exit 0, 16.285 seconds; module build 4.9 seconds). All six inspected
declarations use only propext, Classical.choice, and Quot.sound.
The explicit geometric tail-rate inequality stated earlier in this note is
still not formalized; neither finite-precision interval evaluation nor a
numerical saturation certificate is supplied by this module. All full
ambient/legal Parseval residuals remain present. Higher Meixner completeness
and actual F_2/F_3 legal Parseval saturation and membership remain open.
