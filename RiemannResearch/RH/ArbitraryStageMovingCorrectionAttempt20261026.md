# Arbitrary-stage moving-correction bound: attempted proof and remaining obstruction

Date: 2026-10-26. Source: the user's request to prove the expanding-head bound, and independent calculations in this investigation. No priority or novelty claim is made.

## Status

The requested estimate

\[
\exists C\ge0\quad\forall N\quad\forall 1\le n\le N,
\qquad |b_N(n)|\le C
\]

has **not been proved**. The existing theorem `QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound` remains a conditional reduction. Neither residual vanishing nor RH follows from the findings below alone.

This document records an ordinary proof of square-summable Hilbert increments, the exact signed induction obstruction, a counterexample to a purely Hilbert-space argument, and a larger exploratory computation. No new Lean declaration or Lean verification is claimed. See `FiniteMovingCorrectionInvestigation20261025.md` for the prior complete-tail computations and exact rational finite certificates.

The repository's stage N uses conductors 2 through N+1, with nonsquarefree atoms masked to zero. We use D=N+1 for numerical cutoffs. All formulas below refer to the actual infinite weighted Hilbert space, not a truncated inner product, unless explicitly marked exploratory.

## Exact stage update

Delete unchanged stages and label the active flag by j. Thus
\(V_j=V_{j-1}\oplus\mathbb R v_j\), where \(v_j\) is a unit vector orthogonal to \(V_{j-1}\). Write \(P_j=P_{V_j}^Q\), \(r_j=1-P_j1\), and \(b_j=P_jBr_j\).

Define

\[
a_j=\langle r_{j-1},v_j\rangle_Q,
\quad t_j=P_{j-1}Bv_j,
\quad \nu_j=\langle v_j,Bv_j\rangle_Q,
\quad q_j=(I-P_j)Bv_j.
\]

These give the exact orthogonal decompositions

\[
r_{j-1}=a_jv_j+r_j,
\qquad Bv_j=t_j+\nu_jv_j+q_j.
\]

Since B is self-adjoint and \(r_j\perp V_j\), put

\[
h_j=\langle v_j,Br_j\rangle_Q=\langle q_j,r_j\rangle_Q.
\]

Expanding \(P_j=P_{j-1}+v_j\otimes v_j\) gives the signed identity

\[
\boxed{b_j-b_{j-1}=-a_jt_j+h_jv_j.}
\]

Consequently

\[
\boxed{\|b_j-b_{j-1}\|_Q^2=a_j^2\|t_j\|_Q^2+h_j^2.}
\]

No crossing term is dropped: it is zero because \(t_j\perp v_j\). The residual-energy identity is

\[
a_j^2+\|r_j\|_Q^2=\|r_{j-1}\|_Q^2\le\|1\|_Q^2=1.
\]

The term \(h_jv_j(n)\), including its sign and its moving-coordinate evaluation, is not controlled by telescoping the energy drops \(a_j^2\). This is the obstruction to the proposed induction.

## Unconditional square-summable variation

For completeness, the exact remainder before the estimate is

\[
\begin{aligned}
\|Bv_j\|_Q^2-\nu_j^2-\|b_j-b_{j-1}\|_Q^2
={}&(1-a_j^2)\|t_j\|_Q^2
 +(1-\|r_j\|_Q^2)\|q_j\|_Q^2\\
&+\bigl(\|r_j\|_Q^2\|q_j\|_Q^2-h_j^2\bigr).
\end{aligned}
\]

All three displayed terms are nonnegative, the last by Cauchy--Schwarz. Hence

\[
\|b_j-b_{j-1}\|_Q^2+\nu_j^2\le\|Bv_j\|_Q^2.
\]

Let \(e_n=Q(n)^{-1/2}\mathbf 1_{\{n\}}\) be the orthonormal coordinate basis. The active innovations are orthonormal, and \(Be_n=(n+1)^{-1}e_n\). Therefore, for every finite J,

\[
\begin{aligned}
\sum_{j\le J}\|Bv_j\|_Q^2
 &=\sum_{n\ge1}\frac1{(n+1)^2}
       \sum_{j\le J}|\langle e_n,v_j\rangle_Q|^2\\
 &\le\sum_{n\ge1}\frac1{(n+1)^2}
 =\zeta(2)-1.
\end{aligned}
\]

Only nonnegative sums are interchanged; the inequality is Bessel's. Passing to the monotone limit proves

\[
\boxed{\sum_{j\ge1}\|b_j-b_{j-1}\|_Q^2
       +\sum_{j\ge1}\nu_j^2\le\zeta(2)-1.}
\]

Unchanged masked stages contribute zero increments. In the original stage indexing this in particular yields

\[
\sum_{N\ge0}\|b_{N+1}-b_N\|_Q^2\le\zeta(2)-1.
\]

This ordinary proof requires no RH assumption and no prior convergence theorem. The constant is not asserted optimal. It does not imply bounded physical heads. Coordinate evaluation yields only

\[
\sum_{N\ge0}|b_{N+1}(n)-b_N(n)|^2
\le\zeta(2)n^2(\zeta(2)-1),
\]

and square summability does not give absolute summability of increments.

The existing centered-multiplier argument gives another unconditional estimate, already formalized in `QShiftedReciprocalBounds.lean`:

\[
\|b_N\|_Q\le\frac14\|r_N\|_Q,
\qquad |b_N(n)|\le\frac{\sqrt{\zeta(2)}\,n}{4}\|r_N\|_Q.
\]

The factor n is precisely why this is not the requested uniform estimate.

## Explicit obstruction to a generic projection proof

This example uses the same Q, B, and target 1, but **different subspaces**, so it is not a counterexample to the squarefree head conjecture.

Let \(w(n)=\log n-1/100\) and

\[
U_N=\{f:\operatorname{supp}f\subseteq\{1,\ldots,N\},\ \langle f,w\rangle_Q=0\}.
\]

These are nested finite-dimensional spaces. They have nonnegative bounded generating atoms: for each j>=2 use

\[
u_j=\mathbf1_{\{j\}}+
 \frac{Q(j)w(j)}{-Q(1)w(1)}\mathbf1_{\{1\}},
\]

and rescale each atom by its positive maximum to put its values in [0,1]. The atoms span \(U_N\) for j<=N. They are not the periodic residue atoms.

Set

\[
A_N=\sum_{n\le N}Q(n)w(n),\quad
T_N=\sum_{n\le N}Q(n)w(n)^2,\quad
M_N=\sum_{n\le N}Q(n)\frac{w(n)^2}{n+1}.
\]

All three sums converge. Their limits satisfy T>0, M>0, and A>0. For the last assertion,

\[
A\ge\frac{\log2}{4\zeta(2)}-\frac1{100}
>\frac1{16}-\frac1{100}>0,
\]

using \(\log2>1/2\) and \(\zeta(2)<2\).

The residual of projecting 1 onto \(U_N\) equals \((A_N/T_N)w(n)\) for n<=N and equals 1 for n>N. Thus its actual moving correction is, exactly,

\[
\widetilde b_N(n)=\frac{A_N}{T_N}
 \left(\frac1{n+1}-\frac{M_N}{T_N}\right)w(n),\qquad n\le N.
\]

At the moving coordinate n=N,

\[
\widetilde b_N(N)\sim-\frac{AM}{T^2}\log N\longrightarrow-\infty.
\]

Projection convergence, a positive compact reciprocal multiplier, bounded nonnegative dictionary atoms, the centered norm bound, the variance estimate, and square-summable Hilbert increments all hold in this example. They cannot alone prove a uniform head bound. The actual squarefree arithmetic must enter essentially.

## What the arithmetic step would have to control

Use an independent active basis (or the quotient by the synthesis kernel). For a new atom g_d set

\[
k_e=\langle g_e,g_d\rangle_Q,\quad
\kappa=G_{\mathrm{prev}}^{-1}k,\quad
\sigma_d^2=G_{dd}-k^\top G_{\mathrm{prev}}^{-1}k.
\]

When \(\sigma_d>0\),

\[
v_d=\sigma_d^{-1}\left(g_d-\sum_e\kappa_e g_e\right).
\]

If the atom is redundant, the span and b are unchanged; no inverse of the singular masked Gram matrix is used. A proof using the update identity must control the signed reciprocal cross moments together with \(\sigma_d^{-1}\) and the physical values of this innovation. The energy decrease by itself supplies no such bound.

A second exact formulation perturbs the metric:

\[
Q_t(n)=Q(n)\left(1-\frac{t}{n+1}\right),\quad |t|<2.
\]

On the independent synthesis quotient, G-tH is positive definite, and

\[
c(t)=(G-tH)^{-1}(m-th),\qquad
c'(0)=-G^{-1}(h-Hc)=-\alpha.
\]

Hence \(b_N=-\partial_tF_{N,t}|_{t=0}\). This identity preserves the entire signed source. Analytic Hilbert control of the metric derivative does not establish a uniform bound on its physical coordinates.

A positivity shortcut also fails for the actual dictionary. The previously certified D=96 coefficient enclosure gives

\[
F_{95}(95)\in[-0.450999081,-0.450999079].
\]

It is obtained by evaluating the rational coefficient candidate and adding the certified coefficient-error bound times \(\sum_d g_d(95)\). Thus projection sends the positive constant 1 to a negative head value. This refutes order preservation of that projection; it does not refute the desired b bound.

## Larger exploratory computation

The rigorous certificate remains

\[
\max_{1\le N\le127,\ 1\le n\le N}|b_N(n)|<0.060626<1/16,
\]

as documented in the previous investigation. No rigorous assertion about all larger stages is inferred from it.

## Method and status

We tested every conductor cutoff D=257,...,1024, corresponding to repository stages N=256,...,1023, using 623 nonzero squarefree atoms at the largest stage. Matrices use the unnormalized n^-2 weight, which leaves the projection coefficients unchanged. All signed terms in h-Hc are retained.

The existing complete D=256 Gram/H prefix is reused. For new entries we sum through T, then approximate the infinite tail by its exact periodic mean. For a,b and L=lcm(a,b),

mu_ab = (a-1)(b-1)/(4ab) + (gcd(a,b)^2-1)/(12ab).

The added Gram tail is mu_ab psi_1(T+1); the added H tail is mu_ab [psi_1(T+1)-1/(T+1)]. The m,h vectors still use their complete period special-function formulas.

This is an exploratory approximation, not a certified head bound. The analytic omitted oscillatory tails satisfy

|Delta G_ab| <= L mu_ab(1-mu_ab)/(T+1)^2,

|Delta H_ab| <= L mu_ab(1-mu_ab)/[(T+1)^2(T+2)].

Indeed, a periodic sequence p in [0,1] with period L and mean mu has every partial centered sum bounded in absolute value by L mu(1-mu); summation by parts against the positive decreasing weight gives the displayed inequalities. These bounds do not include floating-roundoff errors and are too coarse, given the Gram conditioning, to certify the largest physical heads directly.

We independently ran T=1,000,000 and T=4,000,000. The larger matrix took 68.6 seconds to assemble; the full stage scan took a few additional seconds. The maximum change in a head maximum between the two runs was 0.000003515902, at D=663. Stability across these two truncations is evidence, not a rigorous error estimate.

## Results at T=4,000,000

| D | N | atoms | max over 1<=n<=N | maximizing n | alpha l1 | cancellation ratio | Gram condition |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 512 | 511 | 313 | 0.03882065015 | 221 | 2.154804 | 0.00248125 | 407234 |
| 666 | 665 | 405 | 0.05997050586 | 665 | 2.589448 | 0.00232695 | 702068 |
| 1024 | 1023 | 623 | 0.04755742304 | 554 | 3.501152 | 0.00217524 | 1645255 |

The cancellation ratio is ||h-Hc||_2/(||h||_2+||Hc||_2).

No tested new stage exceeded 1/16=0.0625. The largest new value was approximately 0.05997050586 at N=665, n=665. Combining this exploratory scan with the earlier finite computations, the largest observed value through N=1023 remains approximately 0.06049032459 at N=95. The rigorous certificate remains only the previously established finite range N<=127; this follow-up does not enlarge that certified range.

The growing coefficient l1 norm, already approximately 3.50115 at N=1023, continues to favor investigating physical head cancellation directly rather than guessing a small universal coefficient-l1 bound. No stage-independent physical-head inequality, residual-vanishing result, or RH proof is obtained here.

## Reproduction

Run with NumPy and SciPy, using the previous numerical_correction_full.npz as the complete D256 prefix:

1. OPENBLAS_NUM_THREADS=2 python arbitrary_stage_search.py 1024 1000000
2. OPENBLAS_NUM_THREADS=2 python arbitrary_stage_search.py 1024 4000000
3. OPENBLAS_NUM_THREADS=2 python arbitrary_stage_compare.py

Outputs are arbitrary_stage_* files only. Summary: arbitrary_stage_comparison.json. Full stage rows: arbitrary_stage_all_D1024_T1000000.json and arbitrary_stage_all_D1024_T4000000.json.

## Reproducible exploratory source

The prerequisite D=256 complete-period prefix is generated by the source in `FiniteMovingCorrectionInvestigation20261025.md`. The scripts below are not interval or exact-arithmetic certificates.

### arbitrary_stage_search.py

```python
"""Exploratory larger-stage head plus exact periodic-mean tail systems.
The tail mean is an approximation, not an exact Gram entry/certificate.
Repeated T diagnostics assess stability; a claimed counterexample needs enclosure.
"""
from pathlib import Path
import time,math,json,sys
import numpy as np
from scipy.special import polygamma,digamma
from scipy.linalg import solve,eigvalsh
BASE=Path(__file__).resolve().parent
Dmax=int(sys.argv[1]) if len(sys.argv)>1 else 1024
T=int(sys.argv[2]) if len(sys.argv)>2 else 1000000
squarefree=lambda n: all(n%(p*p) for p in range(2,math.isqrt(n)+1))
ds=np.array([d for d in range(2,Dmax+1) if squarefree(d)],dtype=np.int64);q=len(ds)
t0=time.time();G=np.zeros((q,q));H=np.zeros((q,q));m=np.zeros(q);h=np.zeros(q)
# m,h use exact complete period formulas, floating special-function evaluation.
for i,a in enumerate(ds):
 n=np.arange(1,a+1,dtype=float);v=(n%a)/a;w2=polygamma(1,n/a)/a**2;wb=w2+(digamma(n/a)-digamma((n+1)/a))/a
 m[i]=v@w2;h[i]=v@wb
for start in range(1,T+1,8192):
 n=np.arange(start,min(start+8192,T+1),dtype=np.int64);A=(n[:,None]%ds)/ds
 W=A/n[:,None];G+=W.T@W
 W/=np.sqrt(n+1)[:,None];H+=W.T@W
 if start==1:print('first block seconds',time.time()-t0,'q',q,flush=True)
a=ds[:,None];b=ds[None,:];gd=np.gcd(a,b)
means=((a-1)*(b-1))/(4*a*b)+(gd*gd-1)/(12*a*b)
tail2=float(polygamma(1,T+1));tailB=tail2-1/(T+1)
G+=means*tail2;H+=means*tailB
# Keep available complete pairwise period prefix exactly as previously evaluated.
z=np.load(BASE/'numerical_correction_full.npz');oldq=int(np.sum(ds<=int(z['maximum_cutoff'])))
G[:oldq,:oldq]=z['G'][:oldq,:oldq];H[:oldq,:oldq]=z['H'][:oldq,:oldq]
print('matrix seconds',time.time()-t0,flush=True)
np.savez(BASE/f'arbitrary_stage_approx_D{Dmax}_T{T}.npz',ds=ds,G=G,H=H,m=m,h=h,cutoff=Dmax,T=T)
outs=[]
for D in range(257,Dmax+1):
 if D%4 and D not in [512,1024]:continue
 k=int(np.sum(ds<=D));d=ds[:k];g=G[:k,:k];c=solve(g,m[:k],assume_a='pos');rhs=h[:k]-H[:k,:k]@c;al=solve(g,rhs,assume_a='pos')
 ns=np.arange(1,D);bb=((ns[:,None]%d)/d)@al;mx=float(max(abs(bb)))
 outs.append(dict(D=D,N=D-1,head_max=mx,argmax=int(np.argmax(abs(bb))+1),alpha_l1=float(sum(abs(al))),c_l1=float(sum(abs(c)))))
print('elapsed',time.time()-t0,'top10',sorted(outs,key=lambda r:r['head_max'],reverse=True)[:10],flush=True)
with (BASE/f'arbitrary_stage_search_D{Dmax}_T{T}.json').open('w') as f:json.dump(outs,f,indent=2)
```

### arbitrary_stage_compare.py

```python
"""Compare larger-stage exploratory periodic-mean tail approximations."""
import json,math,time
from pathlib import Path
import numpy as np
from scipy.linalg import solve,eigvalsh
BASE=Path(__file__).resolve().parent
outs=[];diagnostics=[]
for T in [1000000,4000000]:
 z=np.load(BASE/f'arbitrary_stage_approx_D1024_T{T}.npz');ds=z['ds'];G=z['G'];H=z['H'];m=z['m'];h=z['h'];rows=[]
 for D in range(257,1025):
  q=int(np.sum(ds<=D));d=ds[:q];g=G[:q,:q];c=solve(g,m[:q],assume_a='pos');rhs=h[:q]-H[:q,:q]@c;a=solve(g,rhs,assume_a='pos');n=np.arange(1,D);bb=((n[:,None]%d)/d)@a
  rows.append(dict(D=D,N=D-1,head_max=float(max(abs(bb))),argmax=int(np.argmax(abs(bb))+1)))
  if T==4000000 and D in [512,666,1024]:
   ev=eigvalsh(g);hh=h[:q];hc=H[:q,:q]@c
   diagnostics.append(dict(D=D,N=D-1,dimension=q,head_max=rows[-1]['head_max'],argmax=rows[-1]['argmax'],alpha_l1=float(sum(abs(a))),cancellation_ratio=float(np.linalg.norm(rhs)/(np.linalg.norm(hh)+np.linalg.norm(hc))),condition=float(ev[-1]/ev[0]),residual_norm2=float(1-m[:q]@c/(math.pi**2/6))))
 with (BASE/f'arbitrary_stage_all_D1024_T{T}.json').open('w') as f:json.dump(rows,f,indent=2)
 outs.append(rows)
diffs=[abs(a['head_max']-b['head_max']) for a,b in zip(*outs)]
summary=dict(maximum_stage=1023,largest_new_stage=max(outs[1],key=lambda r:r['head_max']),maximum_headmax_change=max(diffs),D_of_max_change=outs[1][int(np.argmax(diffs))]['D'],all_new_heads_below_one_sixteenth=all(r['head_max']<1/16 for r in outs[1]),diagnostics=diagnostics,rigor='Exploratory floating approximation; not a certified physical-head inequality.')
with (BASE/'arbitrary_stage_comparison.json').open('w') as f:json.dump(summary,f,indent=2)
print(json.dumps(summary,indent=2))
```

## Conclusion

The strongest additional unconditional statement proved here is square-summable Hilbert variation, with the full signed update and nonnegative remainder recorded above. This is an ordinary mathematical proof, not a new Lean-checked theorem. The arbitrary-stage physical-head estimate remains open in this investigation.
