# Audit of the remaining complete-Q closure step

**Date:** 23 October 2026.
**Outcome:** the remaining step was not proved. No unconditional arithmetic provider was found.
**Status:** ordinary mathematical arguments and an exact rational computational
certificate; no new Lean theorem or proof of RH is claimed.

The starting verified development is
[commit 5b9d798](https://github.com/Cnoack3/RiemannResearch/commit/5b9d79826d62d66225efda4c63c595ce537eea34).
Its optimal-energy and harmonic-rigidity conclusions remain valid.

## 1. The open arithmetic statement

Let \(Q(n)=1/(Zn^2)\), \(Z=\zeta(2)\), and let \(V\) be the closed full residue
span. With \(r=1-P_V1\), the verified routes would close upon proving bounded
optimal energies, finiteness of either harmonic sign series of \(r\), or the
stated cofinal bound on its logarithmically scaled tails. All these providers
remain **Open**.

The verified theorem QOptimalExactHead.qOne_mem_iff_energy_bounded explicitly
makes bounded energy equivalent to the missing target membership.
Monotone energies, positive definite finite matrices, exact finite-head repair,
and orthogonal innovations do not by themselves prove boundedness.

The existing positive majorant also does not control harmonic sign mass:
\[
B(n)=4\sum_{k\ge0}g_{4^{k+1}}(n)=\frac43s_4(n),
\]
where \(s_4(n)\) is the base-four digit sum. In particular \(B(4^j)=4/3\).
Pairing with this legal vector weights signs by \(B(n)/n^2\), not by \(1/n\).
Any vector eventually dominating \(cn\), \(c>0\), would itself fail to belong
to \(L^2(Q)\).

## 2. A comparison space with divergent optimal energies

This is a comparison subspace \(W\), not the arithmetic residue span.

Define
\[
h(n)=
\begin{cases}
-2^k/k,&n=2^k,\ k\ge2,\\
1,&\text{otherwise},
\end{cases}
\qquad W=h^\perp\subset L^2(Q).
\]
Then
\[
H=\|h\|_Q^2
=1+\frac1Z\sum_{k\ge2}(k^{-2}-4^{-k})>1
\]
and
\[
c=\langle1,h\rangle_Q
=1-\frac1Z\sum_{k\ge2}(4^{-k}+1/(k2^k))>0.
\]
The subtracted sum is at most \(1/12+1/4=1/3<Z\).
Thus \(h\in L^2(Q)\), but \(1\notin W\).

Every finite head is realizable by a finitely supported vector in \(W\):
choose one later coordinate and correct its pairing with \(h\).
Finite supported vectors of \(W\) are dense in \(W\), by truncation and a
correction at one fixed coordinate. A prescribed initial head is preserved by
choosing that correction coordinate beyond it.

There is a fixed bounded positive majorant:
\[
B=1+8Zc\,\mathbf1_{\{4\}}\in W,\qquad B\ge1,
\]
because \(Q(4)h(4)=-1/(8Z)\).
The actual residual for this comparison space is
\[
r_W=(I-P_W)1=\frac cHh.
\]
Even \(P_W1>0\) pointwise, since \(0<c/H<1\). Both harmonic signs of \(r_W\)
diverge: the positive part contains the harmonic series with powers of two
removed, while the negative part at \(2^k\) contributes \((c/H)/k\).

Set
\[
m_M=\sum_{n\le M}Q(n),\quad
c_M=\sum_{n\le M}Q(n)h(n),\quad
\tau_M=\sum_{n>M}Q(n)h(n)^2.
\]
The exact minimizer over \(W\) is
\[
f_M=\mathbf1_{\{n\le M\}}-\frac{c_M}{\tau_M}h\mathbf1_{\{n>M\}},
\qquad
\boxed{\mathcal E_M(W)=m_M+\frac{c_M^2}{\tau_M}}.
\]
Indeed every feasible tail \(v\) satisfies
\(\langle v,h\mathbf1_{\{n>M\}}\rangle=-c_M\), so Cauchy--Schwarz gives
\(\|v\|^2\ge c_M^2/\tau_M\), attained by the displayed vector.
The head and tail have disjoint support, so their squared norms add exactly.

For \(M\ge4\) and \(K=\lfloor\log_2M\rfloor\),
\[
\tau_M=\frac1Z\sum_{n>M}n^{-2}
+\frac1Z\sum_{k>K}(k^{-2}-4^{-k})
\sim\frac{\log2}{Z\log M}.
\]
Since \(c_M\to c>0\),
\[
\boxed{\mathcal E_M(W)\sim\frac{Zc^2}{\log2}\log M\longrightarrow\infty}.
\]
This satisfies every existing fixed-logarithmic saving and the stretched
sublinear upper allowance. It also has the corresponding tail-escape
properties. These estimates are compatible, not contradictory.
The example does not assert residue orthogonality; that arithmetic information
must do additional work.

## 3. Why positivity cannot be assumed

If the actual \(P_V\) preserved coordinatewise nonnegativity, there would be a
valid closure argument. For \(f\in V\), positivity gives \(|f|\le P_V|f|\).
Contractivity forces equality, hence \(|f|\in V\), and \(V\) is a vector lattice.
One could then clip an exact head \(E_M\) against a bounded nonnegative legal
majorant:
\[
F_M=E_M^+\wedge B_{M+1}\in V,\qquad
F_M=1\text{ on the head},\qquad
0\le F_M\le B_{M+1}.
\]
The uniform majorant norm would give bounded optimal energies.
**The required order-preservation property remains Open.**

It does not follow merely from positive residue generators or positive
definite Gram matrices. For the genuine complete-\(Q\) projection \(p\) of 1
onto \(\operatorname{span}(g_2,\ldots,g_{12})\), the exact rational certificate
below proves
\[
\boxed{p(9856)<-\tfrac1{10},\qquad p(17863)>\tfrac{21}{10}}.
\]
The common factor \(1/Z\) cancels from the normal equations. Infinite periodic
tails are bounded by integrals; this is not a truncated Gram computation.
Independent 70-digit Wolfram evaluation gave approximately
\(-0.15404951142518285874\) and \(2.14599585309502712366\).

This finite example does not refute order preservation of the infinite
projection. It shows that the suggested finite-projection argument fails.

## 4. Dilation identities do not provide a tail upper bound

With \(S_df(n)=f(\lfloor n/d\rfloor)\), \(f(0)=0\), the actual residual obeys
\[
A_d:=\langle S_d1,r\rangle_Q=\langle S_dr,r\rangle_Q,
\qquad Q(n)r(n)=A_n-A_{n+1},
\]
because \(S_d(1-r)\in V\). Dilation norm control and support localization give
\[
|A_d|^2\le\frac{\|r\|_Q^2}{d}\tau_{d-1}(r).
\]
This estimates correlations from tails, not tails from above.

A generic contraction for the quadratic reconstruction is false.
Let \(f_N\) have normalized coordinates \(N^{-1/2}\) at physical indices
\(2^j\), \(1\le j\le N\), and zero elsewhere. Then \(\|f_N\|=1\).
Writing \(C_d=\langle S_df_N,f_N\rangle\), for \(2\le k\le N-1\),
\[
C_{2^k}=\frac{N-k}{N2^k},\qquad C_{2^k+1}=0.
\]
For \(B(f,f)(n)=Zn^2(C_n-C_{n+1})\), therefore,
\[
\|B(f_N,f_N)\|_Q^2\ge
\frac Z{N^2}\sum_{j=1}^{N-2}j^2\sim\frac{ZN}{3}.
\]
No universal estimate \(\|B(f,f)\|\le C\|f\|^2\) is available.

The primary reference
[Manzur--Noor, arXiv:2610.03568v1](https://arxiv.org/html/2610.03568v1)
also requires an additional invariant-subspace property.
The established floor-dilation invariance is not that property, and no
unproved transfer of its Hardy-space operators to complete \(Q\) was used.

## 5. Verification status

These arguments are ordinary mathematics, not newly Lean-checked declarations.
The rational certificate below was executed successfully. Its rounded diagnostic
intervals were approximately
\[
p(9856)\in[-0.154429982124,-0.153669040726],\quad
p(17863)\in[2.145615382396,2.146376323794].
\]
Only the exact rational inequalities in the code are certificate conclusions.

This publication is documentation only. No unconditional RH provider or new
Lean theorem is claimed, and no new hypothesis was hidden inside a claimed proof.

## Appendix: reproducible complete-tail rational certificate

For a residue class of period \(L\), let \(x=r+JL\). The tail bounds are
\[
\frac1{Lx}\le\sum_{j\ge J}(r+jL)^{-2}\le x^{-2}+\frac1{Lx}.
\]
The first 11 physical rows give a positive definite rational Gram lower bound
\(B\). Since \(H\ge B>0\), \(\|H^{-1}\|\le\operatorname{tr}(B^{-1})\).
The code combines this with exact residual intervals.

```python
"""Exact rational certificate that a finite complete-Q projection is not positive.

This is finite computational verification, not a Lean theorem. No floating-point
quantity enters the final certificate. The common zeta(2) normalization cancels
from the normal equations. The infinite tails use decreasing-function integral
bounds for each residue class.
"""
from fractions import Fraction as F
from math import lcm

DS = list(range(2, 13))
M = len(DS)
SCALE = 10**20
CSCALE = 10**18
BLOCKS = 2000
C = [956771111665429255, 922085774549003980, 121325095442925884,
     764622094925932860, -541818876990524989, 567916287328269278,
     29466882659386647, 100107098444551177, -454308785618765400,
     475259241032277680, 25016969499865034]

def ceildiv(a, b):
    return -((-a)//b)

def periodic_interval(period, numerators, denominator):
    lo = hi = 0
    for r, num in enumerate(numerators, start=1):
        if not num:
            continue
        subtotal = sum(SCALE*num // (denominator*(r+j*period)**2)
                       for j in range(BLOCKS))
        x = r + BLOCKS*period
        integral = SCALE*num // (denominator*period*x)
        extra = ceildiv(SCALE*num, denominator*x*x)
        lo += subtotal + integral
        hi += subtotal + BLOCKS + integral + 1 + extra
    return lo, hi

H = [[None]*M for _ in DS]
b = []
for i, d in enumerate(DS):
    b.append(periodic_interval(d, [r%d for r in range(1, d+1)], d))
    for j, e in enumerate(DS[:i+1]):
        L = lcm(d, e)
        H[i][j] = H[j][i] = periodic_interval(
            L, [(r%d)*(r%e) for r in range(1, L+1)], d*e)

# The first M physical rows give a rational positive-definite lower bound B.
A = [[F(n%d, d) for d in DS] for n in range(1, M+1)]
B = [[sum(A[n-1][i]*A[n-1][j]/(n*n) for n in range(1, M+1))
      for j in range(M)] for i in range(M)]
aug = [B[i][:] + [F(int(i==j)) for j in range(M)] for i in range(M)]
for i in range(M):
    pivot = next(k for k in range(i, M) if aug[k][i])
    aug[i], aug[pivot] = aug[pivot], aug[i]
    z = aug[i][i]
    aug[i] = [x/z for x in aug[i]]
    for k in range(M):
        if k != i:
            z = aug[k][i]
            aug[k] = [x-z*y for x,y in zip(aug[k], aug[i])]
assert all(aug[i][j] == int(i==j) for i in range(M) for j in range(M))
trace_inverse = sum(aug[i][M+i] for i in range(M))

# Every component of H*c-b lies in [e_lo,e_hi]/(SCALE*CSCALE).
max_residual_num = 0
for i in range(M):
    e_lo = sum(H[i][j][0 if C[j]>=0 else 1]*C[j] for j in range(M)) - b[i][1]*CSCALE
    e_hi = sum(H[i][j][1 if C[j]>=0 else 0]*C[j] for j in range(M)) - b[i][0]*CSCALE
    max_residual_num = max(max_residual_num, abs(e_lo), abs(e_hi))
max_residual = F(max_residual_num, SCALE*CSCALE)

# H >= B > 0, hence ||H^-1|| <= tr(B^-1). Both the evaluation row and
# the residual vector have Euclidean norm <= sqrt(M) times their max norm.
evaluation_error = M*trace_inverse*max_residual
def candidate_value(n):
    return sum(F(n%d, d)*F(c, CSCALE) for d,c in zip(DS,C))

negative_site = 9856
large_site = 17863
negative_upper = candidate_value(negative_site) + evaluation_error
large_lower = candidate_value(large_site) - evaluation_error
assert negative_upper < F(-1, 10)
assert large_lower > F(21, 10)

print('All certificate inequalities verified with exact rational arithmetic.')
print('Dictionary:', DS)
print('trace(B^-1) =', trace_inverse)
print('max residual upper bound < 1/1000000:', max_residual < F(1, 1000000))
print('evaluation error < 1/100:', evaluation_error < F(1, 100))
print('p(9856) < -1/10:', negative_upper < F(-1, 10))
print('p(17863) > 21/10:', large_lower > F(21, 10))
print('Diagnostic decimal interval at 9856:',
      float(candidate_value(negative_site)-evaluation_error), float(negative_upper))
print('Diagnostic decimal interval at 17863:',
      float(large_lower), float(candidate_value(large_site)+evaluation_error))
```
