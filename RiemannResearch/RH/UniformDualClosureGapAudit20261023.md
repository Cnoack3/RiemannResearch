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

## 4.1 Signed averaging of optimal heads

The following is an ordinary Hilbert-space calculation from the existing
`QOptimalExactHead.optimizer_inner_later` and `energy_increment` identities,
not a new Lean-checked declaration.

Write \(u_M\) for the actual optimal exact head and \(E_M=\|u_M\|_Q^2\).
For \(M_1<\cdots<M_k\) and real \(a_i\) with \(\sum_i a_i=1\),
\[
\boxed{
\left\|\sum_{i=1}^k a_i u_{M_i}\right\|_Q^2
=E_{M_1}+
\sum_{j=1}^{k-1}
\left(\sum_{i=j+1}^k a_i\right)^2
(E_{M_{j+1}}-E_{M_j}).
}
\]
Indeed write the linear combination as
\(u_{M_1}+\sum_{j<k}(\sum_{i>j}a_i)(u_{M_{j+1}}-u_{M_j})\).
The increments are pairwise orthogonal and orthogonal to \(u_{M_1}\);
their squared norms are the displayed energy differences.
Thus even signed averaging of later optimal heads cannot improve on the earliest
optimal energy. Averaging nonoptimal heads can help, but its gain depends on
signed cross terms not controlled by individual norm upper bounds.

## 4.2 A dilation-invariant comparison space with polynomial cost

**Status: ordinary mathematics; this comparison has not been formalized or
verified in Lean.** The argument uses the physical step-function Mellin transform
appearing in `QMellinTransfer.lean` and elementary Hilbert-space minimization.
No novelty claim is made.

Fix \(s=\beta+i\gamma\), \(1/2<\beta<1\), \(\gamma\ne0\), without assuming
that \(s\) is a zeta zero. Work in the real Hilbert space \(L^2(Q)\). Set
\[
a_n=\int_n^{n+1}x^{-s-1}\,dx
=\frac{n^{-s}-(n+1)^{-s}}s,\qquad
L_s(f)=\sum_{n\ge1}f(n)a_n,\qquad W_s=\ker L_s.
\]
This is a real-linear map into \(\mathbb C\simeq\mathbb R^2\).
Since \(a_n=n^{-s-1}(1+O_s(n^{-1}))\),
\[
\sum_{n\ge1}\frac{|a_n|^2}{Q(n)}<\infty.
\]
Cauchy--Schwarz therefore makes \(L_s\) continuous and its defining series
absolutely convergent for every \(f\in L^2(Q)\). In particular \(W_s\) is closed.
Telescoping gives \(L_s(1)=1/s\ne0\), so \(1\notin W_s\).

For every positive integer \(d\), define \(S_df(n)=f(\lfloor n/d\rfloor)\),
with \(f(0)=0\). Directly,
\[
\|S_df\|_Q^2
=\frac1Z\sum_{k\ge1}|f(k)|^2
  \sum_{n=dk}^{dk+d-1}n^{-2}
\le\frac1d\|f\|_Q^2.
\]
For the physical step-function extension \(\widetilde f(x)=f(\lfloor x\rfloor)\),
including zero below 1, substitution \(x=dy\) gives the exact identity
\[
L_s(S_df)=\int_1^\infty \widetilde f(x/d)x^{-s-1}\,dx
=d^{-s}L_s(f).
\]
Thus \(W_s\) is invariant under every established floor dilation.

The phases of \(a_n\) approach \(-\gamma\log n\) modulo \(2\pi\).
Every open arc of the unit circle contains phases from arbitrarily late
coordinates: round an exponential sequence whose logarithmic phases approach
the desired angle. Consequently, beyond any finite head there are two
real-linearly independent \(a_n\). Corrections at those coordinates repair
the Mellin value of any prescribed finite head. This also proves that \(L_s\)
has real rank two.

There is even a bounded positive majorant in \(W_s\).
Choose three late \(a_{n_j}\) whose phases are close to three equally spaced
points of the unit circle. Their positive cone is all of \(\mathbb C\).
Hence there exist \(t_j\ge0\) with \(\sum_jt_ja_{n_j}=-1/s\), and
\[
B=1+\sum_{j=1}^3 t_j\mathbf1_{\{n_j\}}\in W_s,\qquad B\ge1.
\]
The finitely many coefficients make \(B\) bounded and square-integrable.

Here is the complete exact constrained energy, including its infinite tail.
The minimum is over all vectors of \(W_s\) with the prescribed head.
Let
\[
v_n=(\Re a_n,\Im a_n)^{\mathsf T},\quad
b_M=\sum_{n\le M}v_n,\quad
G_M=Z\sum_{n>M}n^2v_nv_n^{\mathsf T},\quad
m_M=\sum_{n\le M}Q(n).
\]
Every \(G_M\) is positive definite by the late-coordinate independence.
The minimizing tail subject to \(\sum_{n>M}f(n)v_n=-b_M\) is
\[
f_M(n)=-Zn^2v_n^{\mathsf T}G_M^{-1}b_M\quad(n>M).
\]
It belongs to \(L^2(Q)\) because the two dual vectors do.
Taking \(f_M(n)=1\) on the head yields
\[
\boxed{\mathcal E_M(W_s)=m_M+b_M^{\mathsf T}G_M^{-1}b_M.}
\]
To check optimality, every other feasible tail differs from this tail by an
element of the tail map's kernel, orthogonal to the displayed minimizing tail.
Pythagoras gives its energy plus the exact nonnegative squared difference.
If competitors are required to have finite support, the same value is an
infimum, not generally an attained minimum. To see equality of the infima,
truncate the minimizing vector and repair its vanishing Mellin error at two
fixed independent coordinates beyond the head; the repairs tend to zero in norm.

Put \(\alpha=2\beta-1\in(0,1)\), and define
\[
A_M=Z\sum_{n>M}n^2|a_n|^2,\qquad
C_M=Z\sum_{n>M}n^2a_n^2.
\]
Then, exactly,
\[
G_M=\frac12
\begin{pmatrix}
A_M+\Re C_M&\Im C_M\\
\Im C_M&A_M-\Re C_M
\end{pmatrix},
\qquad \lambda_\pm(G_M)=\frac{A_M\pm|C_M|}{2}.
\]
Integral comparison with a derivative remainder for the complex power series
and the expansion of \(a_n\) give
\[
A_M=\frac Z\alpha M^{-\alpha}+O_s(M^{-\alpha-1}),\qquad
C_M=\frac Z{\alpha+2i\gamma}M^{-\alpha-2i\gamma}
       +O_s(M^{-\alpha-1}).
\]
Thus
\[
\lambda_\pm(G_M)\sim
\frac Z2\left(\frac1\alpha
\pm\frac1{\sqrt{\alpha^2+4\gamma^2}}\right)M^{-\alpha}.
\]
Both constants are strictly positive. Since
\(b_M=(\Re((1-(M+1)^{-s})/s),\Im((1-(M+1)^{-s})/s))^{\mathsf T}\)
tends to a nonzero vector, the exact minimum satisfies
\[
\boxed{\mathcal E_M(W_s)=\Theta_s(M^\alpha).}
\]
A single asymptotic constant for \(\mathcal E_M/M^\alpha\) is not asserted;
the Gram eigendirections rotate with \(\log M\).

For every fixed logarithmic power, these energies are eventually smaller
than the corresponding \(M/(\log M)^k\) allowance. They are also smaller
than the current stretched-sublinear allowance, since
\[
\log\!\left(
\frac{M\exp[-a\{(6+\log M)\log(6+\log M)\}^{1/11}]}{M^\alpha}
\right)\longrightarrow+\infty
\quad(a>0).
\]
Nevertheless, these energies are not subpolynomial.

The absent arithmetic information is explicit. The existing
`QMellinTransfer.qMellin_residue_zeta` identity is
\[
L_s(g_d)=\frac{\zeta(s)}s(d^{-1}-d^{-s}).
\]
For the chosen strip, the factor at \(d=2\) is nonzero, so the actual residue
dictionary lies in \(W_s\) if and only if \(\zeta(s)=0\).
No such zero is asserted. This comparison shows that floor-dilation invariance,
finite-head feasibility, bounded positive majorants, and the present
sublinear upper allowances alone do not supply the missing arithmetic bound.

## 5. Verification status

These arguments are ordinary mathematics, not newly Lean-checked declarations.
The additions in Sections 4.1--4.2 received an independent mathematical review;
Wolfram confirmed the displayed two-by-two characteristic polynomial and the
strict positivity of its asymptotic lower eigenvalue constant. These checks do
not replace formal verification. A separate conditional residual-bound Lean
snippet and axiom audit timed out at server limits of 240 and 600 seconds; a
narrower proof-only attempt also timed out at 180 seconds. No new Lean result or
successful axiom audit is claimed. Only this documentation was changed.

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
