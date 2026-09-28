# Stronger unconditional energy estimate for the canonical Möbius family

Let
```math
g_d(j)=\frac{j\bmod d}{d},\quad
\|f\|_P^2=\sum_{j=1}^{\infty}\frac{|f(j)|^2}{j(j+1)},\quad
M(x)=\sum_{k\le x}\mu(k),\quad m_N=\sum_{k=1}^N\frac{\mu(k)}k.
```

The auxiliary exact-head approximant is
```math
A_N=-\sum_{d=1}^N\mu(d)g_d+(N+1)m_Ng_{N+1}.
```
It equals one on coordinates 1 through N and lies in V_(N+1).
It is the repository's canonicalMobiusHilbert N.
The user's optimal F_(N+1) remains the orthogonal projection with
c=G^{-1}b=-mu+G^{-1}(b+Gmu); A_N is an auxiliary comparison vector.

## New unconditional bound

Put Phi(N)=((6+log N)log(6+log N))^(1/11).
There exist positive a and nonnegative C such that, for all sufficiently large N,
```math
|m_N|\le C e^{-a\Phi(N)},\qquad
\|A_N\|_P^2\le 3+CN e^{-a\Phi(N)},
```
and, with another C,
```math
\boxed{\|1-A_N\|_P^2\le 8+CN e^{-a\Phi(N)}.}
```
The complete infinite norm is used in every estimate.

This improves the project's earlier normalized ceiling of order
loglog(N)/log(N) to a stretched exponential in log(N).
The exponentially decaying factor is smaller than every fixed inverse
power of log(N). Its positive exponent constant is existential.

## Finite transfer, with all constants

Suppose N>=1, 0<h<=1/2, and |M(y)|<=h^2 y for every real y>=N.
Choose K=ceil(1/h). Then
```math
K\ge2,\qquad K^{-1}\le h,\qquad Kh\le2.
```
Writing H_K for the harmonic sum and using H_K<=K, the exact
reciprocal cutoff estimate gives
```math
|m_N|\le K^{-1}+(NK)^{-1}+h^2(H_K+1)\le5h.
```
Here (NK)^(-1)<=K^(-1) and
h^2(H_K+1)<=h(Kh)+h^2<=3h.

The exact signed floor-tail identity gives, on N<j<=KN,
```math
|A_N(j)|\le1+jD,\qquad
D=h^2(H_K+1)+5h\le8h.
```
The already established complete harmonic-window energy estimate is
```math
\frac{\|A_N\|_P^2}{N}\le\frac3N+2KD^2+\frac4K.
```
It retains the entire region j>KN, where |A_N(j)|<=2N and
the Pareto weights telescope; that region contributes at most 4N/K.
Consequently
```math
\frac{\|A_N\|_P^2}{N}
\le\frac3N+128Kh^2+4h
\le\frac3N+260h.
```

The unconditional checked provider M_stretched_loglog_bound supplies
d>0 and B>=0 with
```math
|M(y)|\le By e^{-d\Phi(y)}\quad(y\ge1).
```
Phi is increasing. Set h_N=sqrt(B+1)exp(-d Phi(N)/2).
It is positive, tends to zero, and its square dominates
B exp(-d Phi(N)). Thus the finite transfer applies for all sufficiently
large N and yields the claimed bounds with a=d/2.
Finally, ||1||_P^2=1 and
```math
\|1-A_N\|_P^2\le2\|A_N\|_P^2+2
\le8+520\sqrt{B+1}\,N e^{-d\Phi(N)/2}.
```

## Exact scope and remaining obligation

No RH, density assumption, bounded-subsequence assumption, or unproved
arithmetic estimate appears in the new assembled Lean theorems.
The imported Mertens theorem is an established project result.

The factor N remains. Since Phi(N)=o(log N),
N exp(-a Phi(N)) tends to infinity, so this upper bound does not establish
boundedness along a cofinal subsequence. It does not prove
||1-F_N||_P -> 0, identify the limiting coefficient corrections as zero,
or resolve RH. It is an unconditional improvement of the arithmetic
error estimate, not another assumption equivalent to the desired conclusion.

## Lean declarations

File: RH/CanonicalMobiusStretchedEnergy.lean, namespace
RiemannResearch.RH.Pareto.

- canonicalMobius_energy_of_uniform_mertens_square: the finite transfer.
- canonicalMobius_eventual_stretched_bounds: unconditional reciprocal
  charge and full canonical energy bounds.
- canonicalMobiusResidual_eventual_stretched_energy: unconditional
  full exact-head error bound.

Provenance: the user's request for concrete progress, the existing exact
finite cutoff identities and full-energy lemmas, and the project's
MertensStretchedDecay arithmetic provider. No claim of mathematical
novelty is made.

## Verification

The complete proof and all three declarations passed serialized Lean job
job_Nfz56UffWqCAqL31ti2zVBCuQmy31lQe with exit_code=0 and verified=true.
Each declaration reports only propext, Classical.choice, and Quot.sound.
The two assembled rate theorems have no domain-specific hypotheses.
The project checkpoint additionally checks the saved module before publication.
