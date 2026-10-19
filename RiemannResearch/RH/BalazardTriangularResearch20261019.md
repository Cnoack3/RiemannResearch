# Balazard's arithmetic transform: strong triangular dual averages

Date: 19 October 2026.

Source: Michel Balazard, *An arithmetical function related to Báez-Duarte's
criterion for the Riemann hypothesis*, arXiv:1812.04309v1, 13 pages.
The corrected upload was read in full, including the appendix. The earlier
upload was Bettin--Conrey--Farmer and is not the paper reviewed here.
Stable source: https://arxiv.org/abs/1812.04309.

This note gives a complete ordinary mathematical argument extending the
weak reciprocal-dual convergence in Propositions 6--7 to strong convergence
of its triangular means, with an exact energy remainder. No novelty claim
relative to the wider literature is made. This is not a proof of RH.

## 1. What the paper settles, and what it leaves open

Proposition 12 already proves unconditional fixed-index convergence of the
optimal coefficients. Proposition 13 identifies the assertion that their
limits are -mu(d) for every d>=2 as equivalent to RH. Thus existence of
coefficient limits is not the remaining problem.

In the project's real sequence convention,
\[
 \|h\|_P^2=\sum_{k\ge1}\frac{h(k)^2}{k(k+1)},\qquad
 \|h\|_Q^2=\frac1{\zeta(2)}\sum_{k\ge1}\frac{h(k)^2}{k^2}.
\]
Their norms are equivalent, but their Riesz representatives and orthogonal
projections differ. All Q statements below use the actual Q inner product.

For either Hilbert space, if p is the limiting projection of 1 onto the
chosen legal closed span and r=1-p, fixed legal coefficient limits obey
\[
 c_{\infty,d}+\mu(d)=w(d;r),\qquad d\ge2,
\]
where \(w(d;h)=(\mu*\Delta h)(d)\), with h(0)=0.
This identifies the defect exactly; it does not prove that it vanishes.
The repository already contains the full-P and squarefree-Q versions.

## 2. Definitions and sign convention

Use the paper's dual vectors
\[
 \phi_d(k)=d(d-1)\mathbf1_{k=d-1}
             -d(d+1)\mathbf1_{k=d},\qquad
 f_n=\sum_{d\mid n}\mu(n/d)\phi_d.
\]
Then \(w(n;h)=-\langle h,f_n\rangle_P\).
The repository's mobiusRieszHilbert is \(-f_n\).

Set
\[
 m(x)=\sum_{d\le x}\frac{\mu(d)}d,\quad
 M(x)=\sum_{d\le x}\mu(d),\quad
 \beta_j=\sum_{n\le j}\frac{f_n}{n},\quad\beta_0=0.
\]
For integer N>=2 define
\[
 S_N=\frac1N\sum_{j=0}^{N-1}\beta_j
     =\sum_{n\le N}\left(1-\frac nN\right)\frac{f_n}{n},
 \qquad
 e_N=\frac1N\sum_{j=1}^{N-1}m(j)^2.
\]
The equality counts the N-n indices j with n<=j<N; the n=N coefficient
is zero. The repository's triangularChargeRiesz is \(-S_N\).

## 3. Exact coordinates, with endpoints retained

Regrouping the finite divisor sum gives
\[
 S_N=\sum_{d\le N}a_N(d)\phi_d,\qquad
 a_N(x)=\frac{m(N/x)}x-\frac{M(N/x)}N
       =\sum_{j\le N/x}\mu(j)\left(\frac1{jx}-\frac1N\right).
\]
Each summand is zero at its entry breakpoint, so a_N is continuous and
piecewise differentiable. Away from these finitely many breakpoints,
\[
 a_N'(x)=-\frac{m(N/x)}{x^2}.
\]
Consequently, for every integer k>=1,
\[
 S_N(k)=k(k+1)[a_N(k+1)-a_N(k)]
       =-k(k+1)\int_k^{k+1}m(N/t)\frac{dt}{t^2}
       =-\frac{k(k+1)}N\int_{N/(k+1)}^{N/k}m(u)\,du.
\]
Explicitly,
\[
 S_N(k)=k\,m(N/(k+1))-(k+1)m(N/k)
 -\frac{k(k+1)}N\{M(N/(k+1))-M(N/k)\}.
\]
There is no endpoint atom: the integrands are ordinary step functions and
the entering summand in a_N is zero. Also S_N(k)=0 for k>=N.

## 4. Exact finite variance identity, then the norm bound

For 1<=k,j<N let
\[
 \ell_{k,j}=
 \max\left\{0,\,
 \min\left(\frac1k,\frac{j+1}N\right)
 -\max\left(\frac1{k+1},\frac jN\right)\right\}.
\]
These are lengths of intersections between two partitions of [1/N,1].
Thus
\[
 \sum_j\ell_{k,j}=\frac1{k(k+1)},\qquad
 \sum_k\ell_{k,j}=\frac1N,\qquad
 S_N(k)=-k(k+1)\sum_j\ell_{k,j}m(j).
\]
All sums here run from 1 to N-1. Expansion of the square, using these three
identities, proves the complete energy equality
\[
 \boxed{\quad
 e_N=\|S_N\|_P^2+V_N,\qquad
 V_N=\sum_{k,j=1}^{N-1}\ell_{k,j}[m(j)+S_N(k)]^2.
 \quad}
\]
Indeed each row variance equals
\(\sum_j\ell_{k,j}m(j)^2-S_N(k)^2/[k(k+1)]\).
Summing the columns gives e_N. There is no missing interval near zero,
because m(u)=0 on [0,1), and no missing tail because S_N(k)=0 for k>=N.

Dropping precisely the nonnegative term V_N gives
\[
 \boxed{\|S_N\|_P^2\le e_N\longrightarrow0.}
\]
The last limit is Cesaro convergence applied to the classical unconditional
m(j)->0, a consequence of the prime number theorem. It requires no RH.

Equivalently, S_N is the orthogonal projection onto the integer step-function
subspace of b_N(t)=-m(N/t) for t>=1 and b_N(t)=0 for t<1. Change of variables
gives ||b_N||^2=e_N and the projection remainder is V_N.

For a completely finite implementation, define
\(H_j(t)=(t-j)_+-(t-j-1)_+\). Then
\[
 \ell_{k,j}=\frac{H_j(N/k)-H_j(N/(k+1))}N.
\]
Column sums telescope in k, and row sums follow from
\(\sum_{j=1}^{N-1}H_j(t)=t-1\) for 1<=t<=N. This avoids measure theory.

The elementary |m(j)|<=1 also gives |S_N(k)|<=1. For 1<=H<N,
\[
 e_N\le \frac{H-1}N+\sup_{j\ge H}|m(j)|^2.
\]
This supplies an explicit bound whenever a reciprocal-Mobius bound is used.

## 5. Uniform moving-test consequence

Define
\[
 \Lambda_N(h)=\sum_{n\le N}\left(1-\frac nN\right)\frac{w(n;h)}n.
\]
Cauchy--Schwarz and the exact energy identity give
\[
 |\Lambda_N(h)|\le \sqrt{e_N-V_N}\,\|h\|_P
                 \le\sqrt{e_N}\,\|h\|_P.
\]
Thus Lambda_N(h_N)->0 for every uniformly bounded moving sequence h_N.
More generally it suffices that ||h_N||_P sqrt(e_N)->0. No convergence
of h_N itself is needed. This is the useful strengthening of the paper's
fixed-test weak convergence result.

The unsmoothed dual sums cannot tend strongly to zero:
beta_N(N)=-(N+1), so ||beta_N||_P^2 >= (N+1)/N.
The exact de-averaging identity is
\[
 \sum_{n\le N}\frac{w(n;h)}n
 =\Lambda_N(h)+\frac1N\sum_{n\le N}w(n;h).
\]
Any use requiring an unsmoothed moving test still needs to control the
second term. Smoothing does not silently discharge that obligation.

## 6. Actual Q norm, and the squarefree specialization

Put
\[
 D_N(k)=\zeta(2)\frac{k}{k+1}S_N(k).
\]
This rescaling is essential:
\(\langle h,D_N\rangle_Q=\langle h,S_N\rangle_P=-\Lambda_N(h)\).
Its complete energy is
\[
 \|D_N\|_Q^2=\zeta(2)\sum_{k<N}\frac{S_N(k)^2}{(k+1)^2}.
\]
Retaining the exact change-of-measure remainder
\[
 W_N=\sum_{k=1}^{N-1}\frac{S_N(k)^2}{k(k+1)^2},
\]
we get
\[
 \boxed{\zeta(2)e_N=\|D_N\|_Q^2+\zeta(2)V_N+\zeta(2)W_N.}
\]
In particular,
\[
 |\Lambda_N(h)|\le \sqrt{\zeta(2)e_N}\,\|h\|_Q.
\]
This applies to the actual moving Q projections and residuals, whose
norms are at most ||1||_Q=1.

For the legal atoms \(g_d(k)=\{k/d\}\),
\[
 w(n;g_d)=\frac{\mathbf1_{n=1}}d-\mathbf1_{n=d}.
\]
Every fixed w(n;.) is continuous in Q. Hence for the closed span of
squarefree atoms, w(n;h)=0 at every nonsquarefree n>=2. The same is true
of 1-h because mu(n)=0 there. The uniform estimate therefore restricts
exactly to squarefree coefficients; no discarded nonsquarefree term
needs a bound.

## 7. An unconditional inverse-Gram consequence

Let a finite dictionary D consist of distinct integers 2<=d<=N, possibly
only squarefree integers or primorial divisors. Its actual Q-Gram matrix
G is positive definite: applying w(d;.) to a linear relation proves
independence. Let V=span{g_d:d in D}, and v_d=1-1/d. Direct calculation gives
\[
 \Lambda_N(g_d)=\frac{v_d}N,\qquad
 \langle g_d,D_N\rangle_Q=-\frac{v_d}N.
\]
The exact orthogonal projection identity is therefore
\[
 \boxed{\zeta(2)N\sum_{j<N}m(j)^2
 =v^\top G^{-1}v+N^2\|D_N-P_VD_N\|_Q^2
   +\zeta(2)N^2(V_N+W_N).}
\]
It follows, by dropping the displayed nonnegative remainders, that
\[
 v^\top G^{-1}v\le \zeta(2)N\sum_{j<N}m(j)^2=o(N^2).
\]
Equivalently, every legal F=sum c_d g_d supported on D satisfies
\[
 \left|\sum_{d\in D}c_d(1-1/d)\right|^2
 \le \zeta(2)N\sum_{j<N}m(j)^2\,\|F\|_Q^2.
\]
This controls a concrete collective coefficient direction, but v is not
the target-mean vector b_d=<1,g_d>_Q.

For completeness, put b_d=<1,g_d>_Q, c=G^{-1}b,
E=||1-P_V1||_Q^2=1-b^TG^{-1}b, and
tau_N=N^{-1}sum_{j<N}m(j). The finite Abel identity gives Lambda_N(1)=tau_N.
Testing the residual against D_N-P_VD_N yields
\[
 [N\tau_N-v^\top G^{-1}b]^2
 \le E\,[N^2\|D_N\|_Q^2-v^\top G^{-1}v]
 \le E\,[\zeta(2)N\sum_{j<N}m(j)^2-v^\top G^{-1}v].
\]
The first bracket on the right is exactly a squared norm. This is a lower
certificate for E when its left side is nonzero; it is not an upper bound
forcing E->0.

## 8. What this fills, and what remains

This fills a specific technical gap if an argument needs uniform
triangular reciprocal-charge cancellation against bounded moving Q
vectors. It also gives the explicit finite inverse-Gram estimate above.

It does not prove q_M->1, identify coefficient limits with -mu, or bound
the energies of the legal exact-head candidates. The vectors S_N and D_N
are dual test vectors, not approximants to the target by legal atoms.
The uniform cancellation holds for every ambient vector, so on its own
it cannot distinguish whether the target belongs to the legal closure.

For the existing squarefree/LCM route, a productive remaining target is
bounded complete Q energy along a cofinal exact-head sequence. Head
convergence plus boundedness would put 1 in the weakly closed legal span.
The stronger claim ||1-F_M||_Q->0 would also work, but is unnecessary for
that particular route. A comparison of adjacent LCM blocks alone does
not provide either bound.

The present inverse-Gram inequality controls v^TG^{-1}v. A further argument
would need to connect this direction to b^TG^{-1}b, or furnish a stable
legal synthesis estimate. No such connection is proved here.

## 9. Formal verification boundary

The accompanying Lean modules formalize:
- the general finite weighted-variance identity and its contraction;
- the exact triangular-charge pairing and de-averaging decomposition;
- nonnegativity and unconditional convergence of e_N.

They do not yet formalize the concrete overlap-matrix row/column
identification, its equality with the actual triangular Riesz vector,
the resulting strong norm bound, or the Q/Gram consequences. Those are
ordinary mathematical proofs in this note, not claimed to be
kernel-verified application theorems. The remaining formalization bridge
must be completed before labeling the whole extension as a checked Lean
result. RH-level approximation energy remains open independently.
