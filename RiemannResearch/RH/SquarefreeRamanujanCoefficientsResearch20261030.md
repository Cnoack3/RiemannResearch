# Complete-squarefree Ramanujan coefficients and convergence audit

Date: 2026-10-30 (user's timezone).

The canonical construction is valid. This investigation does **not** prove
that its error tends to zero. It supplies the exact bridge to the existing
squarefree optimizer, complete-period formulas, quantitative coefficient
bounds proved below on paper, finite experiments, and an obstruction to
the raw Mobius trial.

Write \(X=N+1\), \(D_X=\{2\le d\le X:\mu(d)\ne0\}\), and
\(Q(n)=1/(\zeta(2)n^2)\), \(n\ge1\). Every dictionary includes composite
squarefree conductors. Zero coefficients are allowed.

## 1. Existing declarations and the measure distinction

The requested identities are correct, with \(B_1=0\):
\[
 B_q(n)=\sum_{d\mid q}\mu(q/d)d\,g_d(n),\qquad
 d\,g_d(n)=\sum_{q\mid d}B_q(n),\quad g_d(n)=\frac{n\bmod d}{d}.
\]

- RamanujanFiniteSpanBridge.lean states these Hilbert identities in **Pareto**.
- QRamanujanPackets.qRamanujanPacket_divisor_sum and
  qResidue_eq_divisor_packets establish them in actual Q.
- QRamanujanPackets.packetCoefficient and qSynthesis_eq_packets already give
  \(A_q=\sum_{d:q\mid d}\alpha_d/d\).
- QRamanujanCoefficientInversion.finite_packet_coefficient_inversion proves
  \(\alpha_d=d\sum_{q:d\mid q}\mu(q/d)A_q\) for equal finite syntheses.
- QSquarefreeInverseCapacity already owns the distinct squarefree index,
  conductor map, coefficients, and canonical candidate; candidate_eq_optimizer
  identifies it with \(P_N1\). Its coefficient definition uses the inverse
  **centered covariance**. The new module reuses these objects and identifies
  their coefficients with the uncentered Gram inverse.

The September memo's \(\langle B_q,1\rangle=\Lambda(q)\) is a **Pareto**
identity. It cannot be used as the Q normal-equation source. For example,
\[
 E_Q B_2=\frac34,\qquad E_Q B_6\approx-0.23536021764003440135,
\]
whereas the Pareto moments are \(\log2\) and \(0\).
The B6 decimal is a Wolfram evaluation of the exact divisor formula, not a
Lean-certified decimal. Composite packets can have nonzero Q means.

## 2. The complete finite construction

Let
\[
 G_{de}=\langle g_d,g_e\rangle_Q,\quad m_d=\langle g_d,1\rangle_Q,\quad
 \alpha=G^{-1}m.
\]
Distinct \(g_d\), \(d>1\), are independent. Indeed, for
\(F=\sum\alpha_dg_d\), \(F(0)=0\),
\[
 \Delta F(n)=\sum_d\frac{\alpha_d}{d}-\sum_{d\mid n}\alpha_d,\qquad
 \boxed{\alpha_r=-\sum_{k\mid r}\mu(r/k)\Delta F(k)\quad(r>1).}       \tag{1}
\]
Coefficients outside the dictionary are zero. Thus \(F=0\) forces all
coefficients to vanish, and the strictly positive Q weights give \(G>0\).

Set
\[
 A_{N,q}=\sum_{\substack{d\in D_X\\q\mid d}}\alpha_d/d.
\]
Every divisor \(q>1\) of an element of \(D_X\) is in \(D_X\), and \(B_1=0\).
Hence
\[
 \boxed{F_N=P_N1=\sum_{d\in D_X}\alpha_dg_d
                 =\sum_{q\in D_X}A_{N,q}B_q,}                     \tag{2}
\]
\[
 \boxed{\epsilon_N=1-m^{\mathsf T}G^{-1}m,}                         \tag{3}
\]
\[
 \boxed{\left\|1-\sum_dc_dg_d\right\|_Q^2
   =\epsilon_N+(c-\alpha)^{\mathsf T}G(c-\alpha).}                  \tag{4}
\]
The existing QSquarefreeInverseCapacity.exact_minimum supplies (4) in
Hilbert form, and error_eq_reciprocal gives
\(\epsilon_N=(1+\mathrm{inverseCapacity}(N))^{-1}\).

For \(T_{qd}=\mathbf1_{q\mid d}/d\) and
\(S_{dq}=d\mu(q/d)\mathbf1_{d\mid q}\), one has \(TS=ST=I\).
The packet Gram K and Q moment b satisfy
\[
 K=S^{\mathsf T}GS,\quad b=S^{\mathsf T}m,\quad
 A=T\alpha=K^{-1}b,\quad b^{\mathsf T}K^{-1}b=m^{\mathsf T}G^{-1}m.
\]
This changes coordinates, not approximation power.

Unconditionally,
\[
 F_N\longrightarrow P_{\overline V_{\rm sf}}1,\qquad
 \epsilon_N\downarrow\|1-P_{\overline V_{\rm sf}}1\|_Q^2.
\]
The new formal RH consumer assumes precisely
\(m_N^{\mathsf T}G_N^{-1}m_N\to1\). It does not prove that hypothesis.

## 3. Generalized CRT and complete-period Q identities

For positive representatives \(1\le r\le L\), using r=L for the zero class,
the complete progression mass is
\[
 w_L(r)=\sum_{j\ge0}\frac1{\zeta(2)(r+jL)^2}
       =\frac{\psi_1(r/L)}{\zeta(2)L^2}.                            \tag{5}
\]
Thus, with \(L_{de}=\operatorname{lcm}(d,e)\),
\[
 m_d=\sum_{r=1}^{d}w_d(r)\frac{r\bmod d}{d},\qquad
 G_{de}=\sum_{r=1}^{L_{de}}w_{L_{de}}(r)
       \frac{r\bmod d}{d}\frac{r\bmod e}{e}.                       \tag{6}
\]
These finite formulas include the **entire infinite Q tail**.

Generalized CRT permits residues a mod d and b mod e exactly when
\(a\equiv b\pmod{\gcd(d,e)}\), with one class modulo \(L_{de}\) for every
compatible pair. Formula (6) weights that exact class; the weights are
not independent uniform weights.

The uniform complete-period Gram, by contrast, is
\[
 H_{de}=\frac{(d-1)(e-1)}{4de}
        +\frac{\gcd(d,e)^2-1}{12de}.                              \tag{7}
\]
Proof: compatible residues have the form \(a=s+gu,b=s+gv\), with
\(g=\gcd(d,e)\). Under uniform averaging s,u,v are independent; the covariance
is \(\operatorname{Var}(s)/(de)=(g^2-1)/(12de)\).

The divisibility correlations are exactly
\[
 E_Q[\mathbf1_{d\mid n}\mathbf1_{e\mid n}]=\operatorname{lcm}(d,e)^{-2},
\quad E_Q[(d\mathbf1_{d\mid n})(e\mathbf1_{e\mid n})]
       =\frac{\gcd(d,e)^2}{de}.                                   \tag{8}
\]
Their squarefree tensorization controls the divisibility features, not
automatically their legal primitives. For example,
\[
 \|\Delta g_p\|_Q^2=\frac{2(p-1)}{p^3},\qquad
 \|g_p\|_Q^2\ge\frac{p-1}{\zeta(2)p^2},\qquad
 \frac{\|g_p\|_Q^2}{\|\Delta g_p\|_Q^2}\ge\frac p{2\zeta(2)}.
\]
Already single primes exclude a uniform upper primitive-energy bound from
difference energy.

For a common period L and R=1-F, the complete equality is
\[
 \|R\|_Q^2=\frac1{\zeta(2)}\sum_{r=1}^{L}\frac{R(r)^2}{r^2}
                  +\sum_{r=1}^{L}w_L(r+L)R(r)^2.                 \tag{9}
\]
QPeriodicTailEnergy bounds its second term between
\[
 \frac{1-\zeta(2)^{-1}}{L^2}\sum_{r=1}^{L}R(r)^2
 \quad\hbox{and}\quad \frac1{L^2}\sum_{r=1}^{L}R(r)^2.             \tag{10}
\]
All signed summands remain inside the squares. These formulas do not
supply first-period cancellation as X grows. Also
\(\epsilon_N\ge L^{-2}>0\): all finite trials vanish on positive multiples
of L, whose Q mass is \(L^{-2}\).

The special-function series is DLMF 5.15.1:
https://dlmf.nist.gov/5.15.E1 .
The project already formalizes progression-series and periodic-tail
identities; those bounds do not require special-function asymptotics.

## 4. Actual inverse-Gram bounds: paper proofs

These estimates are proved here on paper; they are **not new Lean
declarations** in this publication.

For m>1 define
\[
 t_{m,n}=\mathbf1_{n\mid m}\mu(m/n)
       -\mathbf1_{n+1\mid m}\mu(m/(n+1)),\quad 1\le n\le m,\qquad
 C_m^2=\zeta(2)\sum_{n=1}^{m}n^2t_{m,n}^2.
\]
A false divisibility term is zero. Equation (1) and weighted Cauchy--Schwarz
give
\[
 |\alpha_m|\le C_m\|F\|_Q,\qquad
 |\alpha_m+\mu(m)|\le C_m\|1-F\|_Q.                               \tag{11}
\]
The residual at index zero is anchored at zero. Hence for the canonical solve,
whenever \(m\in D_X\),
\[
 |\alpha_{N,m}|\le C_m,\qquad
 |\alpha_{N,m}+\mu(m)|\le C_m\sqrt{\epsilon_N},\qquad
 (G_N^{-1})_{mm}\le C_m^2.                                       \tag{12}
\]
For the last inequality use \(F=\sum_d(G_N^{-1})_{dm}g_d\).
Its squared norm and m-th coefficient are both \((G_N^{-1})_{mm}>0\).
Also \(C_m^2\le4\zeta(2)\sum_{d\mid m}d^2\).
These bounds do not identify the coefficient limits with \(-\mu(m)\).

There is a collective estimate. Write \(h_X=\sum_{k=1}^{X}1/k\),
\(b_n=\Delta F(n)/n\), \(a_1=-F(1)\), and \(a_m=\alpha_m/m\) for m>=2.
Then
\[
 a_m=-\sum_{k\mid m}\frac{\mu(k)}k\,b_{m/k},\quad 1\le m\le X.
\]
The dilation supported on multiples of k is a contraction on the truncated
unweighted \(\ell^2\) space. The triangle inequality therefore gives
\(\|a\|_2\le h_X\|b\|_2\).
Since F(0)=0 and
\(\sum_{n=1}^{X}F(n-1)^2/n^2\le\sum_{n\ge1}F(n)^2/n^2\),
\(\|b\|_2\le2\sqrt{\zeta(2)}\|F\|_Q\). Thus
\[
 \sum_{d\in D_X}\frac{|\alpha_d|^2}{d^2}
       \le4\zeta(2)h_X^2\|F\|_Q^2,
\]
\[
 \boxed{G_N\succeq\frac{\operatorname{diag}(d^{-2}:d\in D_X)}
                         {4\zeta(2)h_X^2},\qquad
        \|G_N^{-1}\|_{\rm op}\le4\zeta(2)h_X^2X^2.}               \tag{13}
\]
This is unconditional polynomial conditioning, not target saturation.

For the canonical solve \(\|F_N\|_Q\le1\), so
\[
 \sum_d|\alpha_{N,d}|\le
 B_X:=2\sqrt{\zeta(2)}h_X\left(\sum_{d\in D_X}d^2\right)^{1/2}.
\]
For every integer T>=1, using \(|g_d(n)|\le1\) and
\(\sum_{n>T}n^{-2}\le1/T\),
\[
 \boxed{\sum_{n>T}Q(n)|1-F_N(n)|^2
       \le\frac{(1+B_X)^2}{\zeta(2)T}.}                            \tag{14}
\]
Taking \(T=X^4\) makes the upper bound \(O((\log X)^2/X)\).
The remaining unknown is the error on the growing head \(n\le T\).
Controlling this remote tail does not imply that the head error vanishes.

## 5. Explicit alternatives

### The raw Mobius family fails

Let \(M_X=-\sum_{d\in D_X}\mu(d)g_d\) and
\(s_X=\sum_{d\le X}\mu(d)/d\). For \(1\le n\le X\), the exact floor identity gives
\(M_X(n)=1-ns_X\). Consequently,
\[
 \boxed{\|1-M_X\|_Q^2=\frac X{\zeta(2)}s_X^2
          +\sum_{n>X}\frac{|1-M_X(n)|^2}{\zeta(2)n^2}.}           \tag{15}
\]
QMobiusTrialHeadObstruction.error_head_tail proves this equality, with
X=N+1 and the complete tail reindexed. head_energy_le_error proves the
lower bound. Neither is a lower bound for the canonical optimizer.

Classically \(s_X\ne o(X^{-1/2})\). For \(\Re s>1\),
\[
 \int_1^\infty x\,s_{\lfloor x\rfloor}x^{-s-1}\,dx
       =\frac1{(s-1)\zeta(s)}.
\]
A nontrivial zero on \(\Re s=1/2\) supplies a pole, and the Mellin order
lemma excludes \(x s_{\lfloor x\rfloor}=o(x^{1/2})\).
Thus (15) rules out \(\|1-M_X\|_Q\to0\), unconditionally.
This analytic oscillation step is a **paper consequence**, not newly
formalized here. The Lean nonconvergence consumer exposes it as a hypothesis.

Reference: L. Baez-Duarte, *Arithmetical Aspects of Beurling's Real Variable
Reformulation of the Riemann Hypothesis*, arXiv:math/0011254,
Lemma 2.1 and Proposition 2.1, supporting this Mellin argument:
https://arxiv.org/pdf/math/0011254 .

For squarefree q>1 the raw packet coefficients are
\[
 A^{\rm raw}_{X,q}=-\frac{\mu(q)}q
        \sum_{\substack{k\le X/q\\(k,q)=1}}\frac{\mu(k)}k.
\]

### Corrected and smoothed trials

For a prime p>X,
\[
 M_X^{\rm head}=M_X+p\,s_Xg_p,\qquad
 M_X^{\rm head}(n)=1\quad(1\le n\le X).
\]
Its full error remains a tail-energy problem; numerical data include this
variant with its enlarged cutoff p.

The other tested profiles were
\[
 -\mu(d)\left(1-\frac{\log d}{\log X}\right),\quad
 -\mu(d)\left(1-\frac d{X+1}\right),\quad
 -\mu(d)\left(1-\left(\frac{\log d}{\log X}\right)^2\right).
\]
They are indexed over all of \(D_X\). For any nonzero trial V, the best scalar is
\[
 \lambda=\frac{\langle1,V\rangle_Q}{\|V\|_Q^2},\qquad
 \|1-\lambda V\|_Q^2
      =1-\frac{\langle1,V\rangle_Q^2}{\|V\|_Q^2}.
\]
This uses only two full-Q quantities, not the large inverse Gram.
The scalar-normalized quadratic-log profile outperforms the scalar-normalized
linear-log profile at the reported cutoffs. Its asymptotic convergence is unproved.

## 6. Computations and a rational finite certificate

Every floating-point Gram entry uses (6), including the entire tail.
Normal-equation defects are at most \(1.2\,10^{-16}\); physical packet-transform
checks through site 2048 have discrepancy below \(4.3\,10^{-15}\).
These are exploratory floating-point checks, not interval or Lean certificates.

| Cutoff X | Dictionary size | Canonical squared error | Raw Mobius | Scaled linear-log | Scaled quadratic-log |
|---:|---:|---:|---:|---:|---:|
| 16 | 10 | 0.0127746211 | 0.0623635428 | 0.0249170746 | 0.0189343776 |
| 32 | 19 | 0.0098665600 | 0.1106924717 | 0.0163371797 | 0.0127971241 |
| 64 | 38 | 0.0075828738 | 0.0331100224 | 0.0117682725 | 0.0093360767 |
| 128 | 77 | 0.0063331022 | 0.0241845209 | 0.0092199618 | 0.0077222886 |
| 256 | 156 | 0.0053405567 | 0.0254092586 | 0.0076581014 | 0.0066810337 |

Wolfram independently obtained, at 40-digit working precision,
\(\epsilon_{15}=0.012774621087996827769214121856\ldots\).
No limiting decay law is inferred from this finite range.

A separate rational certificate uses, on
\(D_{16}=(2,3,5,6,7,10,11,13,14,15)\), the coefficients
\[
 \frac1{100}(99,95,82,-58,69,-40,49,47,-35,-12).
\]
The common period is L=30030. Equations (9)--(10), the elementary inequality
\(\zeta(2)>\sum_{n=1}^{23}n^{-2}>8/5\), and outward rounding of positive
first-period terms to multiples of \(2^{-70}\) give
\[
 \|1-F_{\rm rational}\|_Q^2
 \le \frac{87640912280977745186713323370986487}
           {6660770279259472370356463861760000000}
 <\frac1{75}.
\]
Every operation in the certificate program is integer or rational.
Thus \(\epsilon_{15}<1/75\), also for all later stages by monotonicity.
This is an **external exact-arithmetic certificate plus the paper tail
argument**, not a Lean-certified numerical bound.

Data and executable program text are in
RH/experiments/squarefree_ramanujan_20261030/.
The floating-point program requires NumPy and SciPy; the rational certificate
requires only the Python standard library.

## 7. Remaining arithmetic obligation

For successive genuinely new squarefree conductors, let v be the old
cross-Gram column, a the new diagonal, and m* the new moment. The exact
Schur quantities are
\[
 \sigma=a-v^{\mathsf T}G^{-1}v>0,\qquad
 h=m_*-v^{\mathsf T}G^{-1}m,\qquad
 \epsilon_{\rm next}=\epsilon-\frac{h^2}{\sigma}.
\]
Finite-stage error is strictly positive, so
\(0\le\gamma=h^2/(\sigma\epsilon)<1\). The product identity gives
\[
 \epsilon_k=\epsilon_0\prod_{j<k}(1-\gamma_j),\qquad
 \epsilon_k\to0\ \Longleftrightarrow\ \sum_j\gamma_j=\infty.
\]
An eventual estimate \(\gamma_j\ge c/(j+1)\), c>0, would suffice.
It has not been proved for these actual arithmetic quantities.

Concrete next obligations:

1. Prove a non-summable lower budget for the actual signed Schur gains, keeping
   all composite squarefree conductors.
2. Alternatively prove the full Q error of an explicit smoothed Mobius profile
   tends to zero. Pointwise convergence is insufficient.
3. Formalize the paper conditioning and tail estimates (11)--(14) and use them
   to certify larger finite computations. This is finite control, not yet the
   required cancellation.
4. Formalize the classical oscillation provider for the raw-trial
   nonconvergence consumer. Excluding this ansatz does not refute RH.

No lower bound for the raw trial is transferred to the canonical minimum.
No projection limit is silently identified with 1, and no uniform CRT
Gram is substituted for the Q Gram.
