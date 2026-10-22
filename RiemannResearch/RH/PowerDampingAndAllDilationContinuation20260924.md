# RH continuation: power damping, finite dilations, and exact source mass

Date: 2026-09-24.
Starting commit: `0ec9dc5fa91af4c02368b5badc38324e8022b93c`.
Source: `RH_Lateral_Screening_Continuation_2026-09-24(2).md`.

## Outcome and verification boundaries

Unconditional RH was not proved. This continuation supplies a stronger analytic
regularity criterion and four Lean modules supporting the continuation.
No unproved regularity or source divergence is treated as an established fact.

| Result | Status in this continuation |
|---|---|
| Genuine damped Möbius sum: exact increment, linear bound, weighted variation with constant 2 | Lean-verified |
| Pointwise damped limit and dominated primitive-side series limit | Lean-verified |
| Quotient energy and physical norm limit for every finite signed integer-dilation family | Lean-verified |
| Exact full-space source mass, its infinite telescope, and necessary harmonic-weighted source summability under nondensity | Lean-verified |
| Centered Dini-envelope criterion; logarithmic exponent improves from p>2 to p>1 | Complete mathematical proof, independently audited; full infinite interchange and RH assembly not yet formalized |
| All-dilation certificate energy approaching 1; full innovation liminf at least 1 | Mathematical proof using the verified finite-dilation limit; Euler-product specialization and final lower bound not yet formalized |
| Dini envelope for the actual residual, or divergence of its actual signed source series | Open |

The coherent Lean candidate passed with `exit_code=0`, `verified=true`, and no
warnings in job `job_WtSkUHE6PV6s54DI2gwB78M0YrKoFh1Y`.
The five principal axiom inspections printed only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, `admit`, project-local axiom, or unsafe declaration
was introduced. These axiom checks do not discharge hypotheses appearing in a
theorem's type.

The required publication checkpoint validates the saved modules before commit
and push. Its result and commit are recorded in the delivered copy of this report;
for the repository copy, see the commit containing this file.

## 1. The mathematical improvement: preserve the signed damping

The original sharp-cutoff proof controlled a variation term by a positive
divisor-count majorant. Its p>2 threshold is sharp for that majorant. The new
argument changes the approximating family and keeps the signed Möbius sum
until it becomes a nonnegative Euler product. Thus it does not contradict the
old sharpness statement.

The full proof follows. It is an implication from a regularity hypothesis;
its application to the actual residual remains conditional.

## Power damping improves the centered physical primitive criterion

This is a complete mathematical derivation, not yet a Lean verification of the analytic limit/interchange statements.

Let the physical Hilbert space have norm
\[
\|f\|^2=\sum_{n\ge1}\frac{|f_n|^2}{n(n+1)},
\qquad \rho_d(n)=\{n/d\}.
\]
Suppose \(f\in H\) is orthogonal to every \(\rho_d\), \(d\ge2\). Write
\(H_f(n)=\sum_{k=1}^n f_k\). All derivations below use real sequences; conjugations give the complex version.

### Theorem

Suppose there exist \(L\in\mathbb R\) and a nonnegative nonincreasing sequence \(\Psi(n)\), \(n\ge1\), such that
\[
|H_f(n)-Ln|\le n\Psi(n),
\qquad \sum_{n\ge1}\frac{\Psi(n)}n<\infty.
\]
Then \(\langle1,f\rangle=0\).

Consequently, for the canonical residual \(r=\Pi_{V^\perp}1\), this hypothesis gives
\(\|r\|^2=\langle1,r\rangle=0\), hence RH by the existing legal-closure criterion.

In particular the hypothesis
\[
|H_r(n)-Ln|\le \frac{C n}{\log(2n)^p},\qquad p>1,
\]
suffices. This improves the sharp-cutoff unsigned-divisor proof's threshold \(p>2\). It does not prove that the actual residual obeys this bound.

### 1. Exact arithmetic damping

For \(\varepsilon>0\), put
\[
c_\varepsilon=\sum_{d\ge1}\frac{\mu(d)}{d^{1+\varepsilon}}
=\frac1{\zeta(1+\varepsilon)},
\qquad
a_\varepsilon(k)=\sum_{d\mid k}\frac{\mu(d)}{d^\varepsilon}
=\prod_{p\mid k}(1-p^{-\varepsilon}).
\]
Thus \(0<c_\varepsilon<1\), \(0\le a_\varepsilon(k)\le1\), and \(a_\varepsilon(1)=1\).
Define pointwise
\[
A_\varepsilon(n)
=-\sum_{d\ge2}\mu(d)d^{-\varepsilon}\rho_d(n)
=\sum_{k=1}^n a_\varepsilon(k)-c_\varepsilon n.
\]
The infinite series is absolutely convergent for each fixed \(n\), since
\(\rho_d(n)\le n/d\). The second equality follows by writing
\(\rho_d(n)=n/d-\lfloor n/d\rfloor\) and grouping the finite floor sum by \(k\).
The coefficient of \(d=1\) does not matter, because \(\rho_1=0\).

The exact jump is
\[
A_\varepsilon(n+1)-A_\varepsilon(n)=a_\varepsilon(n+1)-c_\varepsilon.
\]
Therefore
\[
|A_\varepsilon(n)|\le n,\qquad
|A_\varepsilon(n+1)-A_\varepsilon(n)|\le1.
\]
Moreover \(c_\varepsilon\to0\) and, for every fixed \(k\ge2\),
\(a_\varepsilon(k)\to0\) as \(\varepsilon\downarrow0\). Hence
\[
A_\varepsilon(n)\longrightarrow1
\quad\text{for every fixed }n\ge1.
\]

### 2. Uniform variation and boundary

Set \(q_\varepsilon(n)=A_\varepsilon(n)/[n(n+1)]\). Then exactly
\[
q_\varepsilon(n)-q_\varepsilon(n+1)
=\frac{2A_\varepsilon(n)}{n(n+1)(n+2)}
-\frac{a_\varepsilon(n+1)-c_\varepsilon}{(n+1)(n+2)}.
\]
Consequently
\[
|q_\varepsilon(n)-q_\varepsilon(n+1)|
\le\frac3{(n+1)(n+2)}
\]
uniformly in \(\varepsilon>0\).

Let \(g=f-L\) and \(C_n=H_f(n)-Ln=\sum_{k\le n}g_k\).
The hypotheses imply \(\Psi(n)\to0\). Since \(|q_\varepsilon(n)|\le1/(n+1)\),
\[
|C_Nq_\varepsilon(N)|\le\Psi(N)\longrightarrow0.
\]
Finite summation by parts followed by this boundary limit therefore defines the (possibly conditionally convergent) pairing by
\[
\sum_{n\ge1}g_nq_\varepsilon(n)
=\sum_{n\ge1}C_n\bigl(q_\varepsilon(n)-q_\varepsilon(n+1)\bigr).
\]
The right side is absolutely convergent, uniformly dominated by
\(3\Psi(n)/n\). Dominated convergence and pointwise \(A_\varepsilon(n)\to1\) give
\[
\lim_{\varepsilon\downarrow0}\sum_{n\ge1}g_nq_\varepsilon(n)
=\sum_{n\ge1}\frac{g_n}{n(n+1)}=\langle1,g\rangle.
\]
The final equality also follows directly from Hilbert-space Cauchy--Schwarz.

**No assertion that \(A_\varepsilon\) belongs to the physical Hilbert space or its legal closed subspace is used.** Such an assertion need not be available for small \(\varepsilon\).

### 3. Absolute interchange after summation by parts

Write \(b_d(n)=\rho_d(n)/[n(n+1)]\). Its exact weighted jump is
\[
b_d(n)-b_d(n+1)
=\frac{2\rho_d(n)}{n(n+1)(n+2)}
+\frac{\mathbf1_{d\mid n+1}-1/d}{(n+1)(n+2)}.
\]
Using \(\rho_d(n)\le n/d\), the contribution of the first term and the \(1/d\) term to
\[
\sum_{d\ge2}d^{-\varepsilon}\sum_{n\ge1}|C_n|\,|b_d(n)-b_d(n+1)|
\]
is at most
\[
3\left(\sum_{d\ge2}d^{-1-\varepsilon}\right)
\left(\sum_{n\ge1}\frac{\Psi(n)}n\right).
\]
For the divisibility contribution, put \(n+1=dk\). Since \(d\ge2\), one has \(dk-1\ge k\) and therefore \(\Psi(dk-1)\le\Psi(k)\). Its contribution is bounded by
\[
\sum_{d\ge2}d^{-\varepsilon}\sum_{k\ge1}
\frac{(dk-1)\Psi(dk-1)}{dk(dk+1)}
\le
\left(\sum_{d\ge2}d^{-1-\varepsilon}\right)
\left(\sum_{k\ge1}\frac{\Psi(k)}k\right).
\]
Thus the complete double sum is bounded by
\[
4\zeta(1+\varepsilon)\sum_{n\ge1}\frac{\Psi(n)}n<\infty
\]
for each fixed \(\varepsilon>0\). Uniformity of this double-sum bound as \(\varepsilon\downarrow0\) is neither claimed nor needed.

The boundary term \(C_Nb_d(N)\) tends to zero for every \(d\), so the justified interchange gives
\[
\sum_{n\ge1}g_nq_\varepsilon(n)
=-\sum_{d\ge2}\mu(d)d^{-\varepsilon}\langle\rho_d,g\rangle.
\]
Since \(f\perp\rho_d\), the right side is
\[
L\sum_{d\ge2}\mu(d)d^{-\varepsilon}\langle\rho_d,1\rangle.
\]

### 4. Exact constant mode

One has the elementary exact formula
\[
\langle\rho_d,1\rangle=\frac{\log d}{d}.
\]
For example, summation by parts gives the finite harmonic difference
\[
\sum_{n=1}^N\frac{\rho_d(n)}{n(n+1)}
=\frac{H_N-H_{\lfloor N/d\rfloor}}d-\frac{\rho_d(N)}{N+1},
\]
whose limit is \(\log d/d\).

Accordingly,
\[
J_\varepsilon:=-\sum_{d\ge2}\frac{\mu(d)\log d}{d^{1+\varepsilon}}
=-\frac{\zeta'(1+\varepsilon)}{\zeta(1+\varepsilon)^2}
\longrightarrow1.
\]
The series and its derivative identity converge absolutely for \(\varepsilon>0\).
The limit uses only the simple pole of \(\zeta\) at 1 with residue 1; equivalently write
\(\zeta(1+\varepsilon)=1/\varepsilon+h(\varepsilon)\), where \(h\) is analytic near zero.
No PNT-strength zero-free estimate is needed in this damping argument.

The preceding identity now reads
\[
\sum_{n\ge1}g_nq_\varepsilon(n)=-LJ_\varepsilon.
\]
Letting \(\varepsilon\downarrow0\) yields
\(\langle1,g\rangle=-L\). Since \(\langle1,1\rangle=1\) and \(f=g+L\),
\(\langle1,f\rangle=0\), as claimed.

### Remaining provider

The actual canonical residual has not been shown to satisfy this Dini envelope (or any adequate logarithmic special case). The theorem strictly enlarges the permissible regularity test class; it does not establish RH. The actual residual hypothesis is itself RH-equivalent, because RH makes the residual zero and zero satisfies the criterion.

The arithmetic coefficient positivity and upper bound are already represented by the existing Lean declarations in `RH/DampedMobiusCoefficients.lean`: `dampedDivisorCoefficient_eq_prime_product`, `dampedDivisorCoefficient_nonneg`, and `dampedDivisorCoefficient_le_one` (verify exact namespace/signatures before use). Feasible next formalization: exact summatory jump, linear bound, and uniform weighted variation bound; then formalize the Abel-primitive and absolute-interchange steps without claiming Hilbert membership of the infinite damped approximant.

## 2. Stronger variation constant proved in Lean

The proof above uses the safe constant 3. The new formal module proves the
stronger bound 2 directly. Put S_n=sum_(k<=n) a_epsilon(k), so 0<=S_n<=n.
The numerator of q_epsilon(n+1)-q_epsilon(n) is exactly

\[
n\,a_\varepsilon(n+1)-2S_n+n c_\varepsilon.
\]

It lies in [-2n,2n], giving

\[
\boxed{|q_\varepsilon(n+1)-q_\varepsilon(n)|
\le\frac{2}{(n+1)(n+2)}}.
\]

The formal statement takes any centering c in [0,1]. Its pointwise-limit
statement takes any nonnegative damping sequence tending to zero and any
centering sequence tending to zero. These are ordinary analytic parameters;
the theorem does not silently identify c with a zeta value or assume
Hilbert membership of an infinite sum.

Module: `RiemannResearch/RH/DampedMobiusPrimitiveVariation.lean`.
Principal declarations:

- `dampedPhysicalSum_step`
- `dampedPhysicalWeight_difference`
- `dampedPhysicalWeight_variation_le`
- `dampedPhysicalSum_tendsto_one`
- `dampedPhysicalPrimitive_pairing_tendsto`

The last theorem is exactly convergence of the absolutely convergent
primitive-side series. The identification of that series with the infinite
linear combination of legal-vector pairings is proved in the prose argument
above, and is not yet a Lean theorem in this continuation.

## 3. Exact source masses and the harmonic obstruction

Use the handoff's actual quantities, with M>=1:

\[
E_M=\|e-P_Me\|^2,\quad B_M=\|v_M-P_Mv_M\|^2,
\quad D_M=\|d_M\|^2,\quad s_M=\langle\operatorname{tail}v_M,Q_M\rangle.
\]

The existing exact identities B_M=D_M+E_M s_M^2 and
D_M=B_M E_(M+1)/E_M imply the newly formalized equality

\[
\boxed{\frac{E_M^2s_M^2}{B_M}=E_M-E_{M+1}}.
\]

Thus, with E_infinity the actual limiting first-head defect,

\[
\boxed{\sum_{M=1}^{\infty}\frac{E_M^2s_M^2}{B_M}
=E_1-E_\infty}.
\]

The endpoint E_infinity is retained. Exhausting all mass E_1 is equivalent
to density, so the identity alone does not establish the desired exhaustion.

There is also a useful necessary arithmetic condition. The repository
already supplies the actual upper bound

\[
0<D_M\le H_{M+1},\qquad H_j=\sum_{k=1}^j\frac1k.
\]

If density fails, capacity K_M tends to E_infinity^(-1)-2. Telescoping its
actual gains gives the exact finite value

\[
\sum_{M=1}^{\infty}\frac{s_M^2}{D_M}
=E_\infty^{-1}-2-K_1.
\]

Consequently the following implication and its RH corollary are formalized:

\[
\text{nondensity}\ \Longrightarrow\
\sum_{M=1}^{\infty}\frac{s_M^2}{H_{M+1}}<\infty,
\]

\[
\boxed{\sum_{M=1}^{\infty}\frac{s_M^2}{H_{M+1}}=+\infty
\ \Longrightarrow\ \mathrm{RH}}.
\]

The source nonsummability is explicitly an Open hypothesis. A lower bound
on D_M cannot justify the comparison needed to infer unweighted summability
of s_M^2; this result correctly uses an upper bound on the denominator.

Module: `RiemannResearch/RH/ScreeningSourceMass.lean`.
Principal declarations:

- `firstHeadSourceMass_eq_error_drop`
- `firstHeadSourceMass_hasSum`
- `firstHeadSourceMass_tsum_eq_iff_density`
- `firstHeadWindowGain_hasSum_of_not_density`
- `firstHead_harmonic_source_summable_of_not_density`
- `riemannHypothesis_of_firstHead_harmonic_source_not_summable`

## 4. What the finite-dilation Lean modules prove

Let S be a finite set of positive integers, w_h real signed weights, and Q a
positive common multiple of S. Define

\[
\eta(n)=\sum_{h\in S}w_h\mathbf1_{h\mid n}
\frac{\mu(n/h)}{n/h},
\quad F(M)=\sum_{h\in S}w_h\sum_{k\le M/h}\frac{\mu(k)}k.
\]

The coefficient value at n=0 is defined as zero. All coefficient bounds,
boundedness of F, and the PNT null limit F(M)->0 are supplied by proofs;
they are not left as research hypotheses.

At common cutoff QN, the actual physical charge is

\[
A_N=\sum_{h\in S}w_h R_{(Q/h)N}.
\]

The reversal Q/h is essential. The new theorem proves exactly

\[
\boxed{\lim_{N\to\infty}\|A_N\|^2=\sum_{n\ge1}\eta(n)^2}.
\]

Modules:

- `RiemannResearch/RH/FiniteDilationMobiusKernel.lean`
- `RiemannResearch/RH/FiniteDilationReciprocalCharge.lean`

Principal declarations:

- `finiteDilationMobiusKernel_square_energy_tendsto`
- `finiteDilationReciprocalCharge_sequence`
- `finiteDilationReciprocalCharge_norm_sq_eq_energy`
- `finiteDilationReciprocalCharge_norm_sq_tendsto`

This establishes the general finite physical limit required by the handoff,
including arbitrary mixed dilations. The remaining Euler-product evaluation
is elementary but is not included in the Lean statement.


## 5. Completing the all-dilation argument mathematically

## All-integer dilation certificates: rigorous continuation

This argument completes the mathematical derivation suggested in Section 5 of
the 2026-09-24 lateral-screening handoff. The generic finite-dilation kernel and
physical norm transfer are proved in the accompanying Lean modules
`FiniteDilationMobiusKernel.lean` and `FiniteDilationReciprocalCharge.lean`.
The coordinating verifier reports that both passed their coherent Lean check
and axiom checks; publication status is reported separately. The
Euler-product evaluation and the final innovation consequence below are prose
proofs here; this note does not label them as Lean-verified theorems.

### 1. A common-multiple realization, with the reversal explicit

Write
\[
 m(x)=\sum_{1\le n\le x}\frac{\mu(n)}n,
 \qquad R_K=\operatorname{reciprocalChargeRiesz}(K).
\]
For a finite set \(S\) of positive divisors of \(Q>0\) and fixed real weights
\(w_h\), put
\[
 F(x)=\sum_{h\in S}w_hm(\lfloor x/h\rfloor),\qquad
 \eta(n)=\sum_{\substack{h\in S\\h\mid n}}w_h
       \frac{\mu(n/h)}{n/h}.
\]
The exact identity \(F(x)=\sum_{n\le x}\eta(n)\) implies the required
quotient-window identity. Moreover
\[
 |\eta(n)|\le\frac{\sum_{h\in S}|w_h|h}{n},\qquad
 |F(x)|\le\sum_{h\in S}|w_h|,
 \qquad \lim_{x\to\infty}F(x)=0.
\]
Here the uniform bound \(|m(x)|\le1\) and the PNT consequence \(m(x)\to0\)
are the existing unconditional arithmetic inputs.

At common physical cutoff \(QN\), the exact integer identity
\[
 \left\lfloor\frac{\lfloor QN/k\rfloor}{h}\right\rfloor
 =\left\lfloor\frac{(Q/h)N}{k}\right\rfloor
 \quad(h\mid Q)
\]
identifies the quotient kernel with the physical vector
\[
 V_N=\sum_{h\in S}w_hR_{(Q/h)N}.
\]
The homogeneous quotient-kernel energy theorem therefore gives
\[
 \boxed{\lim_{N\to\infty}\|V_N\|^2=\sum_{n\ge1}\eta(n)^2.}
\]
The series converges absolutely by the displayed inverse-linear bound. This
formulation does not need a separately asserted symmetry under reversing the
dilation indices.

### 2. Divisor boxes and their exact arithmetic energy

For an arbitrary positive integer \(Q\), define
\[
 A_{Q,N}=\sum_{d\mid Q}\frac1dR_{dN}.
\]
Take \(S\) to be the positive divisors of \(Q\) and \(w_h=h/Q\) above.
The divisor bijection \(h\leftrightarrow Q/h\) gives precisely \(A_{Q,N}\).
The scalar coefficient is
\[
 \eta_Q(n)=\frac1{Qn}\sum_{h\mid\gcd(n,Q)}h^2\mu(n/h).
\]
Let
\[
 b_Q(n)=\sum_{h\mid\gcd(n,Q)}h^2\mu(n/h).
\]
This is a multiplicative function of \(n\): the two factors in its Dirichlet
convolution are \(h\mapsto h^2\mathbf1_{h\mid Q}\) and \(\mu\), both
multiplicative. For a prime \(p\), put \(L=v_p(Q)\). The local coefficients
are exactly
\[
 b_Q(p^e)=
 \begin{cases}
 1,&e=0,\\
 p^{2e}-p^{2e-2},&1\le e\le L,\\
 -p^{2L},&e=L+1,\\
 0,&e\ge L+2.
 \end{cases}
\]
This includes \(L=0\): the only nonzero terms are \(1,-1\).
For \(L\ge1\), finite geometric summation yields
\[
 \begin{aligned}
 p^{-2L}\sum_{e\ge0}\frac{b_Q(p^e)^2}{p^{2e}}
 &=p^{-2L}\left[
 1+(1-p^{-2})^2\sum_{e=1}^{L}p^{2e}+p^{2L-2}
 \right]\\
 &=1+p^{-2(L+1)}.
 \end{aligned}
\]
For \(L=0\) the same result is the immediate identity \(1+p^{-2}\).

Using unique prime factorization and nonnegativity to expand finite prime
products, then monotone convergence, gives
\[
 \sum_{n\ge1}\eta_Q(n)^2
 =\frac1{Q^2}\prod_p
       \left(\sum_{e\ge0}\frac{b_Q(p^e)^2}{p^{2e}}\right).
\]
Distribute \(Q^{-2}=\prod_{p\mid Q}p^{-2v_p(Q)}\) among its finitely many
prime factors. The preceding local computation proves
\[
 \boxed{
 \lim_{N\to\infty}\|A_{Q,N}\|^2
 =\mathcal E(Q)
 :=\prod_p\left(1+p^{-2(v_p(Q)+1)}\right).
 }
\]
Every product here is finite valued: its factors are bounded by \(1+p^{-2}\)
and \(\sum_p p^{-2}<\infty\). Equivalently,
\[
 \mathcal E(Q)=\frac{15}{\pi^2}
  \prod_{p\mid Q}
   \frac{1+p^{-2(v_p(Q)+1)}}{1+p^{-2}}.
\]
For \(Q=2^L\), this reproduces the earlier exact dyadic limit
\[
 \mathcal E(2^L)=\frac{12+3\,4^{-L}}{\pi^2}.
\]

### 3. An explicit sequence of certificates with limiting energy one

For \(D\ge1\), let
\[
 Q_D=\operatorname{lcm}(1,2,\ldots,D),\qquad L_p=v_p(Q_D).
\]
Then \(p^{L_p}\le D<p^{L_p+1}\) for \(p\le D\), and \(L_p=0\) for
\(p>D\). Thus the integers \(p^{L_p+1}\), as \(p\) ranges over all primes,
are distinct and all exceed \(D\). Consequently
\[
 \sum_p p^{-2(L_p+1)}
 \le\sum_{n>D}\frac1{n^2}
 \le\sum_{n>D}\frac1{n(n-1)}
 =\frac1D.
\]
The inequalities \(1+x\le e^x\) and \(x\ge0\) now give the explicit bound
\[
 1\le\mathcal E(Q_D)\le e^{1/D},
 \qquad
 \boxed{\lim_{D\to\infty}\mathcal E(Q_D)=1.}
\]
The exact product is the main result; the exponential estimate supplies a
simple certified accuracy for that limiting energy. It does not provide a
rate of convergence in the physical cutoff \(N\), uniform in \(D\).

### 4. The resulting unconditional innovation bound

Use the handoff notation
\[
 v_M=(M+2)\rho_{M+2}-(M+1)\rho_{M+1},\quad
 z_M=v_M-P_Mv_M,\quad B_M=\|z_M\|^2.
\]
Every charge \(R_{d(M+1)}\), \(d\ge1\), annihilates the actual finite legal
space by `reciprocalChargeRiesz_mem_finiteSpace_orthogonal` in
`ReciprocalChargeInnovations.lean`, because \(M+1\le d(M+1)\).
The same file's `reciprocalChargeRiesz_consecutive_biorthogonal` proves,
for every \(M\ge1\) and \(K>0\), the exact identity
\[
 \langle R_K,v_M\rangle=\mathbf1_{\{K=M+1\}}.
\]
For \(K=d(M+1)\), positivity of \(M+1\) makes \(K=M+1\) equivalent to
\(d=1\). In particular, every \(d>1\) contributes zero; the result is not
restricted to dyadic dilations. Since \(1\mid Q\) and its coefficient is
one, linearity and orthogonality to \(P_Mv_M\) give
\[
 \langle A_{Q,M+1},z_M\rangle=1:
\]
only the divisor \(d=1\), whose coefficient is one, contributes. Hence
\[
 1\le\|A_{Q,M+1}\|^2B_M.
\]
Given \(0<c<1\), choose \(D\) with \(\mathcal E(Q_D)<1/c\). Hold this
single \(D\), hence \(Q_D\), fixed. The norm limit from Section 2 gives
\(\|A_{Q_D,M+1}\|^2<1/c\) for all sufficiently large \(M\), whence
\(B_M>c\). Positivity handles \(c\le0\). Thus
\[
 \boxed{\forall c<1,\quad B_M>c\text{ eventually},}
 \qquad\text{equivalently}\qquad
 \boxed{\liminf_{M\to\infty}B_M\ge1.}
\]
The limits occur in the valid order: fix the finite certificate, let the
physical cutoff grow, then improve the certificate. No diagonal interchange
is used. This proves a lower limit, not \(B_M\to1\).

### 5. Consequences and the remaining RH obstruction

The verified full/tail identity from the handoff is
\[
 D_M=B_M\frac{E_{M+1}}{E_M}.
\]
Thus the all-dilation argument gives, for each \(c<1\), the eventual bound
\[
 D_M>c\frac{E_{M+1}}{E_M}.
\]
If density fails, \(E_M\) tends to a positive limit, so
\[
 \liminf_{M\to\infty}D_M\ge1.
\]
There is no contradiction. The exact positive-defect scalar model in the
handoff has \(B_M=1\), \(D_M\to1\), and \(E_M\to1/4\); it satisfies this
stronger denominator conclusion as well as all the displayed scalar
screening identities.

The new estimate does not prove the signed source accumulation
\[
 \sum_M\frac{s_M^2}{D_M}=\infty,
\]
nor does it prove the actual residual's centered physical-primitive bound.
Those remain the arithmetic providers needed by the RH implications. The
completed all-dilation argument strengthens an unconditional denominator
result; it does not establish unconditional RH.

## 6. The attempt to close RH, and what still fails

Two tempting closing arguments have now been tested.

1. **Nearly unit charge energy forces density.** It does not: even the exact
   scalar model in the handoff has B_M=1, D_M tending to 1, and a positive
   limiting defect. The new lower limit is compatible with that model.
2. **Signed damping and the elementary Euler product automatically regularize
   the actual residual.** They do not: the pairing theorem is a test-class
   statement. No estimate on H_r(n)-Ln has been obtained from the residual's
   arithmetic orthogonality. Its Dini envelope remains an explicit hypothesis.

The full primitive proof gives the improved sufficient condition

\[
\boxed{\exists L,C\in\mathbb R,\ p>1:\quad
|H_r(n)-Ln|\le\frac{Cn}{\log(2n)^p}\quad(n\ge1).}
\]

The source route gives the sufficient condition

\[
\boxed{\sum_{M\ge1}\frac{s_M^2}{H_{M+1}}=+\infty.}
\]

Neither displayed provider has been proved for the actual arithmetic sequence.
The original exact capacity condition sum s_M^2/D_M=+infinity is still the
necessary-and-sufficient target supplied by the repository. The harmonic
replacement is a sufficient condition; its converse has not been asserted.

The primitive Dini condition for the actual residual is itself RH-equivalent:
the proof supplies sufficiency, and under RH the residual is zero, which
satisfies the condition with L=0 and Psi=0. Therefore the improved envelope
must not be described as an unconditional estimate for r or as eliminating
the central difficulty.

## 7. Precise next work

- Formalize the fixed-epsilon absolute interchange after Abel summation and
  the exact constant-mode limit, then assemble the complete p>1 RH criterion
  using the already verified primitive-side limit. This is an extension of
  the verified implication, not a provider of its hypothesis.
- Formalize the local prime-power energy computation and Euler product for
  divisor-box certificates. The generic physical norm limit is now available.
- Focus new arithmetic research on the actual residual envelope or the actual
  harmonic-weighted source divergence. Further denominator positivity alone
  cannot close the demonstrated gap.
- Preserve the distinction between the limiting residual of the constant
  vector (used by the primitive theorem) and the first-head projection defect
  (used by the screening identities). Their roles are connected by the
  existing density criteria, not by identifying the two vectors.

## 8. Literature scope checked

Manzur, Noor and Quintero, *A Hardy space approximation supporting zero-free
half-planes for the zeta-function*, arXiv:2606.16097v1, Theorem 3.1, supplies
convergence in Hardy half-planes with boundary alpha>1. It does not supply
the critical-boundary or actual-residual estimate required here.
https://arxiv.org/html/2606.16097v1

Calderaro, Manzur, Noor and Santos, *Orthogonality questions in the Hardy
space related to zeta-zeros*, arXiv:2203.05030v3, is background for orthogonal
regularity exclusions. The derivations in this continuation were checked
directly; no claim of historical novelty is made.
https://arxiv.org/html/2203.05030v3

The new local proof sources are exported from `RiemannResearch.lean`; the
publication ledger is updated in `RiemannResearch/THEOREM_CATALOG.md`.


## 9. Verified code publication

The code checkpoint `job_s-dbN-EIFZTALEYly-TSKAxXs1zByx5M` succeeded:
all four affected modules built, `committed=true`, and `pushed=true`.
The build reported style/header warnings, not proof errors.

Code commit: `795dcb4b2ca46dc136252cd63218ec0675333508`.
https://github.com/Cnoack3/RiemannResearch/commit/795dcb4b2ca46dc136252cd63218ec0675333508

A report/catalog patch failed before the code checkpoint, so those documents
are completed in a separate documentation-only checkpoint. No Lean theorem
is changed by that documentation recovery. The successful four-module build
and the isolated axiom checks above remain the verification evidence.
