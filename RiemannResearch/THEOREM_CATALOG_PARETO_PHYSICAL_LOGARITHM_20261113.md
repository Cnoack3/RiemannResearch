# Physical Pareto logarithm: approximation proved, legality transfer open

13 November 2026. Source: Christian Noack's correction from Ramanujan packet
coordinates to the physical Pareto sequence, followed by confirmation of
the intended assertion.

## Correct object and status

Let
\[
 P(\{n\})=\frac1{n(n+1)},\qquad
 H=L^2(P),\qquad
 V=\overline{\operatorname{span}}^H\{g_d:d\ge2\},\qquad
 g_d(n)=\{n/d\}.
\]
The intended logarithm is the physical sequence
\[
 h(n)=(\log_*\mathbb1)(n)=
 \begin{cases}1/k&n=p^k,\ p\text{ prime},\ k\ge1,\\
 0&\text{otherwise}.
 \end{cases}
\]
In particular h(1)=0. Equivalently h(n)=Lambda(n)/log(n) for n>=2.
The assertion under investigation is h in V. It is recorded as
PhysicalLogLegality, not supplied by a theorem or an axiom.

The unconditional fact 0<=h<=1 proves h in H. It does not prove h in V.
The earlier Ramanujan packet obstruction concerns synthesis of h as
coefficients against different vectors; it does not refute this corrected
assertion. See THEOREM_CATALOG_RAMANUJAN_LOGARITHM_20261112.md for that
separate, still valid theorem.

No proof of h in V, of h in V implying mathbb1 in V, or of RH has been
obtained in this continuation.

## Prime cutoffs and their formal exponentials

For N>=0 define
\[
 h_N(n)=
 \begin{cases}1/k&n=p^k,\ p\le N,\\0&\text{otherwise},\end{cases}
 \qquad
 E_N(n)=\mathbf1_{\{\text{every prime divisor of }n\text{ is }\le N\}}.
\]
The condition for n=1 is vacuous, so E_N(1)=1. The Lean physical encoding
has a zero anchor at n=0, which carries no Pareto mass.

In the formal Dirichlet convolution algebra,
\[
 \exp_* h_N
 =\prod_{p\le N}\exp_*\left(\sum_{k\ge1}\frac{\delta_{p^k}}k\right)
 =\prod_{p\le N}\left(\sum_{k\ge0}\delta_{p^k}\right)
 =E_N.
\]
The proof is the formal power series identity
exp(sum_{k>=1} z^k/k)=(1-z)^{-1} at each prime and unique factorization.
For a fixed integer, the convolution exponential has only finitely many
nonzero positive-degree contributions, since h_N(1)=0. Likewise
exp_*h=mathbb1 coefficientwise.

This Euler-exponential identification is a mathematical derivation in this
note, not a new Lean theorem. The Lean module defines and verifies the
physical indicators directly. Prime cutoffs retain all powers of each
selected prime; they are not finite-support sequences or finite atom sums.

## Complete Pareto norm convergence

Because E_N takes only the values zero and one,
\[
 \boxed{\|\mathbb1-E_N\|_P^2
 =\sum_{\substack{n\ge1\\n\text{ not }N\text{-smooth}}}
       \frac1{n(n+1)}
 \le\sum_{n=N+1}^{\infty}\frac1{n(n+1)}
 =\frac1{N+1}.}
\]
Every integer between 1 and N is N-smooth, which justifies the inequality.
This is the complete infinite norm, with no omitted tail.

Moreover h_N=hE_N and 0<=h<=1, so
\[
 \boxed{\|h-h_N\|_P^2
 \le\|\mathbb1-E_N\|_P^2\le\frac1{N+1}.}
\]
Thus h_N tends to h and E_N tends to mathbb1 in the actual Pareto Hilbert
space. Both estimates and both norm limits are Lean-kernel checked.

## The remaining legality step

The two convergences do not show that E_N belongs to V. In particular:

1. The bounded coordinate multiplier C_N:f->E_N f is a contraction on H,
   but preservation of V has not been proved. The convergence C_N h->h
   and the assumption h in V do not establish C_N h in V.
2. No theorem here says that V is closed under Dirichlet convolution or
   convolution exponentiation.
3. The convolution identity is epsilon=delta_1, not mathbb1.
   Exponentiation includes this degree-zero term.

The already checked declaration
CoefficientStabilization.firstPoint_mem_iff_one_mem states exactly
\[
 \delta_1\in V\quad\Longleftrightarrow\quad\mathbb1\in V.
\]
Consequently it would be circular to make V a unital Dirichlet convolution
algebra by assuming its unit is legal. Omitting the unit does not solve
this: every positive convolution power of h vanishes at n=1, and
exp_*h-epsilon=mathbb1-delta_1.

The new predicate SmoothExponentialLegality requires E_N in V only for
all sufficiently large N. It deliberately does not require N=0 or N=1,
where E_N=delta_1. Closedness and the proved norm limit then give
\[
 \text{SmoothExponentialLegality}\ \Longrightarrow\ \mathbb1\in V
 \ \Longrightarrow\ \mathrm{RH}.
\]
The first implication is the direct closure argument; the second uses the
repository's existing RH reduction. This conditional theorem does not
discharge its legality hypothesis.

A concrete sufficient next construction is a finite atom sum F_N in V with
\[
 \|E_N-F_N\|_P\le(N+1)^{-1/2}
\]
for arbitrarily large N. Then
\[
 \|\mathbb1-F_N\|_P\le2(N+1)^{-1/2}\longrightarrow0.
\]
Deriving such legal sums from the assumed h in V remains open.

An alternative direct route would use the actual residual
r=mathbb1-proj_V(mathbb1). The user's premise gives <r,h>_P=0.
A proved strictly positive lower bound for <r,h>_P in terms of ||r||_P^2
would therefore settle the target. No such sign or coercivity bound is
asserted here.

## Why a general Hilbert algebra argument is unavailable

There is an elementary obstruction even in the ambient Pareto space:
Dirichlet convolution is not a bounded bilinear operation on H.

For M>=1 let f_M(2^k)=2^k/sqrt(M) for 1<=k<=M and let f_M vanish elsewhere.
Then
\[
 \|f_M\|_P^2=\frac1M\sum_{k=1}^M\frac{2^k}{2^k+1}\le1.
\]
If t_r is the number of pairs i,j in {1,...,M} with i+j=r, then
(f_M*f_M)(2^r)=2^r t_r/M and
\[
 \|f_M*f_M\|_P^2
 =\frac1{M^2}\sum_{r=2}^{2M}\frac{2^r}{2^r+1}t_r^2
 \ge\frac{2M^3+M}{6M^2}\ge\frac M3.
\]
Here sum t_r^2=M^2+2 sum_{j=1}^{M-1}j^2=(2M^3+M)/3.
Thus no uniform convolution bound follows from the Hilbert norm.
This finite-support counterexample is a paper proof, not a Lean declaration.
It does not rule out a special construction for h; it explains why a generic
continuous-algebra inference from h in V is insufficient.

## Lean declarations and evidence

Module: RH/ParetoPhysicalLogarithm.lean.
Namespace: RiemannResearch.RH.Pareto.PhysicalLogarithm.
Exported by the aggregate RiemannResearch.lean.

| Declaration | Result | Status |
| --- | --- | --- |
| physicalLog_prime_pow | h(p^k)=1/k | Kernel checked |
| physicalLog_eq_zero_of_not_primePow | Support is on prime powers | Kernel checked |
| physicalLog_bounds | 0<=h<=1 | Kernel checked |
| physicalLogHilbert_sequence | Actual Hilbert representation of h | Kernel checked |
| smoothSequence_exact_head | E_N(n)=1 for 1<=n<=N | Kernel checked |
| smooth_error_eq_rough_mass | Exact complete error mass | Kernel checked |
| smooth_error_sq_le | Squared error <=1/(N+1) | Kernel checked |
| smoothHilbert_tendsto_one | E_N tends to mathbb1 in H | Kernel checked |
| primeLog_error_sq_le_smooth_error | Log cutoff error <= smooth target error | Kernel checked |
| primeLog_error_sq_le | Log cutoff squared error <=1/(N+1) | Kernel checked |
| primeLogHilbert_tendsto | h_N tends to h in H | Kernel checked |
| one_mem_of_smooth_exponential_legality | Eventual legality implies mathbb1 in V | Kernel-checked conditional |
| riemannHypothesis_of_smooth_exponential_legality | Eventual legality implies RH | Kernel-checked conditional |
| PhysicalLogLegality | The user's intended h in V assertion | Proposition, no provider |
| SmoothExponentialLegality | Eventual legality of E_N | Open |
| PhysicalLogLegality -> SmoothExponentialLegality | Missing transfer | Not proved |

Focused verification succeeded with Bazel/BuildBuddy:
- Job: job_Vb3QNKbOHcyQ7iiH-1j7mT5q1fmGdGlL.
- Scope: //RiemannResearch/RH:ParetoPhysicalLogarithm.
- Checked source SHA-256: b03aea3829b6dac9ad40c235dd8b1997c8d41a3b4c364cb31d2a04dfd44552ee.
- BuildBuddy invocation: https://app.buildbuddy.io/invocation/f4d51a48-a4fd-4b1a-8e97-0be3c8eff4f1.
- Axiom audit of the conditional RH theorem: propext, Classical.choice,
  Quot.sound only. The source scanner noted the local classical decidability
  instance for Smooth; it introduces no axiom beyond Classical.choice.

Publication uses a separate full-project checkpoint. Its terminal job and
commit evidence are reported with the final result; this note does not
predeclare that checkpoint successful.
