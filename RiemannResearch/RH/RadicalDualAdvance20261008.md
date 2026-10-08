# Radical dual extension and reciprocal cap: research continuation

8 October 2026. Base: `08b89f7b6c0bfb642f67e90cb2f269df20023822`.

## Recovered instruction and scope

The explicit recommended research prompt is §7 of
`RH/CriticalZeroMeanOneAdvance20261008.md`. It asks for actual arithmetic
estimates, complete optimizer tails, signed Schur gains, and preserved
negative squares. Later work has already supplied its mean-repair and
source-rate steps. The latest `RH/ExactOptimizerLeanStatus20261008.md`
identifies the remaining arithmetic target precisely:

\[
\frac{\Gamma_N^+}{e_N}\longrightarrow0\quad\text{possibly cofinally},
\qquad \Gamma_N=\delta_N-s_N,
\qquad e_Nm_2(N)=\varepsilon_N+\Gamma_N.
\]

Both positive squares in the signed difference are retained. This run
provides structural identities and a uniform operator cap. It does not
provide the required asymptotic saving or a proof of RH.

## The complete sparse radical dual family

Put \(Z=\zeta(2)\), \(Q(k)=1/(Zk^2)\) for positive integers, and
\(g_d(k)=(k\bmod d)/d\). Extend physical sequences by zero at site zero.
For \(m\ge2\), write \(a=\operatorname{rad}m\), the product of its distinct
prime divisors. Define

\[
f_m(k)=k^2\bigl(\mathbf1_{k=m}-\mathbf1_{k=m-1}
                    -\mathbf1_{k=a}+\mathbf1_{k=a-1}\bigr).
\]

For squarefree \(m\) this vector is zero. For nonsquarefree \(m\), its four
sites are distinct and positive. In particular \(f_4=(1,-4,-9,16)\), and
\(f_9\) has values \((4,-9,-64,81)\) at sites \((2,3,8,9)\).

The full residue jump, including the wrap term, is

\[
g_d(m)-g_d(m-1)=\frac1d-\mathbf1_{d\mid m}.
\]

If \(d\) is squarefree, \(d\mid m\iff d\mid a\). Consequently

\[
\langle f_m,g_d\rangle_Q=0,\qquad
\langle f_m,1\rangle_Q=0.
\]

Thus every literal squarefree legal approximant and its target residual
obey \(\Delta r(m)=\Delta r(a)\), where \(\Delta r(m)=r(m)-r(m-1)\).
This relation passes to strong limits by continuity of coordinate
evaluation. It applies to the actual finite projection optimizers without
any coefficient hypothesis. The formal span theorem is stated for arbitrary
sets of legal conductors, so it includes all finite cumulative stages and
their redundant zero-coordinate presentation.

The exact norms and marked target row are

\[
\|f_m\|_Q^2=\frac{m^2+(m-1)^2+a^2+(a-1)^2}{Z},
\quad
\langle f_m,Df_m\rangle_Q=\frac{2(m+a-1)}Z,
\]
\[
Z\langle f_m,D1\rangle_Q
=\frac1{a(a-1)}-\frac1{m(m-1)}.
\]

These displayed norm formulas are finite-support paper calculations;
the formal results below use the equivalent four-site difference functionals
directly and do not claim a bundled dual-vector span theorem.

## Exact reciprocal row and a trivial common kernel

Let \(D x(k)=x(k)/k\) and define the complete signed reciprocal row

\[
L_m(x)=\Delta(Dx)(m)-\Delta(Dx)(a)=Z\langle f_m,Dx\rangle_Q.
\]

For every \(x\) satisfying the unweighted radical relation, the exact recovery
identity is

\[
\boxed{\frac{x(m)}m=\Delta x(a)-(m-1)
                   \bigl(\Delta(Dx)(a)+L_m(x)\bigr).}
\]

No signed row or remainder is dropped. If both radical difference families
vanish, fix any \(b\ge2\), let \(m=b^{j+1}\), and put
\(A=\Delta x(b)\), \(B=\Delta(Dx)(b)\). Radical invariance at \(b\) and
\(m\) gives

\[
\frac{x(m)}m=A-(m-1)B,
\qquad \frac{x(m-1)}{m-1}=A-mB.
\]

Inverse-square summability implies \(x(k)/k\to0\). Since \(m\to\infty\),
the first equality forces \(B=0\), then \(A=0\). This holds for every
\(b\ge2\); the two equations at \(b=2\) give \(x(1)=x(2)=0\), and
induction gives \(x=0\).

`Analysis/RadicalDifferenceTotality.lean` proves the complete sequence
common-kernel theorem, its stronger power-invariance version, and the
summability provider. `RH/SquarefreeRadicalDifference.lean` realizes the
same common-kernel result using the actual QHilbert physical coordinates,
proves the literal residue-span relation, strong-limit preservation, and
the exact signed recovery formula.

At paper level this also proves density of
\(\operatorname{span}\{f_m,Df_m:m\text{ nonsquarefree}\}\) in \(L^2(Q)\):
its orthogonal complement is zero. Formal bundled density assembly remains
separate from the checked common-kernel theorem. Neither the unweighted
dual family alone nor prime independence is asserted to prove RH.

## What large-conductor rows actually detect

For an actual residual \(r_N\), \(\|r_N\|_Q\le1\). For fixed squarefree
\(a\ge2\) and \(m=a^j\), the exact rearrangement gives

\[
L_m(r_N)+\Delta(Dr_N)(a)
=\frac{\Delta r_N(a)-r_N(m)/m}{m-1}.
\]

Coordinate Cauchy bounds imply
\(|r_N(m)|/m\le\sqrt Z\) and
\(|\Delta r_N(a)|\le\sqrt Z(2a-1)\). Hence, uniformly in the stage,

\[
\boxed{|L_{a^j}(r_N)+\Delta(Dr_N)(a)|
       \le\frac{2a\sqrt Z}{a^j-1}.}
\]

This paper estimate is unconditional. The rows converge to the negative
base reciprocal difference; they need not converge to zero. Dividing by
\(\|f_m\|\asymp m\) can conceal a persistent defect. The exact recovery
identity is the appropriate object for further signed estimates.

## An actual uniform cap with the complete tail

The accompanying `RH/ReciprocalHeadCertificate20261008.md` proves on paper
that every vector orthogonal to \(g_2,g_3\) satisfies
\(\langle x,Dx\rangle_Q\le(3/7)\|x\|_Q^2\). The proof retains the two
negative head contributions, uses an exact rational head at sites 3 through
36, and controls the entire tail from site 37 onward. Positive-form Cauchy
then gives, for the actual stage indices \(N\ge2\),

\[
\boxed{0\le m_2(N)\le\frac9{49}<\frac3{16}},
\qquad
\Gamma_N\le\frac9{49}e_N-\varepsilon_N.
\]

`RH/ReciprocalHeadCertificate.lean` checks the finite rational certificate,
the residue trace bound, the signed Young inequality and the complete-tail
scalar assembly. The infinite weighted-Cauchy and actual operator assembly
are paper results, not kernel-verified specialized cap theorems.

## Mathematica checks using exact infinite residue weights

For reciprocal exponent \(s\ge2\) and representatives \(1\le r\le L\),
the full residue mass is

\[
\frac{(-1)^s\psi^{(s-1)}(r/L)}{(s-1)!\,ZL^s}.
\]

The representative of residue zero is \(L\). Pairwise periods are
\(\operatorname{lcm}(d,e)\); no infinite arithmetic tail is truncated.
Mathematica evaluated ordinary, cubic and quartic Gram matrices with 65-digit
working precision. Here the conductor cutoff is \(M\), so the Lean stage
index is \(M-1\).

| Conductor cutoff M | e | epsilon/e | Gamma/e |
|---:|---:|---:|---:|
| 3 | 0.06868528249 | 0.04666912043 | 0.003822639916 |
| 5 | 0.02723690104 | 0.01564226627 | 0.003181208054 |
| 10 | 0.01724870443 | 0.005745286192 | 0.005400507584 |
| 16 | 0.01277462109 | 0.002713854637 | 0.005348014545 |

The full identity \(M=\varepsilon+\Gamma\) agrees within working precision.
These are computational checks, not interval certificates or asymptotic
proofs. In particular the positive correction shows no monotone decline in
these stages.

## Remaining work

1. Formalize the infinite positive-tail and weighted-Cauchy assembly of the
   rational operator cap, retaining \(T-J\) and both negative head terms.
2. Construct the actual sparse dual vectors and formalize augmented-dual
   density from the checked common kernel.
3. Use the exact amplified rows or enlarged finite-head certificates to
   obtain a moving-stage estimate, rather than a fixed positive cap.
4. The required arithmetic conclusion remains cofinal
   \(\Gamma_N^+/e_N\to0\). The cap and totality do not discharge it.

## Sources

- User-directed exact optimizer continuation and the recovered GitHub prompt,
  8 October 2026, support the research target and exact-term policy.
- NIST DLMF 5.15.1 and 5.15.2 support the classical polygamma series and
  terminology: <https://dlmf.nist.gov/5.15>. The sparse-dual extension and
  rational cap are independently developed arguments here.
- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis*, <https://arxiv.org/abs/math/0607733>, supports
  the background approximation framework. It does not supply the positive
  signed-cancellation estimate used by the latest repository consumer.
