# Displacement regularity: kernel estimates, weaker targets, and obstructions

The investigation began with the November 4, 2026 displacement results. The
five Lean declarations below were checked on November 5 against repository
base `2bffac8e49a4a507feed0497444f9a5c80536fd7`.

## Verification and open hypotheses

Lean proves an exact identity for the mean of a complementary kernel, three
consequences for bounded kernel columns, and a conditional polylogarithmic
smoothed-kernel criterion. The formalizations use the November 4 pairing
identity and the existing bounded-annihilator and polylogarithmic displacement
theorems. The axiom reports list `propext`, `Classical.choice`, and `Quot.sound`
for each declaration.

The Hilbert–Schmidt identity, sparse-prime example, comparison with a
one-dimensional legal subspace, and obstruction to increment-kernel norm
decay are analytic arguments in this note. For the actual displacement, an
upper bound sufficient to imply CRT continuity or RH remains open.

## Exact setup and the existing stronger endpoints

For positive integers put

\[
 Q(n)=\frac1{\zeta(2)n^2},\qquad P(n)=\frac1{n(n+1)},\qquad
 V=\overline{\operatorname{span}\{g_s:s\ge2,\ s\text{ squarefree}\}}^{L^2(Q)},
 \quad g_s(n)=\frac{n\bmod s}{s}.
\]

Let \(\Pi\) be the Q-orthogonal projection onto V, let \(f_P\) be the
P-projection of 1 onto the same physical closure, and write
\(r=1-\Pi1\), \(d=\Pi1-f_P\), \(r_P=r+d\), and
\(Bf(n)=f(n)/(n+1)\). The existing exact identities are

\[
 d=\Pi B(r+d),\qquad
 u:=Br_P-d\in V^\perp,
\]
\[
 \zeta(2)\langle1,u\rangle_Q
 =\zeta(2)\langle r,Br\rangle_Q+\|d\|_P^2.
\]

The final equality retains both nonnegative terms. The full-space annihilator
theorems are essential; the fixed-point equation alone is a generic projection
identity.

The proofs use the following existing declarations.

| File and declaration | Exact relevant content |
| --- | --- |
| `QSquarefreeDisplacementRegularity.displacement_eq_smoothed_kernel_pairing` | \(d(n)=\langle r_P,BK_n\rangle_Q\) |
| `QSquarefreeDisplacementRegularity.displacement_difference_radical` | \(\Delta d(n)=\Delta d(\operatorname{rad}n)\), \(n\ge2\) |
| `QSquarefreeDisplacementRigidity.residual_zero_iff_frequently_bounded_displacement_tail` | Cofinal boundedness of \(N\|\operatorname{tail}_N d\|_Q^2\) is equivalent to \(r=0\) |
| `QSquarefreeLogDisplacement.residual_zero_iff_eventually_polylog_displacement` | For each fixed integer \(m\ge0\), \(d(n)=O((6+\log n)^m)\) is equivalent to \(r=0\) |
| `QSquarefreeLogDisplacement.residual_zero_iff_frequent_log_displacement_tail` | Cofinal boundedness of \(N(6+\log N)^{-k}\|\operatorname{tail}_N d\|_Q^2\), for any fixed integer \(k\ge0\), implies \(r=0\) |
| `QSquarefreeStretchedDisplacement.exists_residual_zero_iff_frequently_bounded_stretched_displacement_tail` | A supplied positive stretched exponent gives a still weaker complete-tail criterion |

Thus a uniform bound on \(\|BK_n\|_Q\) is more than is needed. Either of
the following remains a valid sufficient arithmetic target, for one fixed m:

\[
 |\langle r_P,BK_n\rangle_Q|=O((6+\log n)^m),
 \qquad \|BK_n\|_Q=O((6+\log n)^m).
\]

The first retains the actual directional cancellation and is preferable when
available. The Lean theorem `residual_zero_of_smoothed_kernel_polylog_bound` combines
the second estimate with the existing polylogarithmic displacement theorem.
Obtaining either estimate for the actual kernels remains open.

## Unconditional kernel trace identity and its exact remainder

Let \(e_n=\mathbf1_{\{n\}}/\sqrt{Q(n)}\),
\(E_n=e_n/\sqrt{Q(n)}\), \(K_n=\Pi E_n\),
\(\kappa_n=\|BK_n\|_Q\), and
\(\alpha_m=\langle\Pi e_m,e_m\rangle_Q=\|\Pi e_m\|_Q^2\in[0,1]\).
All sums here start at 1; Lean's artificial zero coordinate is omitted.

The following exact identities hold for **every** orthogonal projection on
this Hilbert space, without squarefree arithmetic or RH:

\[
 \boxed{\sum_{n\ge1}Q(n)\kappa_n^2
 =\|B\Pi\|_{\mathrm{HS}}^2
 =\sum_{m\ge1}\frac{\alpha_m}{(m+1)^2}.}
\]
\[
 \boxed{\sum_nQ(n)\kappa_n^2+
 \sum_m\frac{1-\alpha_m}{(m+1)^2}=\zeta(2)-1.}
\]

Proof: \(\sqrt{Q(n)}BK_n=B\Pi e_n\). Parseval, self-adjointness of
\(\Pi\), and Tonelli for nonnegative double sums give
\(\sum_n\|B\Pi e_n\|^2=\sum_m(m+1)^{-2}\|\Pi e_m\|^2\).
The second summand in the second equality is exactly
\(\|B(I-\Pi)\|_{\mathrm{HS}}^2\). This proves convergence and retains
the complete complement contribution.

Consequently

\[
 \sum_n\frac{\kappa_n^2}{n^2}
 \le\zeta(2)(\zeta(2)-1),\qquad \boxed{\kappa_n=o(n)}.
\]

An alternative proof uses compactness of B and weak convergence of \(e_n\)
to zero. A quantitative finite/tail split, with no omitted tail assumption, is

\[
 \kappa_n^2\le
 \sum_{1\le m\le M}\frac{Q(m)|K_m(n)|^2}{(m+1)^2}
 +\frac{\zeta(2)n^2}{(M+2)^2}.
\]

It uses \(K_n(m)=K_m(n)\), and every fixed \(K_m\in L^2(Q)\) has
\(K_m(n)/n\to0\). None of these estimates supplies a polylogarithmic
rate. Weighted square summability permits unbounded functions such as
\(n^{1/4}\), and does not force a cofinal bounded scaled tail.

## A weaker column-by-column regularity criterion

For each fixed m define \(u_m=E_m-K_m\in V^\perp\). There is an exact
identity

\[
 \boxed{\langle1,u_m\rangle_Q=r(m).}
\]

If \(K_m(n)\) is bounded as a function of n, then \(u_m\) is bounded,
because \(E_m\) is supported at one coordinate. The existing
`QSquarefreeResidualTail.bounded_annihilator_mean_eq_zero` therefore gives
\(r(m)=0\). Hence

\[
 \boxed{[\ \forall m\ \exists C_m<\infty\ \forall n,
 |K_m(n)|\le C_m\ ]\quad\Longrightarrow\quad r=0.}
\]

There is no uniformity requirement on \(C_m\). The strong smoothed-kernel
bound implies this premise by kernel symmetry and bounded evaluation of
\(BK_n\), but the column criterion does not require that stronger bound.
Conversely, \(r(m)\ne0\) forces that particular column to be unbounded.
No nonzero residual coordinate is asserted to exist.

A still weaker analytic variant permits, separately for each m, cofinal
boundedness of \(N\|\operatorname{tail}_N K_m\|_Q^2\): past m the
tail of \(u_m\) is the negative of the tail of \(K_m\), contradicting
the existing annihilator escape theorem if \(r(m)\ne0\). Constants and
cofinal sequences may depend on m. The argument for the cofinal variant is analytic. For a bound on a single
column, the checked theorem concludes precisely that the corresponding
residual coordinate vanishes.

## Preserve cancellation before taking norms

Let \(A=\Pi B|_V\), so \(\|A\|\le1/2\), and let
\(M=(I_V-A)^{-1}\). The fixed point gives
\(d=M\Pi Br\). Since A and M are self-adjoint on V,

\[
 \boxed{d(n)=\langle r,L_n\rangle_Q,\qquad
 L_n=(I-\Pi)BMK_n.}
\]

This is an exact residual-sensitive kernel; the \(V\)-component of
\(BMK_n\) is removed before any norm estimate. It supplies a candidate
direction for estimates, not a proven bound. Also, for every real c,

\[
 (1-c)d(n)=\langle r_P,(B-cI)K_n\rangle_Q,
\]

because \(\langle r_P,K_n\rangle_Q=d(n)\). Dividing requires \(c\ne1\).

## Increment decay and a positive lower bound at powers of two

For a radical-compatible physical sequence f, \(\Delta f(n)\to0\)
forces f to be constant on positive integers. Indeed, for fixed squarefree
\(s\ge2\), \(\Delta f(s^k)=\Delta f(s)\) for every \(k\ge1\).
Letting k tend to infinity gives zero, and radical reduction covers every
\(n\ge2\). Applied to d, constancy implies boundedness, hence \(r=d=0\). The
repository independently formalized the implication from increment decay to RH
in `QSquarefreePrimeLocalTests.riemannHypothesis_of_difference_tendsto_zero`
(commit `400ebec5`).

Thus it would suffice to prove the directional estimate

\[
 \langle r_P,B(K_n-K_{n-1})\rangle_Q\longrightarrow0.
\]

However, its norm-majorant version is impossible. Since every f in V obeys
the radical recurrence, the Riesz kernels obey

\[
 K_n-K_{n-1}=K_{\operatorname{rad}n}-K_{\operatorname{rad}n-1}.
\]

In particular the difference equals \(K_2-K_1\) at \(n=2^k\), and
\(\langle g_2,K_2-K_1\rangle_Q=-1/2\). Because B is injective,

\[
 \|B(K_{2^k}-K_{2^k-1})\|_Q
 =\|B(K_2-K_1)\|_Q>0\qquad(k\ge1).
\]

This rules out \(\|B(K_n-K_{n-1})\|_Q\to0\) unconditionally for the
actual full V. It does not rule out decay of the particular scalar pairings.

## Explicit legal counterexample, with arbitrarily slow unbounded growth

Choose primes \(p_1\ge5\), \(p_{j+1}\ge4p_j\), and put

\[
 A_0=\sum_jp_j^{-1},\qquad
 F(n)=\sum_jg_{p_j}(n)=A_0n-\sum_j\lfloor n/p_j\rfloor.
\]

The floor sum is finite for each n. Splitting the norm sum at p gives

\[
 \|g_p\|_Q^2\le\frac2{\zeta(2)p},\qquad
 \sum_j\|g_{p_j}\|_Q\le2\sqrt{\frac2{\zeta(2)p_1}}.
\]

Thus the series converges in V and at every physical coordinate. Exactly,
\(\Delta F(n)=A_0-\#\{j:p_j\mid n\}\), which depends only on the
radical. If \(J=\#\{j:p_j\le n\}\), then

\[
 0\le F(n)\le J+\frac{4n}{3p_{J+1}}<J+\frac43.
\]

This is \(O(\log n)\). For any nondecreasing \(\omega(n)\to\infty\),
choose additionally \(\omega(p_j)\ge j+2\); then
\(F(n)\le\omega(n)\) for \(n\ge p_1\). Increasing \(p_1\) makes
\(\|F\|_Q\) as small as prescribed. Geometric separation still gives
sublinear growth, regardless of the chosen envelope.

For \(N_J=\prod_{p\le p_J}p-1\), the CRT images tend to \(-1\), while

\[
 F(N_J)\ge J-\sum_{j\le J}p_j^{-1}\longrightarrow\infty.
\]

Therefore legal membership, radical recurrence, and sublinear growth—even
arbitrarily slow unbounded growth—do not force CRT continuity. This F is not
the actual displacement and does not satisfy its full-V normal equations.
It does not refute the valid actual-displacement polylogarithmic criterion.

## Exact projection equations on a smaller legal subspace are insufficient

This stronger countermodel also isolates the role of the full legal closure.
Let \(v_\varepsilon=g_3+\varepsilon F\) with the sparse F above, and let
\(U_\varepsilon=\operatorname{span}(v_\varepsilon)\subset V\). For all
sufficiently small positive \(\varepsilon\), the Q and P projection
coefficients of 1 onto this line differ.

Here is a rational check at \(\varepsilon=0\). Put
\(q_a=\sum_{k\ge0}(3k+a)^{-2}\) and
\(p_a=\sum_{k\ge0}[(3k+a)(3k+a+1)]^{-1}\), \(a=1,2\).
The projection coefficient is \(H(t)=3(1+2t)/(1+4t)\), strictly
decreasing, with \(t_Q=q_2/q_1\) and \(t_P=p_2/p_1\). Integral tails give

\[
 q_1\ge17/16,\quad q_2\le1667/4800<17/48,
 \qquad p_2\ge77/360,\quad p_1\le1817/2940<77/120.
\]

Thus \(t_Q<1/3<t_P\), so the coefficients satisfy
\(a_Q(0)>15/7>a_P(0)\). Continuity in \(\varepsilon\) preserves the
strict gap. Their displacement is a positive multiple of
\(v_\varepsilon\), so it is unbounded, legal, radical-compatible, and
\(O(\log n)\). Nevertheless it satisfies exactly

\[
 d_\varepsilon=\Pi_{U_\varepsilon}B(r_\varepsilon+d_\varepsilon),
 \qquad r_\varepsilon\perp_Q U_\varepsilon.
\]

For this line,
\(K_n^U=v_\varepsilon(n)v_\varepsilon/\|v_\varepsilon\|_Q^2\), so
\(\|BK_n^U\|_Q\) is unbounded too. This is **not** a counterexample for
projection onto the full V. The full-V annihilator theorem fails for this
smaller space and is precisely the extra information that must be used.

## Open estimates for the actual kernels

None of the following has been proved for the actual full-V kernels:

1. A uniform or polylogarithmic bound for \(\kappa_n\).
2. A polylogarithmic bound for the actual pairings \(\langle r_P,BK_n\rangle_Q\).
3. Boundedness of every fixed column \(K_m\), with separate constants.
4. Decay of the actual increment pairings, or a sufficient complete-tail bound.

The mathematical advance is a clearer set of targets, an unconditional trace
identity, and exact obstructions to tempting intermediate estimates. The
arithmetic upper bound needed to discharge the RH criterion remains missing.

The five Lean declarations and their exact scope appear in
`THEOREM_CATALOG_DISPLACEMENT_REGULARITY_20261104.md`. The trace identity,
sparse-prime series, residual-sensitive resolvent identity, and proof of the
increment norm obstruction are paper deductions. Finite rational arithmetic
checked the five displayed numerical comparisons or differences used in
developing the bounds and 1,999 finite residue-increment identities.

## Sources and scope

- [Inspected repository snapshot](https://github.com/Cnoack3/RiemannResearch/tree/6840ed95bacd5adda1b8865aaeacee09db70ba39).
- [November 4 regularity module](https://github.com/Cnoack3/RiemannResearch/blob/6840ed95bacd5adda1b8865aaeacee09db70ba39/RiemannResearch/RH/QSquarefreeDisplacementRegularity.lean).
- [Existing logarithmic displacement rigidity](https://github.com/Cnoack3/RiemannResearch/blob/6840ed95bacd5adda1b8865aaeacee09db70ba39/RiemannResearch/RH/QSquarefreeLogDisplacement.lean).
- [Existing bounded-annihilator theorem](https://github.com/Cnoack3/RiemannResearch/blob/6840ed95bacd5adda1b8865aaeacee09db70ba39/RiemannResearch/RH/QSquarefreeResidualTail.lean).
- [Bhaskar Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis (2006)](https://arxiv.org/abs/math/0607733): the final squarefree-span remark and equivalent-weight observation support the published RH criterion. The inspected Lean bridge supplies the forward direction used here; a formal reverse provider is not claimed.

The trace calculation uses standard Parseval/Tonelli reasoning; the counterexamples
and reductions were developed for this investigation. No priority or novelty
claim is made.
