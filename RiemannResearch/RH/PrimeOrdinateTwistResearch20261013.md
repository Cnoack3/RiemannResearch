# Primewise zero-ordinate twists and preservation of Dirichlet-series zeros

**Date:** 2026-10-13
**Status:** Self-contained paper argument and formalization handoff. The analytic theorems below have **not been Lean-verified**. Their proofs use the cited zero-ordinate equidistribution theorem and, for the counterexample, a cited Helson-zeta theorem. The formal ledger below identifies the exact local results; the global analytic arguments are kept separate.

## 1. What is being defined

Let \(\mathcal P\) denote the primes. For every prime \(p\), choose an ordinate \(\gamma_p>0\) of an actual nontrivial zero of the Riemann zeta function: there exists \(0<\beta_p<1\) with \(\zeta(\beta_p+i\gamma_p)=0\). No assertion that \(\beta_p=1/2\) is assumed.

Define
\[
a_p=e^{-i\gamma_p\log p},\qquad
c_\Gamma(n)=\prod_{p\mid n}a_p^{v_p(n)}\quad(n\ge1).
\]
The empty product gives \(c_\Gamma(1)=1\). This is the unique **completely multiplicative** function with the prescribed prime values, and \(|c_\Gamma(n)|=1\). Ordinary multiplicativity alone would not determine the prime-power values; the definition explicitly requires \(c_\Gamma(p^k)=a_p^k\).

Equivalently, the real-valued function
\[
\Phi_\Gamma(n)=\sum_{p\mid n}v_p(n)\gamma_p\log p
\]
is additive under multiplication of positive integers, and \(c_\Gamma(n)=e^{-i\Phi_\Gamma(n)}\). Only the classes of \(\gamma_p\) modulo \(2\pi/\log p\) affect this function.

For \(\Re s>1\), absolute convergence gives
\[
Z_\Gamma(s)=\sum_{n\ge1}\frac{c_\Gamma(n)}{n^s}
=\prod_p(1-a_pp^{-s})^{-1}.
\]
Its logarithm, with the Euler-product normalization, and logarithmic derivative are
\[
\log Z_\Gamma(s)=\sum_p\sum_{k\ge1}\frac{a_p^k}{kp^{ks}},
\qquad
-\frac{Z_\Gamma'(s)}{Z_\Gamma(s)}
=\sum_{n\ge1}\frac{\Lambda(n)c_\Gamma(n)}{n^s}.
\]
Thus the Dirichlet-convolution logarithm has coefficient \(a_p^k/k\) at \(p^k\), zero at other integers greater than one, and zero at one. These identities use complete multiplicativity; the fact that the chosen real numbers are zero ordinates is unnecessary for them.

If every \(\gamma_p=t\), then \(Z_\Gamma(s)=\zeta(s+it)\). More generally, the coefficient identity \(c_\Gamma(n)=n^{-it}\) holds exactly when
\[
(\gamma_p-t)\log p\in2\pi\mathbb Z\quad\text{for every prime }p.
\]
An arbitrary primewise choice produces a Helson zeta function, not automatically a single vertical translate.

## 2. Selecting distinct actual ordinates near arbitrary target phases

**Theorem A — selection theorem (paper proof, not Lean-verified).** Given arbitrary \(b_p\in\mathbb C\), \(|b_p|=1\), there are actual positive zero ordinates \(\gamma_p\), strictly increasing as the primes increase, for which
\[
|e^{-i\gamma_p\log p}-b_p|<p^{-2}.
\]

**Proof.** The unconditional equidistribution theorem recalled on the first page of Ford–Meng–Zaharescu [1] says that \(\alpha\gamma\bmod1\), with positive zero ordinates counted with multiplicity, is uniformly distributed for every fixed \(\alpha>0\). Take \(\alpha=\log p/(2\pi)\). Every nonempty open arc of possible phases is therefore visited at arbitrarily large ordinates. Enumerate the primes increasingly. At step \(j\), choose an ordinate above the previously chosen ordinate, with phase in the open \(p_j^{-2}\)-neighborhood of \(b_{p_j}\). Induction gives the assertion. Finite multiplicities and the finiteness of the zero count in bounded height intervals ensure that these arbitrarily high choices are distinct. \(\square\)

This is an existence argument. It gives no useful height bound for the chosen ordinates and does not assert that a natural enumeration of zeros already has this approximation property.

## 3. Exact correction coefficients

Let \(a,b\) be the completely multiplicative extensions of unit prime values \(a_p,b_p\). Define a multiplicative function \(h\) by
\[
h(1)=1,\qquad h(p^k)=(a_p-b_p)a_p^{k-1}\quad(k\ge1).
\]
Define \(\widetilde h\) by exchanging \(a_p\) and \(b_p\). At one prime the exact identity is
\[
a_p^k=b_p^k+
\sum_{j=1}^k b_p^{k-j}(a_p-b_p)a_p^{j-1}.
\]
It is the telescoping difference-of-powers identity. Consequently, with \(*\) denoting Dirichlet convolution,
\[
a=b*h,\qquad b=a*\widetilde h,\qquad
h*\widetilde h=\varepsilon.
\]
The last assertion follows either by cancellation in the convolution algebra, where \(a(1)=b(1)=1\) gives invertibility, or directly from the reciprocal local factors.

Indeed, for \(|x|<1\),
\[
\sum_{k\ge0}h(p^k)x^k
=\frac{1-b_px}{1-a_px}
=1+\frac{(a_p-b_p)x}{1-a_px}.
\]
Both denominator and numerator are nonzero. Useful elementary estimates are
\[
|a_p^k-b_p^k|\le k|a_p-b_p|,
\qquad
|a(n)-b(n)|\le\sum_{p\mid n}v_p(n)|a_p-b_p|.
\]
They follow by telescoping products of unit-modulus factors.

## 4. An analytic, nonvanishing multiplier

**Theorem B — divisor preservation (paper proof, not Lean-verified).** Suppose \(|a_p-b_p|\le p^{-2}\) for every prime. The Dirichlet series
\[
H(s)=\sum_{n\ge1}h(n)n^{-s},\qquad
\widetilde H(s)=\sum_{n\ge1}\widetilde h(n)n^{-s}
\]
converge absolutely on \(\Re s>0\), define holomorphic functions there, and satisfy \(H\widetilde H=1\). Moreover,
\[
Z_a(s)=Z_b(s)H(s)\qquad(\Re s>1).
\]

**Proof.** Fix \(\sigma>0\) and put \(\delta_p=|a_p-b_p|\). Since the prime values are unimodular,
\[
\sum_{k\ge1}|h(p^k)|p^{-k\sigma}
=\frac{\delta_pp^{-\sigma}}{1-p^{-\sigma}}
\le\frac{p^{-2-\sigma}}{1-2^{-\sigma}}=:q_p.
\]
The sum \(\sum_pq_p\) is finite by comparison with a convergent positive integer series. Nonnegative Euler products, obtained first over finitely many primes and then by monotone convergence, give
\[
\sum_{n\ge1}|h(n)|n^{-\sigma}
=\prod_p\left(1+
\frac{\delta_pp^{-\sigma}}{1-p^{-\sigma}}\right)
\le\exp\!\left(\sum_pq_p\right)<\infty.
\]
The identical bound holds for \(\widetilde h\). These bounds imply locally uniform convergence, hence holomorphy, on the open right half-plane. Absolute convergence justifies multiplication of the series; the convolution identities give \(H\widetilde H=1\) there and \(Z_a=Z_bH\) on their initial half-plane. \(\square\)

In particular, \(H\) and its reciprocal are bounded on each half-plane \(\Re s\ge\sigma>0\). Wherever \(Z_b\) has meromorphic continuation in a connected region inside \(\Re s>0\) reached from the initial half-plane, \(Z_a=Z_bH\) provides continuation with exactly the same zeros and poles, including multiplicities.

For comparison with the logarithmic approach, the normally convergent series
\[
L(s)=\sum_p\sum_{k\ge1}
\frac{a_p^k-b_p^k}{kp^{ks}}
\]
satisfies \(H=e^L\). The power-difference estimate bounds its absolute local contribution by \(\delta_pp^{-\sigma}/(1-p^{-\sigma})\). Thus no choice of a global principal logarithm is needed.

Combining Theorems A and B shows that **distinct actual zero ordinates can be assigned to the primes while preserving the zero/pole divisor of any target Helson zeta function in the right half-plane**.

There are two useful quantitative and finite consequences. Set
\[
M_\sigma=\sum_p\frac{\delta_pp^{-\sigma}}{1-p^{-\sigma}}.
\]
The logarithmic proof gives, uniformly for \(\Re s\ge\sigma>0\),
\[
|L(s)|\le M_\sigma,\qquad
e^{-M_\sigma}\le |H(s)|\le e^{M_\sigma}.
\]
Thus the comparison controls sizes as well as preserving zeros. The argument actually needs only convergence of \(M_\sigma\) for each positive \(\sigma\). Summability of \(\sum_p\delta_p\) is already sufficient; the convenient choice \(p^{-2}\) makes that requirement automatic.

If the prime assignments differ only on a finite set \(S\), no approximation requirement is needed at all:
\[
H(s)=\prod_{p\in S}\frac{1-b_pp^{-s}}{1-a_pp^{-s}}.
\]
Every factor and its reciprocal are holomorphic on \(\Re s>0\). In particular, changing finitely many prime phases of a common-ordinate character preserves exactly the shifted zeta zeros throughout that half-plane. The theorem above extends this finite modification principle to a controlled infinite modification. This also explains a limitation of finite symbolic experiments: changing a finite collection of local factors cannot move those zeros, although it changes coefficients, values, and logarithmic derivatives. An unrestricted infinite modification has substantially more freedom, as the counterexample below demonstrates.

## 5. A genuine RH equivalence from a Liouville target

Choose \(b_p=-1\), so that \(b(n)=\lambda(n)=(-1)^{\Omega(n)}\). Theorem A supplies distinct ordinates with \(|a_p+1|<p^{-2}\). Euler products give
\[
Z_\Gamma(s)=\frac{\zeta(2s)}{\zeta(s)}H(s)
\qquad(\Re s>1),
\]
and the right side continues meromorphically to \(\Re s>0\).

**Theorem C — RH equivalences (paper proof, not Lean-verified).** For any such selected assignment, the following are equivalent:

1. RH.
2. \(Z_\Gamma\) has holomorphic continuation throughout \(\Re s>1/2\).
3. For every \(\epsilon>0\),
   \[
   \sum_{n\le x}c_\Gamma(n)=O_\epsilon(x^{1/2+\epsilon}).
   \]

**Proof of the analytic equivalence.** On \(\Re s>1/2\), the numerator \(\zeta(2s)\) is holomorphic and nonzero, as is \(H\). A zero of \(\zeta(s)\) there therefore gives a genuine pole of the continued \(Z_\Gamma\). Conversely, absence of those zeros makes the quotient holomorphic; the pole of \(\zeta\) at one merely makes its reciprocal vanish. Functional-equation symmetry makes absence of zeros to the right of the critical line equivalent to RH.

**Proof of the summatory equivalence.** If a function \(B(x)=\sum_{n\le x}b(n)\) satisfies \(|B(x)|\le Cx^\alpha\), then
\[
\left|\sum_{n\le x}a(n)\right|
\le\sum_{d\le x}|h(d)|\,|B(x/d)|
\le Cx^\alpha\sum_d|h(d)|d^{-\alpha}.
\]
For every \(\alpha>0\), Theorem B makes the last sum finite. Exchanging \(a,b\) gives the converse. Hence the asserted bounds for \(c_\Gamma\) are equivalent to the classical Liouville square-root bounds, which are equivalent to RH. One can reduce that classical equivalence to the Möbius criterion using
\[
\lambda(n)=\sum_{d^2\mid n}\mu(n/d^2),\qquad
\mu(n)=\sum_{d^2\mid n}\mu(d)\lambda(n/d^2).
\]
For exponent \(\alpha>1/2\), both transfers are bounded by the convergent sum \(\sum_d d^{-2\alpha}\). \(\square\)

This is a rigorous reformulation, not a proof of the required cancellation. Phase matching preserves the RH obstruction instead of removing it.

## 6. Limits of independent zero selection

The zero-ordinate condition alone imposes no RH-like restriction on the new series. Andersson's Theorem 2 [2] gives, for \(f(s)=s-3/4\), a completely multiplicative unimodular target \(b\) and an entire zero-free function \(g\) such that \(Z_b=f/g\) initially on \(\Re s>1\). Thus \(Z_b\) continues to an entire function with a zero at \(3/4\). Applying Theorems A and B produces distinct actual-zero assignments whose continued \(Z_\Gamma\) also vanishes at \(3/4\).

This counterexample concerns the constructed Helson function, not the Riemann zeta function. It shows why obtaining cancellation for a conveniently selected assignment is insufficient: one must also prove the precise comparison that connects that assignment to the original zeta divisor. For the Liouville-matched assignment, that comparison is available, but the square-root cancellation remains exactly RH-strength.

## 7. Formal verification ledger

| Core Lean module | Formal scope | Main declarations |
|---|---|---|
| `Analysis/PrimeOrdinateTwist.lean` | 13 results: prime extension, multiplication and prime powers, dependence only on prime values, unit norms, exact absolute-convergence boundary | `primeExtension_mul`, `primeExtension_eq_iff`, `coefficient_prime_pow`, `LSeriesSummable_coefficient_iff` |
| `Analysis/PrimePhasePerturbation.lean` | 15 results: power and logarithmic coefficient discrepancy; exact local convolution and finite remainder; Euler correction bound and geometric series | `norm_logPrimePowerDifference_le`, `primePowerCorrection_convolution`, `localEulerCorrection_truncation`, `norm_localEulerCorrection_sub_one_le`, `hasSum_primePowerCorrection` |

All phase assignments in the first module are arbitrary real assignments. The zero-ordinate assumption is unnecessary for these algebraic and absolute-convergence facts. The selection of actual zero ordinates in Theorem A has not been formalized.

Server job `job_I9wnqOG0yffxqDz9qtkkV8V7AD6PZzYb` built both modules successfully (exit 0) and checked the six main declarations above for axioms. Every inspected declaration uses only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry` placeholders or project-local axioms in the new source.

The final server checkpoint of the containing commit is the project-level validation gate. Its terminal job result and published commit are reported with the delivered handoff; acceptance of a queued job alone is not verification.

Theorems A–C, infinite Euler-product continuation, classical RH equivalences, and the Helson counterexample are **paper proofs or cited mathematical inputs, not claims of completed Lean verification**. A verified algebraic module must not be represented as formal verification of these analytic theorems.

## References

1. K. Ford, X. Meng, A. Zaharescu, *Simultaneous Distribution of the Fractional Parts of Riemann Zeta Zeros*, arXiv:1511.06814. The first-page introduction states the unconditional fixed-frequency equidistribution result used here. <https://arxiv.org/pdf/1511.06814>
2. J. Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713 (2024), Theorem 2. Applied above only to the explicit target \(s-3/4\). <https://arxiv.org/pdf/2408.15713>

## Targeted corrections to the original handoff

1. The exterior determinant combines the ordinate phases into `(mn)^(-i gamma)`; that product phase remains. Statements claiming complete phase cancellation are replaced accordingly.
2. The averaged dyadic bound's derivative estimate must use `G_X(t)=X^(it)F_X(t)`. Its derivative contains `log(n/X)`, bounded on the smooth dyadic support. Applying the claimed derivative bound directly to `F_X` misses two logarithmic factors. This repairs the paper proof strategy; no Lean proof of the averaged bound is claimed here.
3. In the explicit formula, use distinct zeros with multiplicity weights, or a multiset without those extra weights. These conventions cannot be mixed.
4. The defining Dirichlet series is initially justified only for `Re s>1`. Values of its analytic continuation at a zero are not automatically values of a convergent series there.
5. Fixed-dimensional prime-torus equidistribution is retained. The more precise secondary-bias theorem in Ford–Meng–Zaharescu has additional hypotheses; those hypotheses are not omitted when that refinement is invoked.

This is a targeted salvage, not a fresh verification of every analytic statement in the original notes. The original self-isolation and dephasing estimates remain unproved.
