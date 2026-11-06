# Fixed-root Möbius cancellation and the actual displacement

The requested conclusion is the equality `QSquarefreeDisplacementRigidity.displacement = 0`, where both projections are the actual projections of the constant one onto the same closed squarefree physical span. This work does not establish that equality unconditionally.

## The exact fixed-root route

For a fixed squarefree root r, write S_r(X) for the ordinary Möbius sum on its ordered-prime descendants. The internally proved theorem in `PrimeTreeMertensImplication.lean` has the hypothesis

\[
\forall\varepsilon>0,\quad |S_r(X)|\le C_\varepsilon X^{1/2+\varepsilon}.
\]

The constants may depend on r and epsilon. The theorem proves Mathlib's `RiemannHypothesis` from these bounds. It supplies no proof of the bounds. The finite-prime deletion identities transfer them to the corresponding bounds for Mertens' function.

`PrimeTreeFixedRootDisplacement.displacement_eq_zero_of_fixedRoot_power_forall` follows this route to the actual equality d=0. Its type retains the preceding bounds and `Pareto.BaezDuarte.BaezDuarteMobiusApproximation`. The latter is the named published approximation theorem used by the current repository to pass from RH back to squarefree constant closure; it is not supplied by a checked provider here. Ordinary logical axioms reported by `#print axioms` do not remove these hypotheses from the theorem's type.

Báez-Duarte's constructive result is Proposition 3.1 of [arXiv:math/0205003](https://arxiv.org/html/math/0205003v1). It gives a damped Möbius approximation under RH. The existing formal bridge then transfers the approximation to the physical squarefree closure, making both projections equal to one.

## The exact obstruction to substituting displacement charges

Use the anchored physical sequence d(0)=0 and set

\[
b_m(d)=\sum_{a\mid m}\mu(m/a)\,[d(a)-d(a-1)].
\]

For every prime p not dividing n, the complete identity is

\[
b_{pn}(d)+b_n(d)
=\sum_{a\mid n}\mu(n/a)\,[d(pa)-d(pa-1)].
\]

The same formula holds for any real sequence. The right side is the additional term in the prime-deletion step. Radical compatibility of the first difference does not set it to zero: p is a new prime here.

For the actual matched displacement, the formal rigidity result is

\[
d=0\quad\Longleftrightarrow\quad
b_{pn}(d)=-b_n(d)\text{ for every prime }p\nmid n.
\]

The nontrivial direction first derives b_m=c mu(m). Möbius inversion then gives d(n)=c for every positive n. The established matched-projection boundedness theorem gives d=0. Consequently, assuming all these prime-deletion defects vanish would already assume a condition equivalent to the desired conclusion.

As an independent arithmetic check, Wolfram evaluated the complete defect identity for 142 coprime pairs on the exact rational legal vector g_2/3-2g_3/5. All complete defects were zero. These finite checks are separate from the formal proof. The single legal atom g_2 itself has b_1=1/2 and b_2=-1, so its prime-deletion sum at (p,n)=(2,1) is -1/2; ordinary legal-span membership does not give the Möbius sign rule.

## Direct cancellation target for the matched displacement

The relevant one-sided quantity is

\[
A_\sigma(H)=\sum_{m=1}^{H}[-\sigma b_m(d)]_+,
\qquad\sigma\in\{-1,1\}.
\]

The direct theorem `PrimeTreeLogChargeCriterion.displacement_eq_zero_of_polylog_charge_prefix` has the sufficient hypothesis

\[
\exists\sigma\in\{-1,1\},\ C\ge0,\ B\in\mathbb N,
\qquad A_\sigma(H)\le C(1+\log H)^B\quad\text{for all }H\ge1.
\]

It concludes d=0 without a Báez-Duarte hypothesis. The required estimate on the actual charges remains an open arithmetic obligation.

The proof first shows that this positive-prefix bound makes the adverse charges summable after division by (1+log m)^(B+1). More generally, `Analysis.summable_weighted_of_prefix_bound` establishes this implication for any decreasing weight in [0,1], retaining the finite boundary term in summation by parts. The exact physical remainder row is bounded by min(1,n/m). Its logarithmic estimate yields sigma*d(n)=O((1+log n)^(B+1)); the existing one-sided harmonic rigidity criterion then gives zero residual and zero displacement. Thus the proof allows one adverse sign to grow as any fixed polynomial in the logarithm.

The contrapositive is also formalized: if the actual displacement were nonzero, neither sign of its adverse charge prefix could obey any such global polynomial-logarithmic bound.

## An internal analytic step toward the published approximation bridge

`Analysis.GammaRatioVertical` proves the exact horizontal integral for the difference of log Gamma norms. The existing vertical digamma Stirling estimate then gives, for 0<a<=b<=1 and |t|>=1/2,

\[
\left|\frac{\Gamma(b+it)}{\Gamma(a+it)}\right|
\le e^{5(b-a)/t^2}|t|^{b-a}.
\]

`Analysis.SymmetricZetaRatio` transfers this through the exact zeta functional equation to

\[
|\zeta(\tfrac12-\varepsilon+it)|
\le e^{20\varepsilon/t^2}
\left(\frac{|t|}{2\pi}\right)^\varepsilon
|\zeta(\tfrac12+\varepsilon+it)|,
\qquad 0\le\varepsilon<\tfrac12,\quad |t|\ge1.
\]

This is unconditional. The multiplicative inequality retains both sides at zeros; the quotient corollary displays its nonvanishing hypothesis. Only the stated range of heights is asserted. This supplies a concrete high-frequency part of the symmetric estimate in Báez-Duarte's Lemma 2.2. It does not establish the separate finite-cutoff L2 limit or identify every damped Möbius series with the relevant Mellin inverse.

## Remaining obligations

1. **Open:** establish square-root-plus-epsilon cancellation for one ordinary Möbius subtree, if following the linked RH theorem.
2. **Open in Lean:** supply the complete Báez-Duarte approximation provider needed by the current reverse RH-to-closure bridge. The published proof is conditional on RH, so formalizing it does not discharge obligation 1.
3. **Alternative open target:** control one adverse sign of the actual displacement charges using both matched projection equations. Finite calculations and normalized subtree convergence do not establish a uniform bound over all horizons.

The known unconditional Mertens bounds of the form x exp(-a Phi(x)), with Phi(x)=o(log x), do not by themselves imply the required x^(1/2+epsilon) estimate for epsilon<1/2: their ratio to that power tends to infinity.
