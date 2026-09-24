# Nyman–Beurling: subpower budget and source audit
Date: 2026-09-24

The unconditional Riemann hypothesis has **not** been proved. This continuation
establishes a stronger sufficient condition in Lean and an unconditional bound
on exactly the same finite arithmetic quantity. It uses the existing theorem
catalog, Wolfram calculations, and primary-source research. The unresolved
arithmetic hypothesis remains explicit.

## The actual finite quantity

For positive integers N and k, put
\[
m_N=\sum_{d=1}^{N}\frac{\mu(d)}d,\qquad
U_N(k)=1+\sum_{d=2}^{N}\mu(d)\frac{k\bmod d}{d},
\]
and
\[
B_N=Nm_N^2+\sum_{k=N+1}^{N^2}\frac{U_N(k)^2}{k(k+1)}.
\]
The middle sum is empty when its upper endpoint is smaller than its lower
endpoint. These are signed Möbius sums before squaring; no absolute-value
majorant replaces their internal cancellation.

The existing finite-window module retains the complete physical norm:
\[
\|U_N\|_P^2\le B_N+1,\qquad
\|f\|_P^2=\sum_{k\ge1}\frac{f(k)^2}{k(k+1)}.
\]

## New verified implications

RawMobiusSubpowerCriterion.lean connects this budget to the existing exact-head
Mellin obstruction. The legal canonical approximant has physical values
\[
F_N(k)=\sum_{d=1}^{N}\mu(d)\lfloor k/d\rfloor
 -(N+1)m_N\lfloor k/(N+1)\rfloor,
\]
and equals 1 for \(1\le k\le N\). Its actual norm satisfies
\[
\|F_N\|_P^2\le12B_N+8.
\]
The proof controls the boundary correction by \(4Nm_N^2\), with no
sign-crossing premise, and identifies the critical continuous energy with
the Pareto norm.

Consequently every hypothetical zeta zero \(\rho\ne1\) with
\(\beta=\Re\rho>1/2\) forces
\[
\frac{2\beta-1}{4|\rho|^2}(N+1)^{2\beta-1}\le12B_N+8
\quad(N\ge3).
\]
This follows from the already catalogued weighted Cauchy–Schwarz exact-head
obstruction, not from an assumed zero-free region.

Lean therefore proves Mathlib's RiemannHypothesis from
\[
\forall\varepsilon>0\quad\exists C_\varepsilon\in\mathbb R\quad
\text{cofinally many }N:\quad
B_N\le C_\varepsilon(N+1)^\varepsilon.
\]
Each exponent may use its own cofinal set. The theorem is
riemannHypothesis_of_frequently_subpower_raw_square_budget.
Its hsub is **Open**. The proof excludes right-half-strip zeros by comparing
powers and then uses the zeta functional equation.

## The unconditional provider and its precise limit

RawMobiusBudgetSublinear.lean uses the catalog's actual PNT consequences,
canonicalMobiusHilbert_sublinear and mobiusReciprocalSum_tendsto_zero.
It proves
\[
B_N\le4\|F_N\|_P^2+4+9Nm_N^2,
\qquad
\lim_{N\to\infty}\frac{B_N}{N}=0.
\]
The latter theorem, rawMobiusSquareBudget_sublinear, has no arithmetic
hypothesis.

Sublinear growth does not imply the cofinal subpower estimates above:
the comparison sequence \(\sqrt N\) is sublinear and fails the required
estimate for \(\varepsilon=1/4\). This is a logical comparison, not a claim
about the actual Möbius budget.

Other catalog results were checked for applicability. The bounded
reciprocal-charge Riesz vectors in MobiusQuotientEnergy are different
vectors from \(U_N\); their norm bound does not control this middle window.
MobiusReciprocalNonvanishing rules out positive cutoffs with \(m_N=0\).
MobiusSignCrossingBridge supplies finite crossing estimates, with
cofinal sign changes still external to that Lean module.

## Literature audit

- [Gallardo-Gutiérrez–Seco, arXiv:2206.02654v6](https://arxiv.org/html/2206.02654v6),
  Theorem 3.1, supplies a conditional Möbius-kernel route. It cites
  S. Selberg's 1955 theorem on infinitely many reciprocal-Möbius sign
  changes. Crossings supply small reciprocal heads, but do not supply
  the full middle-window energy estimate. The new subpower implication
  needs no such cutoff theorem.

- [Burnol, arXiv:math/0202166](https://arxiv.org/pdf/math/0202166),
  Lemma 4.1 and Theorem 4.2, gives another precise target:
  \[
  f_\varepsilon(t)=\sum_{n\ge1}\mu(n)n^{-\varepsilon}\{1/(nt)\}.
  \]
  Membership in \(L^2(0,\infty)\) is unconditional for
  \(\varepsilon\ge1/2\). Membership for a positive sequence
  \(\varepsilon\downarrow0\) implies RH; no common norm bound is required.
  The smaller-parameter membership is not supplied by the unconditional
  result. Burnol also distinguishes the arithmetic function from the
  inverse Mellin transform of an unconditionally square-integrable
  symmetric zeta quotient. Identifying them cannot be assumed.

- [Maier–Rassias, arXiv:1705.09921](https://arxiv.org/pdf/1705.09921),
  Theorem 1.1, treats linear Möbius sums with a cotangent/Estermann kernel
  in separated coefficient-to-denominator ranges. This does not directly
  bound the truncated quadratic energy defining \(B_N\).
  The retrieved [2018 version](https://arxiv.org/html/1806.05070v1)
  also requires an audit before import: its displayed Lemma 6.1 bound
  contradicts periodicity when both dilation indices equal m.
  No claim is made here about corrections in another version.

- Rational-point normalization matters. With ordinary fractional part,
  the displayed series \(\sum_l(1-2\{la/q\})/l\) has a divergent harmonic
  contribution. The normalized Bernoulli convention in
  [Balazard–Martin, arXiv:1305.4395](https://arxiv.org/pdf/1305.4395),
  page 4, subtracts the integer indicator. For reduced a/q, the exact
  finite discrepancy is \(H_{\lfloor M/q\rfloor}/q\).
  A rational kernel cannot be imported using the uncorrected series.

- [Manzur–Noor–Quintero, arXiv:2606.16097v1](https://arxiv.org/html/2606.16097v1),
  available in 2026, proves Hardy convergence for \(\alpha>1\).
  Its critical-region computations do not prove convergence down to
  \(\alpha=1/2\).

- [Álvarez Cruz–Álvarez Gutiérrez, arXiv:2606.22562v1](https://arxiv.org/html/2606.22562v1)
  proposes a Colombeau reformulation. A claimed general step in Section 2,
  from distributional association to weak \(L^2\) convergence, is
  insufficient as stated. For nonzero smooth \(\psi\) supported in (1,2),
  \(u_\varepsilon(x)=\varepsilon^{-1}\psi(x/\varepsilon)\) vanishes
  eventually on every compact subset of (0,1), while
  \(\|u_\varepsilon\|_2^2=\varepsilon^{-1}\|\psi\|_2^2\) for \(0<\varepsilon<1/2\).
  It is locally negligible and distributionally zero, yet its unbounded
  norms prevent weak \(L^2\) convergence along \(\varepsilon\to0\).
  This is our direct counterexample to that general implication, not a
  Lean theorem in this batch. An appropriate global bound would need
  a separate proof.

## Verification

Wolfram checked the canonical/raw identity exactly at selected finite
cutoffs N = 3, 5, 10, 20, 40, and checked rational-centering discrepancies
at three finite rational examples. These are finite consistency checks,
not proofs of asymptotic estimates.

Lean verified the source batch with only propext, Classical.choice,
and Quot.sound in the printed principal theorem dependencies.
No sorry, added axiom, or assumption of RH is used. The conditional
RH theorem still has its explicit arithmetic hsub premise.
The modules are exported through RiemannResearch.lean, and their
established/open status is recorded in THEOREM_CATALOG.md.
