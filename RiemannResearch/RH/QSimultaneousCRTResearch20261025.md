# Applying CRT simultaneously to all squarefree atoms

Date: 2026-10-25. Source: Christian's request to use the most general CRT
simultaneously on every squarefree atom, or an infinite linear combination,
to prove constant-target membership.

## Outcome

The requested target membership is not proved. The formal development gives
an exact global CRT change of generators, a decisive obstruction to unordered
atomic summation, and an exact analysis of legally projected CRT cylinders.
These do not disprove RH or constant-target membership in the closed span.

Write \(H=\overline{\operatorname{span}}\{g_d: d\ge2,\ d\text{ squarefree}\}\),
with \(Q(n)=1/(\zeta(2)n^2)\) on positive integers. Thus H is already closed.
The repository's names are `qSquarefreeCRTSpan.topologicalClosure` and
`ZetaTwoOptimizerStage.closure`, whose equality is already proved.

## 1. Applying the finite CRT identity to every squarefree atom

For each squarefree \(d\), take the canonical integers
\(a_{d,p}=(d/p)^{-1}\bmod p\), for primes \(p\mid d\). Put
\[
A_d=\sum_{p\mid d}a_{d,p}g_p,\qquad
C_d(n)=\left\lfloor\sum_{p\mid d}a_{d,p}g_p(n)\right\rfloor.
\]
The existing canonical CRT certificate proves \(g_d=A_d-C_d\).
The new `QSimultaneousCRT.canonicalCarry_sequence` identifies the encoded
vector with this literal floor function.

Applying these identities to the entire dictionary gives the exact equality
\[
\operatorname{span}\{g_d:d\ge2\text{ squarefree}\}
=
\operatorname{span}\{g_p:p\text{ prime}\}
+\operatorname{span}\{C_d:d\ge2\text{ squarefree}\}.
\]
This is `squarefreeSpan_eq_prime_sup_carry`; the norm closures are equal too.
No carry is dropped. For every finite coefficient family,
\[
\sum_{d\in D}c_dg_d
=\sum_{d\in D}c_dA_d-\sum_{d\in D}c_dC_d.
\]
This is `finite_synthesis_identity`. Regrouping the prime terms is legitimate
in a finite sum. An infinite regrouping requires its own convergence proof.

## 2. An unordered sum of individual atoms cannot represent one

A new unconditional negative result is:
\[
\boxed{\text{For every fixed family }(c_d)_{d\ge2},
\quad\sum_{d\ge2}c_dg_d\ne1
\text{ as an unordered Hilbert-space sum}.}
\]
The exact formal conclusion is the negation of `HasSum`, not a claim about
the arbitrary value of Lean's `tsum` on a nonsummable family.

Here `HasSum` means that the net of sums over *all finite subsets* converges.
The result holds for the full conductor family, the masked squarefree
dictionary, and the literal squarefree subtype.

Proof:
1. Applying each continuous biorthogonal coefficient functional gives
   \(c_d=-\mu(d)\), using `q_target_coordinate` and
   `q_coordinate_biorthogonal`.
2. In particular, \(c_p=1\) for every prime.
3. Physical evaluation at \(n=1\) is a continuous linear functional.
   It would send an unconditionally summable atom family to an
   unconditionally summable real family.
4. Restricting that real family to the primes gives
   \(g_p(1)=1/p\), contradicting Euler's prime-reciprocal divergence.

The main declarations are
`QUnconditionalAtomSeries.coefficient_eq_neg_moebius_of_hasSum`,
`no_hasSum_qOne`, and `no_hasSum_squarefree_subtype_qOne`.

Consequently, the two separately summable unordered series
\(\sum_d c_d A_d=P\) and \(\sum_d c_d C_d=C\) cannot satisfy \(P-C=1\).
This is `QSimultaneousCRT.separated_prime_carry_difference_ne_one`.

This obstruction also explains the weak-compactness difficulty for the
unrestricted finite-subset net. Its prime sub-sums satisfy
\[
\left\|\sum_{p\in E}g_p\right\|_Q^2
\ge\frac1{\zeta(2)}
\left(\sum_{p\in E}\frac1p\right)^2
\]
for every finite set E of primes, so those sub-sums are unbounded.
This displayed estimate is an ordinary consequence of retaining the n=1
term in the Q norm; it is not a separate new Lean declaration.

The result leaves open ordered conditional series, sums of grouped blocks,
and finite approximations with coefficients depending on the stage. It does
not infer that a point in the closed linear span must have an unconditional
expansion in the original, nonorthogonal atom dictionary.

## 3. The natural simultaneous Mobius primorial construction

One concrete attempt takes a squarefree primorial L and
\[
S_L=-\sum_{d\mid L}\mu(d)g_d
=\#\{1\le k\le n:(k,L)=1\}-n\rho_L,\qquad
\rho_L=\prod_{p\mid L}(1-1/p).
\]
The first equality defines a finite legal vector. The second is the existing
`QPrimeSieve.divisorSieve_eq_count_sub_linear` identity, evaluated at n.

When L contains every prime up to M, all integers 2 through M are removed
by the sieve, and its complete head error is exactly
\[
\sum_{n=1}^{M}Q(n)|1-S_L(n)|^2=\frac{M\rho_L^2}{\zeta(2)}.
\]
The existing `QPrimeSieve.primeConductor_fullError_ge_quarter` gives, for
the explicitly defined primeConductor family, the unconditional lower bound
\(1/(4\zeta(2))\) on complete error.
`primeConductor_fullError_not_tendsto_zero` rules out L2 convergence to one
for that uncorrected family. These declarations predate this development.
This is an obstruction to the specified coefficients, not to optimal
stage-dependent coefficients.

## 4. CRT cylinders approximate one, but legal projection retains the residual

The bounded ambient CRT cylinder
\(h_L=1-\mathbf1_{\{L\mid n\}}\) has exact complete-Q error
\[
\|1-h_L\|_Q^2=L^{-2}.
\]
Thus ambient CRT cylinder approximation is available explicitly.
Now set \(F_L=P_Hh_L\) and \(r=1-P_H1\). The new exact identities are
\[
1-F_L=r+P_H\mathbf1_{\{L\mid n\}},
\]
\[
\boxed{
\|1-F_L\|_Q^2
=\|r\|_Q^2+\|P_H\mathbf1_{\{L\mid n\}}\|_Q^2,
\qquad
0\le\|1-F_L\|_Q^2-\|r\|_Q^2\le L^{-2}.}
\]
The signed vector identity and the full nonnegative remainder are retained.

These are formalized in `QCRTCylinderProjection`, together with strong
convergence \(F_L\to P_H1\) along every conductor sequence tending to infinity.
The theorem `legalCylinderApprox_tendsto_one_iff` identifies convergence to
the target exactly with \(1\in H\). Projecting the cylinders therefore does
not eliminate the unknown residual energy.

## 5. Why the derived-descent formula cannot simply be substituted

This section is ordinary mathematical analysis, not Lean formalization.

The descent formula recalled in the discussion assumes a descendable
algebra map. Its expansion as a product over all tuples was stated for a
finite family. Tensor products need not distribute over infinite products.

A concrete example is
\[
\mathbb Q\otimes_{\mathbb Z}\prod_p\mathbb F_p\ne0,
\qquad
\prod_p(\mathbb Q\otimes_{\mathbb Z}\mathbb F_p)=0.
\]
For the first assertion, the diagonal unit in \(\prod_p\mathbb F_p\) is not
annihilated by any nonzero integer; it therefore survives rational
localization. Each individual prime-field tensor factor, however, vanishes.
Thus the finite expanded formula cannot be extended to all primes by merely
replacing finite products with infinite ones.

There is a second obstruction to the universal descendability hypothesis.
Let \(B=\prod_p\mathbb F_p\). For a fixed prime p, split B into its p-component
and the product C of the other components; p is invertible in C.
On \(X_m=\mathbb Z/p^m\), the map \(f=p\) becomes null after derived tensoring
with B: the C part is contractible and the p-component is a two-term complex
with zero differential and zero multiplication by p. But \(f^N=p^N\) on
\(X_m\) is nonzero for \(m>N\).

This contradicts the uniform nilpotence criterion for descendability,
Proposition 2.32 of Akhil Mathew,
[Examples of descent up to nilpotence](https://math.uchicago.edu/~amathew/Vancouver.pdf),
page 8. That reference supplies the criterion; the product-ring application
above is the present ordinary deduction. The same argument applies to the
product of all squarefree quotient rings: finite CRT splits them into
repeated prime-field factors. This excludes blanket use of universal
descendability, not descent for every particular module separately.

Finally, over the real algebra of bounded CRT cylinder functions, the
natural pointwise action does not preserve H. The previously verified
legal indicators \(A=g_6-g_2+g_3\) and \(O=2g_2\) have
\(AO=\mathbf1_{\{n\bmod6=5\}}\notin H\).
Hence H is not a module under that natural action. Applying an algebraic
reconstruction theorem to the ambient function space does not establish
membership in this particular closed linear subspace.

## Remaining research obligation

**Open:** construct finite legal combinations \(F_j\) whose complete Q error
tends to zero. Simultaneous CRT provides exact arithmetic coordinates for
every such combination, but the error estimate is still needed.

One sufficient alternative is a uniformly Q-norm-bounded legal family with
coordinatewise limit one. Weak compactness and continuity of each coordinate
then identify a weak limit as one. The necessary uniform bound, together
with those coordinate limits, remains **Open** for an actual construction.

There is no new RH proof and no counterexample to constant-target closure.
The formal negative results concern unordered atomic summation and the
specified primorial family; the exact projected-cylinder identity isolates
the unresolved residual floor.
