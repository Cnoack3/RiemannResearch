# Signed aggregate lower-bound continuation — 30 September 2026

Continues the requested commit 10cb52f2e94cdbe298800a7793ae4e99600d5009
on its current descendant 8dbde6f206c3a70ad351625d3874c9aade54713e.
The September 30 large-sieve, Li/Hadamard, and operator imports are present.

**Outcome:** a genuine complete CRT cancellation provider is proved,
uniformly in the optimization dimension. A fully finite lower estimate
for the signed aggregate is also proved, with its residual square retained.
The zero-threshold cofinal lower-bound provider remains open. Neither
this result nor the newer imports establish RH.

## 1. Exact quantities and the complete CRT sum

Repository stage n uses conductors 2,...,n+1. Write

\[
e_{n,d}=c_{n,d}+\mu(d),\quad
H_n=\sum_{d=2}^{n+1}e_{n,d}h_d,\quad
q_n=\sum_{d=2}^{n+1}\frac{e_{n,d}}d,
\]
\[
R_{m+1}=\delta_1+\sum_{d=2}^{m+1}\mu(d)h_d,\qquad
M_N=\sum_{d=1}^{N}\frac{\mu(d)}d,
\]
\[
a(q)=\sum_{\substack{k\ge1\\q\mid k}}\frac1{k(k+1)},\quad
D_n=\sum_{e=2}^{n+1}e_{n,e}a(e),\quad
v_n=q_n\,1-H_n.
\]

The Hilbert weight of physical site 1 is 1/2. At positive physical sites,

\[
v_n(k)=\sum_{e=2}^{n+1}e_{n,e}\mathbf1_{e\mid k},
\qquad v_n(1)=0,\qquad D_n=\langle1,v_n\rangle.
\]

The new quantity includes the entire conductor-one contribution:

\[
\boxed{
I_{m,n}=\sum_{d=1}^{m+1}\mu(d)
 \sum_{e=2}^{n+1}e_{n,e}a(\operatorname{lcm}(d,e)).
}
\]

The d=1 summand is exactly D_n. Every lcm intersection and every
positive arithmetic-progression tail is retained.
completeMobiusCRTIntersection_eq_lcm_sum verifies this exact finite sum.

## 2. Unconditional CRT cancellation, before absolute values

The central new identity is

\[
\boxed{I_{m,n}=M_{m+1}D_n-\langle R_{m+1},v_n\rangle.}
\]

It can also be seen from the full truncated divisor sum

\[
\sum_{d=1}^{m+1}\mu(d)\mathbf1_{d\mid k}
=M_{m+1}+\delta_1(k)-R_{m+1}(k)
\quad(k\ge1),
\]

paired with v_n. Its first-site contribution vanishes because v_n(1)=0.
The Lean proof assembles the finite CRT rows and existing aggregate
reconstruction, so it needs no exchange of an infinite sum with a growing
coefficient family.

Only after the exact signed identity is retained do we estimate:

\[
\boxed{
|I_{m,n}|
\le\bigl(|M_{m+1}|+\|R_{m+1}\|\bigr)\|v_n\|.
}
\]

Moreover, \(\|v_n\|\le |q_n|+\|H_n\|\), and the existing strong derivative
correction limit bounds these norms uniformly. Therefore

\[
\boxed{
\forall\varepsilon>0\ \exists M\
 \forall m\ge M\ \forall n:\quad |I_{m,n}|<\varepsilon.
}
\]

Even an arbitrary optimization sequence n(k), fixed or oscillating,
is allowed: if m(k) tends to infinity, then I_(m(k),n(k)) tends to zero.
No inverse-Gram coefficient l1 norm occurs.

Verified declarations in RH/DerivativeMobiusCRT.lean:

- completeMobiusCRTIntersection_exact;
- completeMobiusCRTIntersection_bound;
- correctionDivisorSynthesis_uniform_norm_bound;
- completeMobiusCRTIntersection_uniform_approximation;
- completeMobiusCRTIntersection_tendsto_zero.

## 3. Why this cancellation leaves the actual sign problem

Let \(T_{m,n}=-\sum_{d=2}^{m+1}\mu(d)\langle h_d,H_n\rangle\).
The exact aggregate CRT decomposition is

\[
\boxed{
T_{m,n}
=\left(\frac12-\langle R_{m+1},1\rangle\right)q_n
 +M_{m+1}D_n-I_{m,n}.
}
\]

This follows from mobiusRowAggregate_complete_crt and
mobiusDivisorMoment_eq_raw_mean. The full lcm term I_(m,n) tends to zero,
as do the other raw-error contributions. The reciprocal charge q_n/2
survives. Equivalently, the original complete pairing remainder is

\[
U_{m,n}=\langle R_{m+1},H_n\rangle,\qquad
\frac{q_n}2=T_{m,n}+U_{m,n}.
\]

Thus the newly established CRT cancellation is compatible with the exact
possibly nonzero limit

\[
T_{m(n),n}\longrightarrow-\frac{r(1)}2
=-\frac12\left[(2-\sqrt2)\|r\|^2+
\frac{\sqrt2}{2}\left\|r-\frac{\sqrt2}{2}D_2r\right\|^2\right].
\]

The entire dyadic square remains. Proving I_(m,n) small cannot be used
to delete the surviving q_n term.

## 4. Fully finite control of negative excursions

Write \(r_n=1-F_n\), \(E_n=\|r_n\|^2\), and

\[
Q_n=(2-\sqrt2)E_n+\frac{\sqrt2}{2}W_n,\qquad
W_n=\left\|r_n-\frac{\sqrt2}{2}D_2r_n\right\|^2.
\]

Here Q_n is finiteDyadicSquare, not the projection capacity used elsewhere.
For b>=0 set n=2b+1 and t=2n+1. Retain the complete increment square

\[
J_b=\left\|(F_t-F_n)
-\frac{\sqrt2}{2}D_2(F_n-F_b)\right\|^2.
\]

The new finite identity, valid for every independent test cutoff m, is

\[
\boxed{
2T_{m,n}
=M_{n+1}-(2-\sqrt2)E_n-\frac{\sqrt2}{2}W_n
 +\frac{\sqrt2}{2}(E_b-E_t-J_b)-2U_{m,n}.
}
\]

Every signed term, both full dyadic squares, and both energy endpoints
remain in mobiusRowAggregate_doubleStage_full_remainders.

The derived lower estimate is

\[
\boxed{
T_{m,n}\ge-\frac{Q_n}2+\frac{M_{n+1}}2
-\frac{\sqrt2}{4}(E_b-E_t)
-\|R_{m+1}\|\bigl(\|R_{n+1}\|+2\|r_n\|\bigr).
}
\]

This is mobiusRowAggregate_doubleStage_lower_bound. It uses only finite
projection energies, physical Hilbert norms, and the scalar Möbius sum.
The positive errors vanish when both cutoffs tend to infinity, but Q_n
tends to r(1), whose vanishing is precisely the unresolved obligation.

There is also a finite signed dyadic budget. Put
n_k=dyadicStage(b,k+1), and allow arbitrary m(k). Then

\[
\sum_{k<K}\left|2T_{m(k),n_k}+Q_{n_k}-M_{n_k+1}
+2U_{m(k),n_k}\right|
\le\frac{\sqrt2}{2}
 \left(E_b+E_{2b+1}-E_{\mathrm{dyadicStage}(b,K)}
 -E_{\mathrm{dyadicStage}(b,K+1)}\right).
\]

The absolute value is taken after complete signed cancellation.
mobiusRowAggregate_centered_dyadic_budget verifies this bound.
It bounds the centered expression, not the uncentered negative part of T.

## 5. Most concrete remaining arithmetic provider

Define the actual correction primitive

\[
P_n(k)=\sum_{j=0}^{k-1}\texttt{correctionCoefficient}(n,j).
\]

For k<=n this is \(\sum_{d=2}^{k+1}e_{n,d}\).
The exact scalar Abel formula is

\[
\boxed{
A_n=\frac{P_n(n)}{n+2}
+\sum_{k=0}^{n-1}\frac{P_n(k+1)}{(k+2)(k+3)}
=q_n.
}
\]

The endpoint is P_n(n)/(n+2), including at n=0; the interior terms are
signed primitives. They must be tested together.

The sharp closing condition produced here is

\[
\boxed{
\forall\varepsilon>0\ \forall N\
 \exists n\ge N:\quad
\frac{P_n(n)}{n+2}
+\sum_{k=0}^{n-1}\frac{P_n(k+1)}{(k+2)(k+3)}
>-\varepsilon.
}
\]

No separate positivity of the endpoint or individual primitives is required.
No absolute coefficient norm or convergence rate is imposed.
reciprocalCorrectionAbel_cofinal_iff_residual_zero proves this is
equivalent to r=0, and hence to vanishing of every fixed derivative mismatch.
riemannHypothesis_of_cofinal_reciprocalCorrectionAbel gives the conditional
RH implication. **Open:** a provider of this complete signed scalar inequality.

The primitive itself already has the exact finite divisor form in
DerivativeCRT.correctionPrimitive_eq_divisor_sum, valid for K<=n:

\[
P_n(K)=\sum_{j<K}\sum_{d\mid j+2}
 \mu\!\left(\frac{j+2}{d}\right)\Delta r_n(d).
\]

Thus the target can be stated entirely as this signed divisor-primitive
harmonic average using the actual optimal residual. The identity is not
a sign estimate.

## 6. Screening the other routes

| Route | What is currently supplied | Remaining input for this task |
| --- | --- | --- |
| Exact CRT | The complete lcm-intersection cancellation above, uniform in n | One-sided sign control of q_n |
| Abel | Exact endpoint plus harmonic-weighted signed primitives | Cofinal lower control of their combined value A_n |
| Weil | Actual correction Mellin samples and mixed/finite zero identities, with reflected-difference square retained | A checked signed comparison to A_n supplying its lower bound |
| September 30 large sieve | Exact finite Parseval/DFT identities and conductor-averaged upper square-energy bounds | Actual CRT Fourier/weighted-tail transfer and a comparison that controls the sign of the surviving charge |
| September 30 Li/Hadamard | Actual RH equivalence and multiplicity-weighted signed zero identities | Positivity of all actual Li coefficients, or a provider relating them to A_n |
| September 30 operator core | Closure, adjoint, deficiency, and shifted-range criteria | The actual domain/range and spectrum-to-zeta identifications |

An upper bound on square energy does not by itself fix the sign of the
reciprocal charge. The Weil reflected-difference square cannot be omitted
to manufacture positivity. No actual Weil/Gram identification or Li
positivity is asserted. The operator imports do not provide arithmetic
cancellation merely by being available.

Contextual literature check: Báez-Duarte, *Arithmetical Aspects of
Beurling's Real Variable Reformulation of the Riemann Hypothesis*,
[arXiv:math/0011254](https://arxiv.org/abs/math/0011254), and
*A strengthening of the Nyman–Beurling criterion*,
[arXiv:math/0202141](https://arxiv.org/abs/math/0202141).
These support the distinction between arithmetic approximation statements
and the required Hilbert-space closure. They are not additional hypotheses
or imported proof steps in the new Lean results.

## 7. Numerical screening, separate from verification

Exploratory double-precision computations used the repository's exact
digamma Gram formula and
\(a(q)=(\psi(1+1/q)-\psi(1))/q\).
The table is indexed by conductor cutoff N=n+1, so the aggregate is T_(N-1,N-1).

| N | Aggregate |
| --- | ---: |
| 2 | 0.2500000000 |
| 3 | 0.1158137453 |
| 5 | -0.0584773969 |
| 8 | -0.0426361602 |
| 12 | -0.0334347465 |
| 24 | -0.0302328713 |

These are exploratory values, not interval certificates or kernel-proved
signs. They provide no asymptotic conclusion. In particular, this work does
not strengthen the requested cofinal condition to pointwise nonnegativity.

## 8. Verification and continuation

The complete 10-endpoint candidate passed the serialized Lean check:
exit code 0, verified=true, 4.834 seconds. The untruncated axiom audit
reported exactly propext, Classical.choice, and Quot.sound for:

- completeMobiusCRTIntersection_eq_lcm_sum;
- completeMobiusCRTIntersection_exact;
- completeMobiusCRTIntersection_uniform_approximation;
- completeMobiusCRTIntersection_tendsto_zero;
- mobiusRowAggregate_doubleStage_full_remainders;
- mobiusRowAggregate_doubleStage_lower_bound;
- mobiusRowAggregate_centered_dyadic_budget;
- reciprocalCorrectionAbel_eq_moment;
- reciprocalCorrectionAbel_cofinal_iff_residual_zero;
- riemannHypothesis_of_cofinal_reciprocalCorrectionAbel.

All substantive assumptions are visible in their theorem types.
The first eight listed facts are unconditional. The cofinal equivalence
does not prove either side; the last theorem retains the arithmetic
provider as an explicit hypothesis. No sorry, admit, project-local axiom,
or unsafe declaration is introduced.

The code extends RH/DerivativeMobiusAggregate.lean and adds the focused
RH/DerivativeMobiusCRT.lean, exported by RiemannResearch.lean.
The theorem catalog records established estimates and the open sign provider
separately. The final publication checkpoint validates changed modules
and local reverse dependents before committing and pushing; its actual
outcome and commit are reported in the final task response.

Continue by proving a lower bound for the combined harmonic Abel charge A_n.
The complete conductor-one CRT intersection already has an unconditional
uniform cancellation provider and need not be reproved.
