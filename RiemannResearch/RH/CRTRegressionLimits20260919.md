# CRT weights and the limit of two-seed regressions

Christian Noack — RiemannResearch — 19 September 2026

This continues the finite Green–Pareto/Schur candidates. It establishes convergence with a fixed prescribed prefix and an expanding tail dictionary. Convergence to one as the prescribed prefix grows remains unproved.

## Exact finite regression

Work in the full Pareto Hilbert space
\[
 \|f\|_w^2=\sum_{k\ge1}\frac{|f(k)|^2}{k(k+1)}.
\]
Let \(I_N\) be the canonical balanced packet equal to one on \(1,\ldots,N\).
For a finite set \(S\) of balanced indices greater than \(N\), let \(V_S\)
be their span. The previously constructed full inverse-Gram error minimizer is
\[
 F_{N,S}=I_N+P_{V_S}(1-I_N).
\]
The finite inverse-Gram construction and orthogonal projection are proved
equal. Linear independence of the actual balanced vectors supplies the
Gram inverse, and equal optimal losses force equal coefficient vectors.

For \(S\subseteq T\), the full Pythagorean identity is
\[
 \boxed{\|1-F_{N,S}\|_w^2
 =\|1-F_{N,T}\|_w^2+\|F_{N,T}-F_{N,S}\|_w^2.}
\]
The same identity holds for any scalar target, including zero for the
minimum-energy construction. The prescribed prefix \(N\) is unchanged.

The numerical packet construction uses normalized digit columns
\(h_m(k)=\lfloor k/m\rfloor\bmod a_m\).
The project's literal scalar balanced Hilbert column is \(m h_m\).
Nonzero column scaling preserves the spans and fitted functions; coefficient
vectors must be scaled accordingly.

## Unconditional limit and the missing condition

For any nested finite sets \(S_M\), put
\(K=\overline{\bigcup_M V_{S_M}}\). The strong limit is
\[
 \boxed{F_{N,S_M}\longrightarrow
 I_N+P_K(1-I_N)\qquad(M\to\infty).}
\]
No density hypothesis is needed to obtain this limit. The literal intervals
\(S_M=\{N+1,\ldots,N+M\}\) exhaust all balanced indices greater than \(N\).

The exact remaining condition is
\[
 \boxed{F_{N,S_M}\longrightarrow1
 \quad\Longleftrightarrow\quad 1-I_N\in K.}
\]
Uniqueness identifies the projection onto \(K\); it does not establish this
membership.

For the diagonal \(F_N=F_{N,S_N}\), the prefix constraints change with \(N\).
The fixed-prefix nested identity therefore cannot be applied between
\(F_N\) and \(F_{N+1}\). If the diagonal has a norm limit, that limit must be
one: every coordinate is eventually exactly one, and evaluation is
continuous. Legality and closedness then give the project's unconditional
implication to mathlib's RiemannHypothesis. Existence of the norm limit is
an explicit OPEN hypothesis.

## The complete CRT weights

For positive \(Q,r\), the weight of residue \(r\) modulo \(Q\) is
\[
 W_Q(r)=\sum_{j\ge0}\frac1{(r+jQ)(r+jQ+1)}.
\]
The exact first-atom split and telescoping estimates give
\[
 \frac1{r(r+1)}\le W_Q(r)\le
 \frac1{r(r+1)}+\frac1{Q(r+1)}.
\]
Thus, as \(Q\to\infty\),
\[
 \boxed{W_Q(r)\to\frac1{r(r+1)},\qquad
 W_Q(1)-\frac1Q\to\frac12.}
\]
CRT supplies compatible residue coordinates and exact regroupings; it does
not replace these weights by \(1/Q\).

The residue-one calculation is not an error lower bound for our candidates,
whose errors vanish there. It rules out a blanket uniform-weight replacement
justified only by increasing the modulus. A growing-family estimate must
control the actual weighted quadratic after removing the exact head.

## Arithmetic estimate still required

In tail coordinates, let
\[
 d_{N,S}=\langle z,1-I_N\rangle_w,\qquad
 D_{N,S}=\|1-I_N\|_w^2-d_{N,S}^{\mathsf T}G_S^{-1}d_{N,S}.
\]
The identity \(D_{N,S}=\|1-F_{N,S}\|_w^2\) is exact. The requested conclusion
requires a finite selection \(S_N\) with \(D_{N,S_N}\to0\). The signed Schur
formula expresses this goal without proving the required bound.
The previously formalized uniform exact-head energy criterion would also
supply approximation, but its bound remains the unresolved closure condition.

A fixed-dictionary CLT estimates the finite regression coefficients as sample
size grows. It supplies neither this deterministic approximation bound nor a
dimension-uniform statistical estimate for growing dictionaries.

## Formal coverage

- Analysis/FiniteHilbertGramProjection.lean identifies inverse-Gram synthesis
  with projection onto the actual finite span.
- RH/TwoSeedSchurConvergence.lean proves finite coefficient uniqueness, the
  nested error identity, fixed-prefix strong convergence, the exact
  membership criterion, interval exhaustion, and identification of any
  growing-prefix norm limit with one. Its RH implication is conditional
  on existence of that norm limit.
- RH/ParetoCRTWeightLimits.lean proves the progression limits and failure
  of the residue-one uniform defect to tend to zero.

These arguments use existing project results and Mathlib's
[monotone projection theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html).
No novelty or unconditional RH proof is claimed. The associated checkpoint
records the final kernel verification and publication.
