# An alternate RH route through the actual conditional residual

Christian Noack — RiemannResearch — September 18, 2026

**RH is not proved.** This continuation replaces the proposed subpolynomial
head-energy argument with a precise qualitative residual-regularity criterion.
The implication to RH has a complete mathematical proof. The regularity of the
actual arithmetic residual remains an open mathematical obligation.

## 1. Actual spaces and canonical residual

For positive integers set
\[
w_n=\frac1{n(n+1)},\qquad q_t=\frac2{(t+1)(t+2)},\qquad
(CF)(t)=\frac1t\sum_{n=1}^t F(n).
\]
Let \(H=\ell^2(w)\), \(J=\ell^2(q)\), and let \(V\) be the full finite legal
span of the residue generators and their positive integer dilations. Normalizing
each residue by its conductor does not change this span. The already verified
Cesàro operator \(C:H\to J\) has norm one and an injective adjoint.

Construct the actual closed subspace and its actual orthogonal residual:
\[
W=\overline{C(V)}^{\,J},\qquad r=1_J-P_W1_J,\qquad h=C^*r.
\]
These are definitions; no arithmetic approximation or RH hypothesis is used to
construct them. Orthogonal projection gives the exact equalities
\[
\langle h,F\rangle_H=\langle r,CF\rangle_J=0\quad(F\in V),
\qquad
\langle h,1_H\rangle_H=\|r\|_J^2.
\tag{1}
\]
For every legal \(F\), the full approximation error satisfies
\[
\boxed{\|1_J-CF\|_J^2
=\|r\|_J^2+\|P_W1_J-CF\|_J^2.}
\tag{2}
\]
No mixed term is silently discarded: the mixed term is exactly zero by the
proved orthogonality to the actual closed legal image.

## 2. Signed-tail uniqueness supplies a different route

Define
\[
a_n=w_n h_n,\qquad B_n=\sum_{m\ge n}a_m\quad(n\ge1),\qquad B_0=0.
\]
The existing checked theorem
`legalAnnihilator_anchored_eq_zero_of_summable_signedTail` says that a weighted
square-summable legal annihilator with \(\sum_n|B_n|<\infty\) is zero, provided
the dictionary contains seed 2 and all of its integer dilations. Its proof uses
exact signed summation by parts, inversion of absolutely summable multiples
equations, dyadic scaling, and the weighted difference-energy rigidity theorem.

Apply that theorem to the actual \(h=C^*r\). If \(B\in\ell^1\), then \(h=0\).
Injectivity of \(C^*\) gives \(r=0\). Thus \(1_J\in W\), so for every
\(\varepsilon>0\) there is an actual finite legal \(F\) with
\[
\sum_{t\ge1}q_t\bigl(1-(CF)(t)\bigr)^2<\varepsilon.
\tag{3}
\]
The project's existing `riemannHypothesis_of_conditionalMeanApproximation`
deduces mathlib's `RiemannHypothesis` from (3), using its proved Mellin
second-difference dual functional and zeta reflection. This does not require a
bounded inverse of Cesàro averaging or an assumed Nyman–Beurling implication.

In fact the exact equivalence is
\[
\boxed{B\in\ell^1\iff r=0\iff\text{arbitrarily small legal conditional errors}.}
\tag{4}
\]
For the reverse implications, arbitrarily small errors force \(r=0\) by (2),
and the zero residual has zero signed tail. Neither side of (4) is proved
unconditionally for the actual legal dictionary.

## 3. A concrete sufficient regularity condition

The exact adjoint and double-tail formulas are
\[
a_n=\sum_{t\ge n}\frac{q_t}{t}r_t,
\qquad
B_n=\sum_{t\ge n}\frac{t-n+1}{t}q_t r_t.
\tag{5}
\]
Both identities retain the signed residual. For each fixed \(n\), absolute
convergence follows from \(r\in J\) and \(\sum_tq_t=1\).

A sufficient condition is
\[
\boxed{\sum_{t\ge1}\frac{|r_t|}{t+2}<\infty.}
\tag{6}
\]
Indeed, summing the absolute-value majorant of (5), Tonelli and the exact finite
triangular sum give
\[
\sum_{n\ge1}|B_n|
\le\sum_{t\ge1}\frac{q_t|r_t|}{t}\sum_{n=1}^t(t-n+1)
=\sum_{t\ge1}\frac{|r_t|}{t+2}.
\tag{7}
\]
The Lean construction can obtain the convergence consequence by applying the
existing first-moment tail theorem twice. Specifically, for
\(u_t=q_t r_t/t\), the second absolute moment is controlled by
\[
t^2|u_t|=\frac{2t}{t+1}\frac{|r_t|}{t+2}
\le2\frac{|r_t|}{t+2}.
\]
This yields summability of the first absolute moment of the first tail, then
absolute summability of the second tail. The exact constant in (7) is a written
calculation; the Lean convergence argument does not require that sharp constant.

Condition (6) concerns a single canonically defined limiting residual. It uses
no head length, conductor-growth rate, or subpolynomial estimate. It remains a
substantive unresolved arithmetic condition.

## 4. Why adjoint smoothing does not finish the proof

Take the actual vector \(r=1_J\). It has \(\|r\|_J^2=1\), while
\[
C^*1_J=1_H,\qquad a_n=\frac1{n(n+1)},\qquad
\boxed{B_n=\frac1n.}
\tag{8}
\]
The harmonic sequence is not absolutely summable. Therefore membership in the
conditional Hilbert space and application of the exact adjoint do not imply
the regularity required in Section 2. This example is about the operator in
general; it is not asserted to be the projection residual for the full legal
dictionary.

The actual residual might satisfy a stronger cancellation property because it
annihilates every legal generator. No proof of sufficient additional regularity
has been found here. Finite strict improvements alone also do not supply it:
the project already proves that the actual relative gains must be nonsummable
to force the full residual to zero, and that divergence is itself open.

## 5. Lean verification and publication

No new research declaration has been kernel-verified in this continuation.

- The main proof candidate timed out after 180 seconds with no diagnostics.
- A reduced candidate timed out after 120 seconds with no diagnostics.
- The combined candidates timed out after 180 seconds with no diagnostics.
- A check containing only imports of existing project modules and two `#check`
  commands timed out after 90 seconds with no diagnostics.
- A basic `Nat` arithmetic proof did verify in 3.634 seconds after the worker
  became available. That establishes basic Lean access, not verification of the
  new research declarations.

All these verification jobs reached terminal states. The timeouts are execution
failures, not mathematical refutations. No candidate project patch has been
applied. No new Lean theorem or source module has been committed or published.
The Lean source base remains `b9c341a3d000b278932eb5a818b83ccf6c8afc32`.
This note is suitable for a documentation-only research checkpoint, which does
not certify the draft Lean files.

The accompanying `.lean` files and tool-format patch are explicitly unverified
candidates. Sections 1–4 give written mathematical proofs, not claims of successful
verification of the new declarations.

Intended modules:

- `RiemannResearch/Analysis/FirstMomentTails.lean`: a second-moment tail lemma.
- `RiemannResearch/Analysis/CesaroAdjointTailRegularity.lean`: sufficient
  harmonic integrability and the exact harmonic obstruction.
- `RiemannResearch/RH/ConditionalResidualTailCriterion.lean`: actual closed
  legal image, residual, charge, signed-tail uniqueness, exact Pythagoras,
  qualitative approximation, and conditional RH endpoint.

The remaining obligation is **Open**: absolute summability of the actual
adjoint residual's signed tail, or a proved sufficient condition such as (6).
