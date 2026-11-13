# Actual displacement and continuity on the profinite limit

Date: 2026-11-12 (America/Los_Angeles).

## Result and unresolved target

The requested unconditional assertion that the actual displacement has a continuous
profinite extension remains **Open**. No extension or vanishing provider was found
or assumed in this development.

This change proves, for each of the repository's actual matched displacements,

\[
\boxed{\exists F\in C(\widehat{\mathbb Z},\mathbb R),\
F(n)=d(n)\ (n\ge1)\quad\Longleftrightarrow\quad d=0.}
\]

It also proves that existence of this extension implies Mathlib's
`RiemannHypothesis`.

The two displacements are explicitly distinguished:

| Family | Actual Lean definition |
| --- | --- |
| All conductors \(m\ge2\) | `QFullDisplacement.displacement` |
| Squarefree conductors \(m\ge2\) | `QSquarefreeDisplacementRigidity.displacement` |

Each is the Q projection of the constant target minus its P projection,
represented in the same physical Q coordinates. Neither is the prime-space
projection \(d_W\).

## A stronger quantitative rigidity theorem

Let X be any compact topological space and let \(\iota:\mathbb N\to X\).
For either actual displacement, if a continuous real-valued F and a finite C satisfy

\[
|d(n)-F(\iota(n))|\le C\qquad(n\ge1),
\]

then \(d=0\). The elementary estimate is

\[
|d(n)|\le |d(n)-F(\iota(n))|+|F(\iota(n))|
\le |C|+\|F\|_\infty.
\]

The repository's bounded-displacement rigidity gives residual vanishing,
which gives displacement vanishing. Taking C=0 proves the forward implication
in the boxed equivalence; the reverse implication uses the zero continuous map.

Equivalently, for every nonzero actual displacement and every continuous F,

\[
\forall C\in\mathbb R\quad\exists n\ge1:\quad
C<|d(n)-F(\iota(n))|.
\]

Thus even a finite uniform approximation error is an arithmetic obligation.
These statements apply both to the prime-residue product and to the full
profinite inverse limit, since the proof only requires compactness.

## Exact profinite model

The Lean predicate `HasContinuousProfiniteExtension` uses
`NumberTheory.GeneralizedCRT.ProfiniteInt`, the closed compatible subring of
the product of \(\mathbb Z/m\mathbb Z\) over every positive modulus m.
The physical point is the canonical natural-number cast.
All prime-power depths are retained.

The existing `GeneralizedCRT.profinitePadicEquiv` identifies this full inverse
limit with \(\prod_p\mathbb Z_p\). Existence of the real-valued continuous
extension is not supplied by that ring-valued universal property.

## Why the preceding convergence theorem does not close the target

The preceding prime-Gram theorem approximates \(d_W=\Pi_W^Qd\).
Even for finite projections converging to the actual d, complete-Q convergence
only gives the site-dependent estimate

\[
|d(n)-d_j(n)|\le \sqrt{\zeta(2)}\,n\,\|d-d_j\|_Q.
\]

The factor n is unbounded. The estimate does not imply a uniform bound over n
or over an entire congruence class.

The checked actual displacement equation is \(d=\Pi_V^Q(T r_P)\), where
\(T f(n)=f(n)/(n+1)\) is the operator named B in `QShiftedReciprocal`.
The squarefree closed-kernel identity is

\[
d(n)=\langle r_P,TK_n\rangle_Q,\qquad
K_n=\Pi_V^Q(\mathrm{evaluation}_n).
\]

The exact signed pairing is available. A bound uniform in n for this pairing
has not been established. A uniform bound for \(\|TK_n\|_Q\) would suffice by
Cauchy-Schwarz, but is a stronger unresolved sufficient condition.

Existing modules already reduce the task further: a finite oscillation bound at
one fixed positive modulus suffices. Finite-stage periodicity does not provide
a common such bound for the limit.

## Declaration map

Generic helper module: `RH/QCompactPhysicalBounds.lean`.

- `physically_bounded_of_compact_error`.

Application module: `RH/QDisplacementProfiniteContinuity.lean`.

In each of its `Full` and `Squarefree` namespaces:

- `zero_of_compact_bounded_error`;
- `profinite_extension_iff_zero`;
- `rh_of_profinite_extension`;
- `unbounded_error_of_ne_zero`.

The first, second and fourth are unconditional implications/equivalences
with their hypotheses exactly as displayed. The RH statement is a
**conditional research reduction**: its extension hypothesis for the actual
displacement remains Open.

## Published converse and formalization boundary

Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137-146,
[Theorem 1 and Remark 8](https://arxiv.org/pdf/math/0607733), gives the RH converse
for the constant target's closure membership, including squarefree conductors.
The paper also explains invariance under weights comparable to \(n^{-2}\).

At the published-mathematics level, RH therefore makes both matched projections
of the constant equal to that constant, so d=0 and the extension is continuous.
Combined with the checked direction, the requested continuity is RH-equivalent.
This change does not formalize that published analytic converse or insert it as
an axiom. Its Lean theorems prove the boxed equivalence and the direction to RH.

## Verification

The coherent candidate passed Bazel/BuildBuddy in
`job_SecvLKRGADoyT4h7YsuXx9EY-Ve7bOUe` (77.204 seconds server verification).
The saved modules and nine exact axiom guards passed in
`job__MzNDMkSraPNdfVR0orC1El8gtjGhMfy` (51.429 seconds server verification).
Every audited declaration depends only on `propext`, `Classical.choice`,
and `Quot.sound`. There are no custom axioms or unfinished proof placeholders.

The full publication checkpoint performs source audit, whole-project validation,
and any required integrated-main validation before pushing. Its job and exact
published commit are supplied in the completion report.
