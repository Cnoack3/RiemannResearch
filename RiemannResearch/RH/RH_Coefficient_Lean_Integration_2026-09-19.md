# Coefficient stabilization: Lean integration and the remaining RH input

The complete combined Lean candidate passed kernel checking on September 19,
2026 (job `job_0nZjUZUETj9X-ixwd6hq6bfw1JvwcEsr`, exit code 0, 5.238 seconds).
No warnings were reported. Inspection of the central declarations reported only
`propext`, `Classical.choice`, and `Quot.sound`. The modular checkpoint validates
and publishes the split project files. RH is not proved unconditionally.

## Exact mathematical result

Let W be the closed span of g_d(n)=(n mod d)/d, d>=2, in the actual Pareto
Hilbert space with weight 1/(n(n+1)). Let P_n be the orthogonal projection of
the anchored constant one onto span(g_2,...,g_(n+1)), P the projection onto W,
and r=1-P. Define L_m(f)=sum_{d|m} mu(m/d)(f(d)-f(d-1)).

The finite coefficients are exactly c_(n,m)=-L_m(P_n), and their limits exist:
c_m=-L_m(P). The exact identities and characterization are

\[
E_n=E_\infty+\|P-P_n\|^2,\qquad
c_m=-\mu(m)+L_m(r),
\]
\[
[\forall m\ge2,\ c_m=-\mu(m)]
\iff r=0\iff E_\infty=0\iff\mathbf1\in W
\iff E_n\longrightarrow0.
\]

The written proof is in RH_Coefficient_Stabilization_Theorem_2026-09-18.md.
These equivalences do not assert that their equivalent conditions hold.

## Lean modules

- `Analysis/ExhaustiveProjectionWalk.lean`: four additions for continuous
  projection coordinates, exact limiting energy, and norm bounds.
- `RH/MobiusHilbertCoordinates.lean`: finite coefficient recovery on normalized
  residues, joint separation of Hilbert vectors by L_m for m>=2, the actual
  Riesz representers, and the explicit squared operator norm.
- `RH/MobiusCoefficientStabilization.lean`: exact finite projection expansion,
  stabilization, explicit residual correction, equivalences, and conditional RH
  assembly using the existing Mellin theorem.

The stage n indexing corresponds to N=n+1 in the written proof. All projections
use the full infinite Hilbert norm. Rounded computational approximators and
finite truncations of the norm are not substituted for these projections.

## Combination with existing project results

The key existing inputs are `sum_mobiusDifference`,
`linear_square_summable_iff`, `walkProjection_tendsto`, and
`riemannHypothesis_of_hilbertOne_mem_legalClosure`.

If all target coefficients occur, Möbius inversion makes r(n)=n*r(1).
The existing summability exclusion forces r(1)=0, hence r=0. Every normalized
residue is a legal atom, so the existing Mellin separation and zeta reflection
theorem then proves Mathlib's `RiemannHypothesis`. The theorem formalizes this
implication in `riemannHypothesis_of_limitCoefficients`.

**Open input:** for every m>=2, L_m(r)=0. Stabilization alone establishes the
existence of the limits, not these values.

## A second approximation route

Define A_(m,j)=mu(m/j) when j divides m, minus mu(m/(j+1)) when j+1 divides m,
with each absent divisor contributing zero. The Riesz vector is explicitly

\[
R_m(j)=j(j+1)A_{m,j},\qquad
L_m(f)=\langle R_m,f\rangle,\qquad
\|L_m\|^2=\sum_{j=1}^{m}j(j+1)A_{m,j}^2.
\]

Thus R_m is finitely supported. If R_m belongs to W for every m>=2, projection
orthogonality gives L_m(r)=0. Joint separation then gives r=0 and the same RH
bridge applies. This is formalized in `riemannHypothesis_of_mobiusRiesz_mem`.

**Open input:** approximation of these finite-support Riesz vectors by finite
legal residue combinations in the actual Pareto norm. Finite support and
continuity do not establish that membership. In particular, the legal atoms
g_d and the representing vectors R_m are different families.

The existing bounded-exact-head interpolation theorem supplies another
sufficient condition for target membership, but it explicitly requires a
uniform bound on the full Hilbert norms of legal exact-head interpolants.
No inspected theorem discharges that bound or the Riesz-membership condition.

In particular, `CanonicalMobiusConditionalHead.lean` already constructs legal
exact heads with coefficients -mu(d) for 2<=d<=Y and a correction at d=Y+1.
Those coefficients are eventually the desired values at each fixed index.
They belong to a different family from the full-norm orthogonal projections
used in the new stabilization theorem. Its exact heads and linear bound on
conditional Cesaro energy do not supply a uniform bound on the full Pareto
Hilbert norms, or a strong limit for that canonical family. Substituting those
coefficient limits into the projection theorem would change its hypotheses.

## Verification

Base project commit: `2fbe925a2f73f9727afa26b23d797e7cc742e351`.
The restored workspace initially lacked compiled project imports. Recovery build
`job_NLACout_SfhqdIWvxPNmLm8fEfQneZpG` succeeded. The first combined proof check
then found one definition-unfolding mismatch in the error bound. After repair,
the complete second check succeeded, including the explicit squared norm,
coefficient recovery and stabilization, totality, equivalences, and both
conditional RH implications.

The root module exports both new RH modules, and the theorem catalog separates
the unconditional results from the open hypotheses of the RH reductions.
The code uses no proof placeholders, project-local axioms, or unsafe declarations.
Axiom inspection does not establish hypotheses in a theorem's type: the two RH
entry points still require their displayed arithmetic approximation assumptions.
