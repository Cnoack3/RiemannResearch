# One-sided anchored short-head criterion

Date: 14 November 2026. This continues the Verification Desk's common-bound obligation.

## Result and boundary

The unconditional arithmetic common bound is still open. The new module
`RH/QFullShortHeadOneSided.lean` proves a weaker sufficient hypothesis and its
equivalence to zero actual full Q residual. No unconditional RH theorem is asserted.

Let \(S_j(n,m)=\operatorname{shortSchur}(R,j,H_j,n,m)\), using the actual
all-conductor matched projections and the canonical physical cutoff.
Assume the existing nested, divisor-exhausting periods and \(H_j\to\infty\).
Fix \(L>0\), set \(a_L(n)=n\bmod L+L\), and fix one sign
\(\varepsilon\in\{-1,1\}\). It suffices to prove

\[
 \exists C\in\mathbb R\quad
 \forall n\ge1\quad\forall J\quad\exists j\ge J:
 \quad\varepsilon S_j(n,a_L(n))\le C.
\]

Only one orientation is required. The sign and constant must be independent
of the site and stage; good stages may depend on the site. At \(L=1\), every
anchor is the single physical site 1. A site-dependent constant or a
site-dependent choice of sign does not meet this hypothesis.

## Proof

Write \(d(n)=qSequence(QFullDisplacement.displacement,n)\).
The already checked exact signed limit gives
\(S_j(n,a)\to\zeta(2)(d(n)-d(a))\). Passing the frequent upper bound to this
limit yields a global one-sided bound

\[
 \varepsilon d(n)\le
 D:=|C|/\zeta(2)+\sum_{0\le r<2L}|d(r)| .
\]

The finite anchor set is the reason this constant is uniform. The value at
zero is handled separately using \(d(0)=0\).

For any one-sided physical bound \(\varepsilon d(n)\le D\), with \(D\ge0\),
the selected signed harmonic prefix satisfies

\[
 \sum_{n=1}^{X}\frac{\max(\varepsilon d(n),0)}n
 \le D H_X\le D(1+\log X)\le 2D\log X
\]
for sufficiently large \(X\). The checked full-displacement cofinal signed
harmonic rigidity theorem then gives \(qResidual=0\), and hence RH.

Once that premise is provided, every fixed pair satisfies \(S_j(n,m)\to0\).
In particular, for every \(c>0\), all sufficiently late stages satisfy
\(|S_j(n,m)|\le c\). This consequence does not assume that the two sites
are congruent.

## Declaration map

All names below are in `RiemannResearch.RH.QFullShortHeadOneSided`.

- `harmonicSide_le_of_oneSided_bound`: signed prefix at most \(D H_X\).
- `qResidual_zero_of_oneSided_displacement_bound`: either globally bounded
  signed side forces zero full residual.
- `oneSided_displacement_bound_of_frequent_anchor`: frequent anchor bounds
  give a global one-sided physical displacement bound.
- `qResidual_zero_of_frequent_oneSided_anchor`: the main conditional reduction.
- `eventually_abs_shortSchur_le_of_frequent_oneSided_anchor`: recover every
  positive two-sided bound, eventually at each fixed pair.
- `riemannHypothesis_of_frequent_oneSided_anchor`: conditional RH consumer.
- `qResidual_zero_iff_frequent_oneSided_anchor`: equivalence for each fixed
  positive modulus and each fixed sign.
- `riemannHypothesis_of_frequent_oneSided_fixed_anchor`: the modulus-one
  specialization, comparing only with site 1.

## What the attempt did not establish

The Hilbert evaluation estimate in `QFullCRTDisplacement` contains the
factor \(\sqrt{\zeta(2)}(n+m)\); it does not provide a common constant.
The signed harmonic argument is a consumer of the missing arithmetic bound.
It must not be used as evidence that this bound already holds.

Finite exploratory calculations of the full-period matched displacement
used all divisor atoms and the complete periodic weights
\(Q_R(a)=\psi_1(a/R)/(\zeta(2)R^2)\) and
\(P_R(a)=[\psi((a+1)/R)-\psi(a/R)]/R\), for \(1\le a\le R\).
These were floating-point SciPy weighted least-squares calculations, without
interval certification. They concern \(d_R(n)-d_R(1)\), not the finite-stage
shortSchur expression.

| Period R | Divisor atoms | Minimum anchored displacement | Maximum anchored displacement |
|---:|---:|---:|---:|
| 6 | 3 | -0.01366537 | 0.00966700 |
| 60 | 11 | -0.04639564 | 0.00334507 |
| 2520 | 47 | -0.10081892 | 0.06849046 |
| 27720 | 95 | -0.18997627 | 0.16002954 |

These finite samples do not establish a cofinal common bound, its sign,
or its asymptotic size. No numerical hypothesis enters any Lean proof.

## Verification

The complete module compiled in `job_PasbB8qJPH8vjxIotFhd2rojV4uHY9bh`
(Bazel/BuildBuddy, exit 0; 146.700 server seconds).
Eight exact axiom-list guards passed in
`job_mPFX55tYRF8gTWm6xaxUv139c164421G`
(Bazel/BuildBuddy, exit 0; 78.431 server seconds):
only `propext`, `Classical.choice`, and `Quot.sound`.
[Module check](https://app.buildbuddy.io/invocation/8017a944-69ca-4fbc-9108-f2a6b4989494).
[Axiom guards](https://app.buildbuddy.io/invocation/1fa14eb6-e8a2-41b9-b440-15e3c6d8b665).

The publication checkpoint separately performs full-project
`bazel build --config=buildbuddy //:RiemannResearch` validation and records
the exact published commit. The focused axiom audit is not an audit of every
declaration in the repository.
