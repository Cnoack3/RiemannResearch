# Independent arithmetic certificate review

Date: 24 October 2026.

## Seven explicit squarefree Möbius families

The script `exact_head_rational_certificates.py` was independently inspected.
Its exact rational formula for each residual was checked against the direct
synthesis at every site from 1 through 2000 for all seven heads
1, 2, 4, 8, 16, 32, and 64. Separate exact-Fraction sums checked the directed
finite norm and signed bilinear rounding on smaller cutoffs.
All seven complete output certificates were also regenerated in a separate
run and matched the original JSON exactly.

No correctness defect was found. The complete P tail mass is exactly
1/(K+1); the unnormalized Q tail mass is at most 1/K. The interval for zeta(2)
includes both finite-grid rounding and the integral tail enclosure. Division
uses all four interval corners, including for signed pairings. The residual
amplitude includes the target subtraction and both positive and negative
coefficient ranges. All main-program inputs have positive heads.

The script certifies actual candidate residual norms and pairings. It does not
compute orthogonal projections, minimum feasible energy, or normal repair cost.
Its decimal fields are display approximations; the rational strings are the
certificate endpoints.

## Larger dictionary and physical head

`expanded_squarefree_primal_certificate.py` tests the squarefree dictionary
2 <= d <= 96, containing 59 atoms with largest conductor 95, and physical head
64. This is larger than the earlier repository table's 36 atoms and head 32.

The proposal stage uses numerical complete-P Gram entries and constrained
optimization. The certificate stage uses rational coefficients only. It fixes
every coefficient through the head to -mu(d), rounds the free higher
coefficients, and solves one final rational balance equation so that
sum(c_d/d)=1. Every physical head equation is checked directly afterward.

Finite residual squares are combined before summation and enclosed by directed
rounding at scale 2^96 through K=400000. Infinite tails retain the signed
periodic mean of the residual square, assembled from every singleton and pair
of conductors. The remainder is bounded only after signed assembly.

For a nonnegative period-L function f bounded by b, its centered partial sums
have absolute value at most Lb. Summation by parts bounds its centered P tail
by Lb/((K+1)(K+2)), and its centered unnormalized Q tail by Lb/(K+1)^2.
The P constant tail is exact; the Q constant tail uses the integral enclosure.
All pair means are obtained by exact integer summation over their pairwise LCM,
without enumerating the enormous period of the entire dictionary.

The full rational endpoints and coefficients are in
`expanded_squarefree_primal_certificate.json`. The recorded intervals belong
to the exhibited feasible candidate. Their upper endpoints bound the
constrained minimum, but their lower endpoints do not. They are not intervals
for the normal repair cost. Numerical condition and proposed optimum fields
are explicitly unverified diagnostics.

Outward decimal enclosures for the larger candidate are

| Complete squared residual | Certified interval |
|---|---|
| P | [0.0288461096, 0.0288690873] |
| Q | [0.0176645567, 0.0176785256] |

Both upper endpoints are below the corresponding certified lower endpoints
for the head-64 next-prime Möbius candidate. Thus the larger dictionary gives
a rigorously improved finite candidate. The P signed-Abel tail upper bound
is about 55.72 times smaller than its crude amplitude upper bound.

The separate final verifier run succeeded with the output
`Complete rational P/Q primal certificate independently recomputed.`

Reproduce the proposal and its certificate:

```sh
python expanded_squarefree_primal_certificate.py
```

Recompute the existing certificate using only Python's standard library:

```sh
python expanded_squarefree_primal_certificate.py --verify
```

These exact arithmetic instances are not Lean kernel certificates. No finite
collection supplies an infinite-family growth bound or an unconditional proof
of RH.
