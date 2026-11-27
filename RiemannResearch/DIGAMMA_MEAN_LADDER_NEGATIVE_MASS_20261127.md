# Digamma mean-ladder negative mass (2026-11-27)

## Why the finite character certificate was abandoned

The theorem `finite_character_cross_certificate_impossible` on current main
proves that the Cauchy--Schwarz certificate introduced at commit `b7e9850a`
fails strictly for every finite character-mode set, including non-prefix sets.
The common-period contribution forces a positive shortfall. Therefore adding
more finite modes cannot close that particular inequality.

## Original mean ladder

Let
[
U_n(k)=operatorname{sectionCoordinate}(n+1,k),
]
the normalized mean-one section computed from the inverse digamma Gram matrix.
For a finite physical head (K), define
[
D_{n,K}=sum_{0le j<K}
 rac{1}{(j+1)(j+2)}max{-U_n(j+1),0}.
]
This keeps every negative coordinate with its exact Pareto weight.

The new Lean identity `digammaNegativeMassHead_eq` identifies this finite
arithmetic sum with
[
operatorname{negativeMassHead}(K,operatorname{packetUnitMean}(n)).
]

## Verified limit and RH equivalence

For every growth law (K:mathbb N	omathbb N) satisfying
(K(n)	oinfty), Lean proves
[
D_{n,K(n)}longrightarrow
 operatorname{hilbertNegativeMass}(u).
]
The proof retains the exact head/tail decomposition. The omitted Pareto tail is
bounded by
[
|operatorname{packetUnitMean}(n)|_P, (K(n)+1)^{-1/2},
]
while the original digamma sections converge in (L^2(P)) to the screened
vector (u).

Consequently,
[
oxed{quad D_{n,K(n)}	o0quadLongleftrightarrowquadmathrm{RH}.quad}
]
This is formalized as `digammaNegativeMassHead_zero_iff_rh`.

The concrete diagonal specialization is
[
oxed{quad
sum_{0le j<n}rac{max{-U_n(j+1),0}}{(j+1)(j+2)}
 longrightarrow0
quadLongleftrightarrowquadmathrm{RH}.
quad}
]
It is formalized as `digammaDiagonalNegativeMass_zero_iff_rh`.

## Exact remaining arithmetic obstruction

The missing unconditional input is now a single averaged signed estimate:
[
D_{n,n}longrightarrow0.
]
Unlike the earlier cofinal prefix lower bound, this does not demand one
pointwise lower bound valid over arbitrarily long prefixes. It permits negative
coordinates, but requires their Pareto-weighted mass in the growing diagonal
head to vanish.

The known negative coordinate in the complete period at stage (n=11),
(k=9856), is retained and prevents any claim of stagewise global positivity.
It does not by itself refute the diagonal-head limit, because that coordinate
lies outside the head (kle11). Any attempt to enlarge the head to a complete
period must include its signed contribution rather than replace it by a
positivity assertion.
