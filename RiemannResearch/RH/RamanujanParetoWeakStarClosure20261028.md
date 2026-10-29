# Ramanujan coordinates, Pareto duality, and exact legal heads

28 October 2026 (America/New_York). This continuation is symbolic. It keeps the
previous complete-Q minimizers, finite certificates, and conductor-gap results
unchanged. It distinguishes the squarefree legal span from the full-conductor
span, and algebraic coordinate convergence from actual Hilbert weak convergence.

## What cannot be the squarefree density target

Let L_sf be the closed Pareto span of residues g_d(n)=(n mod d)/d with d>1
squarefree, equivalently the closed span of the corresponding legal Ramanujan
packets. The new explicit vector

    w(1)=2, w(2)=-6, w(3)=-12, w(4)=20, w(n)=0 for n>4

satisfies

\[
\|w\|_P^2=40,\qquad
\langle w,f\rangle_P=f(1)-f(2)-f(3)+f(4),\qquad
w\in L_{\rm sf}^{\perp}.
\]

Therefore L_sf-perp is not zero. This remains true after completing the entire
squarefree conductor dictionary or changing to its Ramanujan coordinates.
However <w,1>_P=0: the witness does not disprove P_(L_sf)1=1.

Its pairing with g_4 is -1. Thus it does not annihilate the full-conductor legal
space. For that larger space, the existing theorem
Pareto.CoefficientStabilization.closedSpace_eq_top_iff_one_mem proves that full
density is equivalent to constant membership. Adding nonsquarefree conductors
is a genuine enlargement; an invertible coefficient transform is not.

## Two different uses of Ramanujan coordinates

The legal packet moment map f -> (<R_q,f>)_(q legal) has kernel L-perp.
The target and its projection have identical such moments. This is already
expressed by RamanujanTransfer.q_moments_eq_projection and q_dual_error_exact.
Convergence on these individual packet tests alone does not separate 1 from P_L1.

The complete finite-site Möbius coefficient map is different. In
RamanujanCompactCoordinates, pareto_coordinates_separate and
q_coordinates_separate use all conductors and genuinely separate the ambient
Hilbert space. Their admissibly weighted observation maps are compact and
injective. Injectivity does not make their inverses continuous on unbounded
families. The canonical projection sequence has a known strong limit P_L1;
its complete coefficients therefore converge to the coefficients of that limit.
Convergence of all those coefficients to the coefficients of 1 would identify
the limit, but that target convergence is not supplied by the coordinate change.

The usual complete Ramanujan character system and its Haar/Cesaro inner product
must also be distinguished from legal integrated residue packets with the
complete Pareto or Q Gram matrix. The existing transfer theorems preserve the
actual legal spans and their metric-specific projections.

## A precise positive weak-star theorem

For a complete closed real Hilbert subspace L define

\[
\mathcal R_L(x)(v)=\langle v,x\rangle,\qquad v\in L.
\]

This is an actual element of Mathlib's WeakDual(R,L), not an informal coordinate
array. The new generic module proves

\[
\mathcal R_L(x)=\mathcal R_L(P_Lx).
\]

For eventually legal F_i, convergence of these restricted dual functionals to
R_L(x) gives ambient weak convergence of F_i to P_Lx. The crucial additional
information from cofinal exact heads is supplied by projected point tests.
For any observation vector e and any legal F with <e,F>=<e,x>,

\[
\boxed{\langle P_Le,F-x\rangle=\langle e,x-P_Lx\rangle.}
\]

In the Pareto application take e_k to be the point vector at physical site k.
Then <e_k,f>_P=P(k)f(k). If F_i eventually matches x at each physical site,
and the projected-point defects tend to zero, every coordinate of x-P_Lx is
zero. Therefore P_Lx=x.

In particular the new theorem projection_eq_of_weakStar_cofinal_exact_heads
proves: for the SAME legal family, cofinal exact heads and genuine weak-star
convergence R_L(F_i) -> R_L(x) imply P_Lx=x. No separate uniform norm bound is
assumed. Specializing x=1 gives exactly the requested projection conclusion,
conditional on this actual weak-star premise.

For sequences, genuine weak-star convergence on all of complete L also implies
uniform functional norms by Banach--Steinhaus. For legal F_i these norms equal
||F_i||. Thus no separate bound is assumed in the new proof, but the convergence
premise has not removed the missing arithmetic control.

The theorem requires tests in the complete subspace L. Convergence on finite
algebraic packet combinations does not establish convergence at P_Le_k.
One must also not combine weak convergence of the least-squares projection
family with exact-head properties of a different CRT family.

The theorem projection_eq_of_epsilon_projected_tests gives its explicit
all-epsilon form: for every k and epsilon>0, eventually

\[
|\langle P_Le_k,F_i-x\rangle|<\epsilon.
\]

When the k-th head coordinate is already exact, the quantity inside the
absolute value is the fixed number P(k)(x(k)-(P_Lx)(k)). A nonzero value
therefore defeats every sufficiently small epsilon. Choosing epsilon indices
alone does not prove the required estimate.

The formal weak-star topology is pointwise convergence on all vectors of its
predual; weak and norm closures of convex sets agree. See Mathlib's
[WeakDual documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/Spaces/WeakDual.html)
and [weak closure theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/LocallyConvex/WeakSpace.html).
These sources support the functional analysis, not the arithmetic premise.

## Finite arithmetic progress: every compatible head is realizable

For an anchored target v(0)=0 and head H, assume

\[
\Delta v(n)=\Delta v(\operatorname{rad}n),\qquad 2\le n\le H.
\]

Define the signed Möbius charges and normalization slope

\[
b_d=\sum_{e\mid d}\mu(d/e)\Delta v(e),\qquad
A_H=v(1)+\sum_{2\le d\le H}\frac{b_d}{d}.
\]

The new finite argument proves b_d=0 at every nonsquarefree d<=H.
For any prime p>H it then constructs the actual vector

\[
\boxed{F_{H,p}=-\sum_{2\le d\le H}b_dg_d+pA_Hg_p.}
\]

It is squarefree legal and satisfies F_(H,p)(n)=v(n) for every n<=H.
Its Pareto image is legal and has the identical physical head. Every
coefficient is retained; zero nonsquarefree coefficients are proved, not assumed.
The proof uses finite Möbius inversion and the fresh-prime relation p*g_p(n)=n
through the head. No energy bound is asserted for this explicit family.

The same vector has the verified finite Ramanujan expansion

\[
F_{H,p}=\sum_{d\in\{p\}\cup[2,H]}\frac{c_d}{d}
\sum_{q\mid d}R_q,
\]

where c_p=p*A_H and c_d=-b_d otherwise. The existence theorem also discharges
the fresh-prime choice for every finite H.

This fills every finite head compatible with the existing radical relations.
It proves finite interpolation, not density for the complete infinite-tail norm.
The already verified matrix reparametrization theorem preserves the complete
feasible-energy set; it cannot promote finite interpolation to norm density.

## Correct dual change of measure

Put Q(n)=1/(zeta(2)n^2) and P(n)=1/[n(n+1)]. The primal sequence-preserving
map toPareto does not itself preserve orthogonality. The new continuous dual
map is

\[
V(u)(n)=(1+1/n)u(n),\qquad
\langle V(u),\operatorname{toPareto}(f)\rangle_P
=\zeta(2)\langle u,f\rangle_Q.
\]

Thus V is zeta(2) times multiplication by dQ/dP on physical sequences.
It transports orthogonal complements faithfully for every submodule.
For the actual squarefree Q residual r, V(r) is a Pareto annihilator and

\[
\langle V(r),1\rangle_P=\zeta(2)\|r\|_Q^2.
\]

It is generally not the Pareto projection residual. Truncation commutes with
V, so every legal exact-head F satisfies the exact transported identity

\[
\zeta(2)\|r\|_Q^2
=\langle T_HV(r),1-\operatorname{toPareto}(F)\rangle_P.
\]

The complete tail inequality follows only after this signed equality. The
additional theorem identifies uniform physical-coordinate boundedness of V(r)
as equivalent to r=0, using the existing actual-residual regularity theorem.
Hilbert norm finiteness is not that uniform physical-coordinate bound.

## Verification and remaining obligation

The new modules are ProjectedObservationTests, ParetoProjectedHeadTests,
ParetoRamanujanSquarefreeAnnihilator, QParetoResidualDualTransport, and
QSquarefreeCompatibleHeads. The final server checkpoint validates the saved
sources and aggregate import. No sorry/admit declarations or new axioms are
introduced. Wolfram separately checked the exact four-site arithmetic and the
fresh-prime cancellation identity; it supplies no premise to the Lean proofs.

Open: prove the actual projected-point test limits (or the genuine WeakDual
convergence) for a cofinal exact-head legal family, or supply a complete-energy
bound/all-epsilon approximation provider. Neither the existing finite-packet
moment convergence nor the finite interpolation theorem establishes that step.
No unconditional target projection identity or RH proof is claimed.
