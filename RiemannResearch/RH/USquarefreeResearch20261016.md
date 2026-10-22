# Squarefree legal Parseval coordinates: formalization and research agenda

Date: 16 October 2026.

## Scope and conventions

The physical probability law is Q(N=n)=1/(zeta(2)n^2), n>=1.
The repository represents this weighted space by the actual Hilbert realization
ZetaTwoHilbert.QHilbert; qSequence recovers physical values and sets the auxiliary
value at zero to zero. The legal residue atoms are
g_m(n)=(n mod m)/m. The squarefree legal space is

    H_sf = closure(span{g_m : m>=2 and m squarefree}) in L2(Q).

Let psi_d be the complete, Jordan-normalized divisibility wavelet basis, indexed
by every positive integer d, including prime powers. The full Parseval map is

    U f = (<f,psi_d>_Q)_(d>=1),
    K_sf = U(H_sf),
    U_sf = U restricted to H_sf.

K_sf is the image of the legal closure. It is not the coordinate subspace
supported on squarefree divisor labels.

## Formalization status

The following modules contain the formal development. Publication requires the
final server checkpoint to validate these files and their project consumers.

| Module | Checked declaration content |
| --- | --- |
| RH/QSquarefreeCoordinates.lean | Full Parseval coordinates; restriction isometry and equivalence onto the closed legal image; exact mean/energy split; adjoint and projection identities. |
| RH/QSquarefreeCoordinateLegality.lean | Radical differences throughout the legal closure; four-point constraint; qResidue 4 exclusion; proper coordinate image. |
| RH/QSquarefreeCoordinateApproximation.lean | Actual finite synthesis columns and exact error; legal finite synthesis; target membership iff genuine inverse-capacity divergence; optimizer coordinates converge to the legal projection. |

The principal declaration names are `coordinateEquiv`, `coordinateSpace_isClosed`,
`coordinateAdjoint_apply`, `coordinateMap_coordinateAdjoint`,
`error_eq_mean_and_nonconstantEnergy`, `closure_difference_radical`,
`coordinateSpace_ne_top`, `target_mem_iff_inverseCapacity_tendsto`, and
`optimizer_coordinates_tendsto`. The only new RH-facing conclusion,
`riemannHypothesis_of_target_mem`, has an explicit target-membership hypothesis;
it is a conditional research reduction.

The implementation reuses the existing actual QDivisorHilbertBasis, the
literal qSquarefreeCRTSpan, and the actual QSquarefreeCapacity development.
It does not introduce an assumed Hilbert basis or a new assumed RH bridge.

## Exact geometric and arithmetic statements

U_sf is a linear isometric equivalence from H_sf onto K_sf. Its inverse on this
image reconstructs f as the L2-convergent series sum_d z_d psi_d. The image is a
closed subspace of full divisor-coordinate ell2.

For every actual Q vector f,

    (Uf)_1 = E_Q f,
    ||1-f||_Q^2 = |1-(Uf)_1|^2 + sum_(d>=2) |(Uf)_d|^2.

The latter nonconstant energy is Var_Q(f). No nonconstant coordinate is omitted.

For a residue atom,

    (U g_m)_d =
      [sum_(a|d) mu(d/a) E_Q g_m(aN)] / sqrt(J_2(d)),

where J_2(d)=d^2 product_(p|d)(1-p^(-2)).
These are the columns T_(d,m). A finite legal candidate F=sum_m c_m g_m has
coordinates U F=T c, and

    ||1-F||_Q^2 = ||e_1-Tc||_ell2^2.

As a map into all ell2, U_sf has adjoint

    U_sf^* z = P_(H_sf) U^(-1)z,
    U_sf^* U_sf = I,
    U_sf U_sf^* = P_(K_sf).

If the codomain is K_sf itself, the adjoint is the inverse.

The full arithmetic basis factors over coprime conductors. This uses the
independence of prime valuations under Q, with

    Q(v_p(N)=k)=(1-p^(-2))p^(-2k).

This is distinct from independence of ordinary residue classes. It does not
make H_sf a tensor product of prime-local legal spaces.

## Squarefree constraints and properness

For F in H_sf, the backward difference Delta F(n)=F(n)-F(n-1) obeys

    Delta F(n)=Delta F(rad(n))  (n>=2).

In particular,

    F(4)-F(3)-F(2)+F(1)=0.

Continuity of physical evaluation passes these identities to the closure.
They show H_sf and K_sf are proper subspaces of their full ambient spaces.
They do not exclude the constant target: 1 satisfies the displayed relation.
Do not assert that these necessary local relations characterize H_sf.

Ordinary dilation does not generally preserve this space: F(n)=g_3(2n) has
F(4)-F(3)-F(2)+F(1)=1.

Finite divisor-coordinate truncation also need not preserve membership in K_sf.
Finite legal candidates are finite combinations of the actual columns U g_m.

## Priority 1: an arithmetic capacity-growth provider

For a finite family D of distinct squarefree conductors >=2, put

    b_m=E_Q g_m,
    C_D(m,n)=Cov_Q(g_m,g_n),
    kappa_D=b^T C_D^(-1)b.

The actual covariance is positive definite. The exact best legal coefficients
and error are

    c_D^*=C_D^(-1)b/(1+kappa_D),
    min_c ||1-sum_(m in D)c_m g_m||_Q^2=1/(1+kappa_D).

The existing project has a genuine inverse-covariance implementation on an
exhaustive squarefree stage; reuse it rather than applying an inverse to the
masked stage, whose illegal coordinates are zero and hence redundant.

For L_M=product_(i<=M)p_i and D_M={m|L_M:m>=2}, the analytic target is

    kappa_(D_M) -> infinity.

QSquarefreePrimorialCofinality proves cofinal equivalence for its cutoff-indexed
primorial(n+3) family and the exhaustive distinct-squarefree stages.
Here L_M is squarefree; lcm(1,...,n) usually is not. Its pairwise coprime
factors are the maximal prime powers p^floor(log_p n), not just the primes.
CRT decomposes the residue domain and must not be used to infer an additive
linear-span identity for the residue atoms.

Equivalently, the squared mean divided by variance of legal candidates is
unbounded. Positivity, monotonicity, and finitely many numerical values do not
establish this divergence.

On adjoining a conductor, preserve the full centered Schur identity

    kappa_new-kappa_old
      = (beta-v^T C^(-1)b)^2 / (s-v^T C^(-1)v).

A sufficient next theorem is a lower bound forcing the sum of these actual
increments to diverge. The numerator is a screened, signed arithmetic mismatch;
prime independence alone does not control it.

### Primorial cofinality and the block-screening target

The checked QSquarefreePrimorialCofinality module establishes both finite
inclusions, equality of closed legal spans, a common limiting optimal Q
error, and equivalence of capacity divergence. It uses Mathlib's shifted
primorialPeriod(M)=primorial(M+3); reindexing to the product of the first
M primes leaves cofinality unchanged.

The primorial mean and covariance are principal restrictions of a containing
exhaustive system. The divisor-list optimizer has coefficients
c_D=C_D^(-1)b_D/(1+kappa_D), but is generally not the restriction of the
larger optimizer. The checked exact cross-index gain is

    kappa_E-kappa_D
      = ||F_E-F_D||_Q^2 / (error_D * error_E).

For a prime-adjunction packet, D_new=D_old disjoint-union T with
T={p_new*d : d|L_old}. In the centered block covariance, write

    C_new=[C V; V^T S],  b_new=[b; beta],
    R=S-V^T C^(-1)V,  delta=beta-V^T C^(-1)b.

Block inversion gives kappa_new-kappa_old=delta^T R^(-1) delta,
u_T=R^(-1)delta, u_D=C^(-1)b-C^(-1)V u_T, and
c_new=u/(1+kappa_new). These exact finite identities are implemented in
QCovarianceScreening and specialized in QSquarefreePrimePacket. The latter
proves the literal old/new divisor partition, squarefree legality, the next
prime cutoff reindexing, zero increments at composite cutoffs, and the exact
capacity telescope with its initial term. It also identifies the signed
source with (1+kappa_old) times the actual optimal residual correlation
and proves delta(j)^2<=gain*R(j,j). CRT carries remain in the Q covariance.

Conditional research reduction: riemannHypothesis_of_packetGain_sum_tendsto
uses divergence of the actual gain partial sums to conclude Mathlib RH.
Open: an arithmetic provider of that divergence. The new finite identities
do not supply the provider. Detailed record and an informal Mobius sieve
trial: QSquarefreePrimePacketResearch20261016.md.

Next: control the signed screened source delta sufficiently often to force
the sum of packet gains to diverge. Packet size and prime independence
alone do not supply that estimate. Cofinality alone does not prove RH.

## Priority 2: control the collective divisor-coordinate tail

For a chosen finite legal sequence F_j, prove both the required fixed-coordinate
limits and an actual uniform tail budget, for example

    (UF_j)_1 -> 1,
    (UF_j)_d -> 0 for each fixed d>=2,
    lim_(R->infinity) sup_j sum_(d>R)|(UF_j)_d|^2 = 0.

These conditions imply strong convergence to 1. All divisor modes are needed;
squarefree support of the conductors does not restrict the wavelet indices.

A separate sufficient route needs only uniformly bounded total norms and
coordinatewise convergence to e_1: weak closedness of K_sf then gives
e_1 in K_sf. It does not by itself prove strong convergence of that same
sequence. Suitable finite convex combinations can provide strong legal
approximants after membership is established.

## Priority 3: eliminate the target-relevant dual obstruction

The exact dual target is

    z in ell2 and <z,U g_m>=0 for every squarefree m>=2
      implies z_1=0.

This is equivalent to e_1 in K_sf. The aim is to rule out nonzero constant
coordinate in the annihilator; it is unnecessary to prove K_sf=ell2, which is
false because of the local squarefree constraints.

## Priority 4: retain the correct coefficient topology

The raw synthesis matrix T on ordinary squarefree-conductor ell2 has a
different input norm from U_sf on H_sf. A separate, not-yet-formalized development
should establish its boundedness, injectivity, and dense nonclosed range in
K_sf. The coordinate map on H_sf is already an onto isometry.

For the raw operator, a useful proof plan is to dominate its Gram kernel by
a Hardy-type kernel, pass finite synthesis to the ell2 limit, and use the
divisibility formula for physical backward differences to prove injectivity.
The column norms tend to zero, obstructing a bounded inverse on its range.

Analytically, an exact ordinary-ell2 representation Sc=1 would force
c_m=-mu(m), which is not square summable. Thus the target is membership in the
closure of the raw range, not an ordinary-ell2 solution Tc=e_1.

The Gram norm ||c||_G=||sum c_m g_m||_Q gives the appropriate completion for
an isometric synthesis onto H_sf. Formalize additional raw-synthesis claims
separately if they are needed; do not silently infer them from Parseval.

## Priority 5: distinguish literature and formal RH bridges

Classically, Bagchi's squarefree refinement identifies 1 in H_sf with RH,
and equivalent Q/P weights preserve the closure statement. The actual project
already proves squarefree closure => Mathlib's RiemannHypothesis and transfers
squarefree closure between Q and Pareto.

The RH => squarefree-density analytic provider remains a separate formalization
obligation in the inspected capacity module. Do not advertise a two-way Lean
RH equivalence until that provider has a checked declaration.

No capacity divergence, collective coordinate-tail decay, dual-obstruction
elimination, or unconditional RH proof is asserted by this coordinate
formalization.

## Provenance

- User-directed CRT/divisibility/Parseval discussion, continued 16 October 2026:
  definitions, geometric questions, and the requested research direction.
- Bhaskar Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis, 2006, especially Remarks 4 and 8:
  https://arxiv.org/abs/math/0607733
  This supports the classical squarefree RH closure criterion.
- NIST DLMF 27.4: https://dlmf.nist.gov/27.4
  This supports Euler-product terminology and the prime-factor decomposition.
- Mathlib HilbertBasis.repr, LinearIsometryEquiv.submoduleMap, and orthogonal
  projection/adjoint APIs supply the general Hilbert-space geometry.
