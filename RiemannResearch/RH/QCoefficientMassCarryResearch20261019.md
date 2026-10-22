# Q coefficient mass, scaled carries, and the remaining arithmetic estimate

Date: 2026-10-19 (UTC).

Source: user-provided coefficient-mass argument and requested continuation of
the October 19 conditional-carry and Fourier-kernel development. The argument
supplies the requested norm and mass bounds; the scaled-carry examples below
are a continuation developed in this task. These are not novelty claims.

## What was already available

The workspace starts at commit
079319c2be6f140e8bc30d97f5e953d60463daf7, which includes the cited
1c196c65f52f2dd98fe7c5227bf0c29c9a472eda and the subsequent exact head-step
and periodic-tail results.

Declaration-name searches and focused source inspection found the following
providers, which are reused rather than reproved:

| Existing module | Established provider |
| --- | --- |
| QFiniteEnergyBounds | norm_sq_unweighted and norm_sq_le_head_tail: complete inverse-square series and certified head/tail upper bound |
| Analysis/InverseSquareAbelTail | weight_mass_upper: full inverse-square tail is at most 1/K |
| QConductorLimits | qResidue_tendsto_zero: qualitative strong atom convergence |
| QConductorEscape | exact linear heads, their energy, and qConductorTailSpan_weak_tendsto_zero for arbitrary bounded signed combinations |
| QUniformNormalizedAverages | the same normalized averages have uniform error tending to zero and complete-Q error tending to one |
| QResidueConditional | literal step carries, exact conditional Gram decomposition, zero-fiber leakage, and carry_norm_sq_lower |
| QPrimeCRTCarries | canonical prime-coordinate certificates, integer floor carries, legal representatives, and finite conditional formulas |
| QFourierKernel | exact finite DFT/physical Gram identities and complete frequency-block cancellation |

No equivalent explicit complete-Q conductor upper bound or finite
absolute-coefficient mass consequence was found in the inspected declarations.
The general weak conductor-escape theorem was already present; it is not
claimed as a new result here.

## New unconditional conductor and coefficient bounds

Write Z=zeta(2), Q(n)=1/(Z n^2) for n>=1, and
g_d(n)=(n mod d)/d.

QConductorCoefficientMass.lean first establishes the exact identity

    ||g_d||_Q^2
      = (1/Z) [ (d-1)/d^2
          + sum_(n>d) g_d(n)^2/n^2 ],    d>0.

The head includes d, whose contribution is zero. There are exactly d-1
nonzero terms before that site, each with unnormalized energy 1/d^2.
The entire remaining infinite series is retained. Applying the existing
complete-tail bound gives

    ||g_d||_Q^2 <= 2/(Z d),    d>=2.

For an arbitrary finite indexed dictionary with d_i>=D>=2 and real
coefficients, the triangle inequality and the conductor bound give

    ||sum_i c_i g_(d_i)||_Q
      <= sqrt(2/(Z D)) sum_i |c_i|.

If ||1-sum_i c_i g_(d_i)||_Q<=epsilon, then

    sum_i |c_i| >= (1-epsilon) sqrt(Z D/2).

The declaration does not need epsilon<1; that restriction makes the bound
positive and useful. No squarefreeness, independence, coprimality,
coefficient-sign assumption, or RH assumption occurs.

New public declarations in the ZetaTwoHilbert namespace:

- qResidue_norm_sq_head_tail
- qResidue_norm_sq_le_two_div
- qResidue_sum_norm_le_mass
- qResidue_sum_mass_lower

The sum estimate allows repeated conductors. For an intrinsic coefficient
mass, merge equal conductors first; the same bound applies to that dictionary.

## What signed carry scaling actually achieves

Let C_(d,p)=p g_(dp)-g_d. The existing exact arithmetic identity says

    C_(d,p)(n) = floor(n/d) mod p.

It proves exact cancellation on n<d. The existing lower energy bound is
(p-1)/(Z d^2); this is not replaced by a Haar calculation.

QCarryCoefficientEnergy.lean adds the complete-Q upper bound

    ||C_(d,p)||_Q^2 <= 4(p+1)/(Z d),    d>=2, p>=1.

The signed norm expansion behind this estimate is the existing real Hilbert
identity

    ||C_(d,p)||_Q^2
      = p^2 ||g_(dp)||_Q^2 + ||g_d||_Q^2
          - 2p <g_(dp),g_d>_Q.

This expansion follows from norm_sub_sq_real; it needs no new Gram axiom.
The upper bound uses the triangle inequality on the actual vectors, so it
makes no false assertion about the sign or smallness of that mixed term.

For B_(d,p)=C_(d,p)/sqrt(p), the new declarations prove

    B_(d,p) = sqrt(p) g_(dp) - (1/sqrt(p)) g_d,

    (p-1)/(Z d^2 p) <= ||B_(d,p)||_Q^2 <= 8/(Z d).

Squarefree dp supplies legal membership through the existing divisor-stage
provider. For fixed d and p tending to infinity, every physical coordinate
of B_(d,p) tends to zero. The module proves convergence of every Hilbert
pairing to zero and the exact asymptotic error accounting

    ||1-B_(d,p)||_Q^2 - ||B_(d,p)||_Q^2 -> 1.

Thus increasing coefficient mass and bounded energy coexist, but this
particular family has the wrong weak limit. The positive lower energy bound
also prevents its norm from tending to zero as p grows with d fixed.

There is also an example at precisely the necessary escaping-support mass
scale. Fix p>1 and put S_(d,p)=sqrt(d) B_(d,p). Then

    ||S_(d,p)||_Q^2 <= 8/Z,

and its actual two-conductor coefficient mass is

    sqrt(d) [ sqrt(p) + 1/sqrt(p) ].

Both conductors d and dp escape with d; the mass is of order sqrt(D) with
D=d. For example, p=2 and increasing odd primes d make every packet
squarefree legal. The new scaled_normalizedCarry_weak_tendsto_zero theorem
reuses the existing general conductor-escape theorem to prove that these
bounded packets are weakly zero as well.

These examples establish compatibility of the necessary coefficient-growth
scale with bounded Q energy. They do not construct mutually cancelling
growing collections of carries with progressively exact heads.

## Rigorous cancellations versus the missing estimate

For a finite signed combination F of carry functions of period K=Lr, define
m_a=E_Q[F | N congruent to a modulo L], a=1,...,L, and let w_L(a) be the
complete progression mass. The zero residue is a=L.

The existing periodic_conditional_gram, applied to the combined function
before squaring, gives the exact identity

    ||1-F||_Q^2
      = sum_a w_L(a) (1-m_a)^2
          + sum_(a,k) w_K(a+Lk) [F(a+Lk)-m_a]^2.

This is a mathematical specialization of the existing general theorem,
not an additional declaration added here. It keeps every signed cross term
inside both combined squares. For carry coefficients t_i, the innovations
in the second term are sum_i t_i (C_i-E_Q[C_i|a]); replacing their square by
a sum of individual squares would discard the cancellations being sought.

Similarly periodic_gram and synthesis_gram give the exact physical energy

    sum_(u,v) A_u conjugate(A_v) K_Q(theta_u-theta_v)

of the combined Fourier coefficients. The complete-block identity equals
one even for an all-ones frequency packet. However that packet is
L times the divisibility indicator and includes the constant frequency.
It is not an old divisor-stage legal residue vector: at n=L all old
divisor residues vanish, whereas the packet equals L.

The following are rigorous:

- Reciprocal-slope cancellation gives exact zero physical heads of
  compensated packets.
- Conditional centering makes the mean and innovation parts orthogonal
  in the complete weighted finite profile.
- The canonical prime CRT formula retains its integer floor carry exactly.
- The DFT kernel formula retains all signed frequency interactions.
- A scaled single carry can have growing coefficient mass and bounded energy.
- Uniformly bounded all-escaping residue combinations are weakly zero.

None of these supplies a uniform estimate for the selected *combined*
conditional innovations, or a legal growing-block Fourier bound that
simultaneously enforces the exact physical head constraints.
The conditional mean generally fails to belong to the old legal stage;
conditionalValue_not_old_legal and conditional_leakage_floor already
prevent treating conditional centering as an automatically legal projection.

## Open arithmetic objective for the squarefree RH route

Construct actual squarefree legal F_H, retaining the necessary fixed
conductors, with F_H(n)=1 for 1<=n<=H and a uniform bound on the complete
Q error (equivalently on their Q norms). The existing
squarefree_closure_capacity_and_rh_of_bounded_exact_heads is the conditional
consumer; the provider remains Open.

A concrete conditional/Fourier route would bound the two combined profile
energies in the preceding exact identity along a feasible sequence of
stages. Exact-head synthesis already fixes the relevant low-conductor
coefficients; arbitrary coefficient cancellation is not sufficient.

Alternatively, QSquarefreeHeadStep and QSquarefreeAffineHead give the
actual cost/gain telescope. A summable coefficient-defect budget or a
uniform signed cumulative balance strong enough to bound those minima is
still Open. The new coefficient-mass inequality is a necessary obstruction,
not such a provider.

## Verification boundary

The new source contains no sorry, admit, unsafe declaration, or project-local
axiom. Each proof candidate was checked on the Lean server before persistence.
The push-enabled final checkpoint audits the source and verifies the project
scope required by the server before publishing. Its terminal job, validation
scope, and published commit are reported in the accompanying response.
No hosted CI is requested or used as a verification substitute.
