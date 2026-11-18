# Finite atom/carry CRT and Ramanujan coordinates

Source agenda: user-provided categorical CRT note, section 14, priorities 1--2 and the finite foundations of priority 6. This is the first of three implementation stages.

## Exact finite results

- `NumberTheory/PrimePowerCRTDecomposition.lean`, namespace `PrimePowerCRT`: maximal prime-power moduli, pairwise coprimality, factorization, canonical inverse bounds, the simultaneous modular certificate, its exact integer/reciprocal charge, and `atom_reconstruction` for every positive conductor.
- `CategoryTheory/AtomCarryPresentation.lean`: a category of finite-dimensional synthesis presentations with synthesis-preserving linear maps. `crtEquiv` is the coefficient involution `(x,y) -> (x+U y,-y)`; `crtIso` is its presentation isomorphism. `family_crt_span` and `family_crt_disjoint` connect this category to finite generator families.
- `RH/ResidueAtomIndependence.lean`: `residueFraction_linearIndependent` proves independence of every finite injectively indexed family of normalized atoms with conductors greater than one.
- `RH/FiniteAtomCarryCRT.lean`: actual divisor-stage indices, canonical coefficient rows, `presentationIso`, `atomSpan_eq_prime_sup_carry`, and `prime_carry_disjoint`. The latter two assert an algebraic internal direct sum, not an orthogonal sum.
- `RH/RamanujanFiniteIdentities.lean`: `ramanujanSum_divisor_sum` and `ramanujanPacket_prefix_with_constant` retain the conductor-one term in the exact finite identities.
- `RH/CRTCarryRamanujanCoordinates.lean`: `carry_packet_expansion` gives the exact integrated-packet coefficients of every certified finite divisor carry; `canonicalCarry_packet_expansion` specializes it to the full prime-power CRT; `mixed_packetCoefficient` and `canonical_mixed_packetCoefficient` identify the mixed coefficients as `-1/d`.

The new code uses the existing arithmetic floor carry, genuine Moebius function, and genuine normalized residue functions. It does not replace these objects by formal symbols or assume a squarefree output conductor.

## Normalizations and precise hypotheses

Write `g_d(n)=(n mod d)/d` and `J_q(n)=sum_{e|q} mu(q/e)*(n mod e)`. Then

`sum_{q|d} J_q(n) = d*g_d(n)`.

The multiplier is the conductor `d`, not the argument `n`. Also `J_1=0` and `c_1=1`; for positive `q`,

`J_q(n) = n*1_{q=1} - sum_{m=1}^n c_q(m)`.

For the exact carry expansion, all input moduli `p_i` are positive divisors of the positive output `d`, and the integer coefficients satisfy

`sum_i (d/p_i)*a_i = 1+d*k`.

For `q|d`, its packet coefficient is

`A(q)=sum_{i:q|p_i} a_i/p_i - 1/d`.

When each input has at most one distinct prime factor and `q` has at least two, `A(q)=-1/d`. This concerns an exact finite change of coordinates, not orthogonality.

## Remaining stages

Stage two: universal free atom/carry presentation and its defining relations, all-representatives spanning, recursive composition, gcd/divisibility/Ramanujan coordinate assembly, and full-conductor finite Plancherel.

Stage three: P/Q Hilbert transport, weighted Gram and orthogonal decompositions, compatible conductor refinement, full versus squarefree profinite limits, and the additional uniform minimum-energy condition for infinite reconstruction. These analytic conclusions do not follow solely from a finite involution.

## Provenance

S. Ramanujan, *On certain trigonometrical sums and their applications in the theory of numbers*, Transactions of the Cambridge Philosophical Society 22, No. 13 (1918), 259--276, section 2, (2.6)--(2.7), and section 16: https://ramanujan.sirinudi.org/Volumes/published/ram21.html . This supports the divisor/Moebius and cumulative-sum identities.

The category and carry assembly follow the user-provided argument. Wolfram finite checks support the normalization audit but are not used as formal premises.

Publication is gated by the managed full-project Bazel/BuildBuddy checkpoint. The separate continuation handoff records its terminal result and exact commit.
