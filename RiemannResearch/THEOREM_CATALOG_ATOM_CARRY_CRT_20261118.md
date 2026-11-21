# Atom/carry CRT, Ramanujan coordinates and physical reconstruction

Source agenda: user-provided categorical CRT note, section 14 and the Stage 3 handoff.

The single Lean import `RiemannResearch.CategoryTheory.All` exposes the repository’s categorical CRT declarations and the split exact sequence of the Pareto legal mean.

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

## Universal floor carries and finite conductor transforms

| Module | Principal declarations | Scope |
|---|---|---|
| `RH/UniversalAtomCarryPresentation.lean` | `synthesis_eq_realized`, `relations_eq_ker`, `quotientEquivAtomSpan`, `quotientEquivAtomSpan_mk` | Finite real words on atom labels and full signed certificates. Each carry is the actual floor. The span of the displayed carry relations is the entire kernel. |
| `RH/AllCertifiedCarrySpan.lean` | `adjacentMinus_floor_identity`, `adjacentPlus_floor_identity`, `adjacent_carry_difference`, `allCarrySpan_eq_atomSpan` | For every d > 1 the charges 0 and 1 on the same input pair give carries differing by d times the atom. All representatives together span the algebraic atom space. |
| `RH/CertifiedCarryComposition.lean` | `Certificate.flatten`, `Certificate.flatten_carry`, `recursivePrimeCarry_reciprocal_charge`, `recursivePrimeCarry_flattened` | Signed coefficients multiply down each branch. The outer charge and floor each acquire the coefficient-weighted inner contributions. For an arbitrary finite chain, the total charge and total floor are explicit sums with the same downstream multipliers. The terminal residue and fractional part are retained. |
| `RH/FiniteCarryRamanujanDictionary.lean` | `certificate_packet_expansion`, `packet_coefficients_unique_on_period`, `certificate_cumulative_gcd_expansion`, `certificate_pairing_conductor_scores` | On a common multiple of all inputs and the output, integrated packets, cumulative gcd cells and finite conductor scores compute the same floor carry or its pairing. |
| `RH/UniversalCarryRamanujanSynthesis.lean` | `word_packet_expansion`, `mem_relations_iff_nontrivial_packets_vanish` | Every finite universal word has an actual positive common period. The nontrivial packet coordinates detect membership in the explicitly generated relations. |
| `RH/FullConductorRamanujanTransform.lean` | `primitive_period_orthogonality`, `primitive_gcd_orthogonality`, `conductor_kernel`, `polarized_plancherel`, `transform_inverse` | Arbitrary positive L, including L = 1 and nonsquarefree L. The primal counting measure weights a gcd cell g by φ(L/g), and the dual kernel has diagonal L/φ(L/g). |

At a divisor q of a common period, the floor-carry coefficient is the sum of aᵢ/pᵢ over the inputs divisible by q, minus 1/d when q divides the output. At q = 1 this choice equals the integer charge, while J₁ is zero. One full period of the synthesized sequence determines every nontrivial packet coefficient.

`weighted_gcd_cells_orthogonal` follows from pointwise disjointness. The modulo-six calculation `modulo_six_primitive_and_integrated_gram` gives uniform pairings 0 for c₂,c₃ and 1/2 for J₂,J₃. At L = 4 the full dual diagonal at g = 2 is 4.

## Functorial conductor refinement

`atomPresentationFunctor` and `carryPresentationFunctor` take positive periods ordered by divisibility to their synthesis presentations over real sequences. Both functors extend coefficients by zero along a divisibility arrow. The component of `atomCarryRefinementIso` at period \(L\) is the existing `presentationIso L`. Every refinement square commutes. [Lean declarations](RH/FiniteAtomCarryFunctor.lean)

## Physical Hilbert spaces, conductor refinement and reconstruction

| Module | Checked mathematical conclusion |
|---|---|
| [PhysicalPrimePowerCarryProjection](RH/PhysicalPrimePowerCarryProjection.lean) | Each certified signed floor has its literal physical sequence under P and Q. In both Hilbert spaces, the closed span of projected canonical mixed carries is the orthogonal complement of the closed prime-power span inside the full atom closure. All exponents j ≥ 1 occur. |
| [PhysicalCarryGram](RH/PhysicalCarryGram.lean) | The Stage 1 coefficient matrix T transports each physical Gram matrix to TᵀGT and its observations to Tᵀb. Inverse energy uses the explicit invertibility hypothesis. For singular systems, feasibility, the extended minimum energy and the feasible minimum-norm vector are invariant. The Pareto identities retain the weighting defect, the Green boundary product and the full tail. The Q identities give the inverse-square weighted series and a finite trigamma formula for the packet Gram on a common period. |
| [FiniteAtomCarryRefinement](RH/FiniteAtomCarryRefinement.lean) | For L dividing M, zero extension of the old coefficient arrays commutes with the coefficient involution. Synthesis of both dictionaries commutes with reduction from Z/M to Z/L. In the packet expansion of an old word, every old nontrivial coefficient persists and every new one vanishes. |
| [ConductorTowerCompletions](RH/ConductorTowerCompletions.lean) | On a nested divisibility-cofinal LCM tower the compatible residues form the product of the p-adic integer rings. The primorial tower gives the product of the prime fields. Both identifications are bicontinuous. The quotient reduces each component modulo p. The tuple supported at 2 with value 2 has zero primorial image and residue 2 modulo 4. |
| [ConductorReconstructionEnergy](RH/ConductorReconstructionEnergy.lean) | For arbitrary real data on distinct physical atoms, every finite Gram system is feasible. The supremum of the Moore–Penrose energies over nontrivial divisors of successive LCMs is the global minimum energy. If it is finite, the canonical finite solutions converge in norm to the closed-span solution. |
| [ArithmeticResidueMomentEnergy](RH/ArithmeticResidueMomentEnergy.lean) | For data b(d) = ∑ a(n)g_d(n) with ∑ n²a(n)² finite, explicit physical representers give the all-conductor inequalities below. Conversely, the observations of every physical representer have such a signed-moment representation. |

### Uniform energy estimates and an obstruction

For the signed-moment targets above, the constants in the squared finite-coefficient bound are

- Under P the constant is ∑ n(n+1)a(n)².
- Under Q the constant is ζ(2) ∑ n²a(n)².

These are the squared norms of the displayed physical representers. The least possible constant is the norm squared of the projection onto the atom span closure. For evaluation at a single positive site k, the respective constants are k(k+1) and ζ(2)k². The estimates hold simultaneously over every finite conductor restriction.

For independent prescribed data the two physical norms give equivalent solvability. A P dual-bound constant C gives a Q constant ζ(2)C, and a Q constant C gives a P constant 2C/ζ(2). Any representable atom data satisfy √d b(d) → 0. Thus b(d) = 1/√d has a solution on each finite stage and unbounded least energies on the LCM tower under both measures.

### Conditional research reduction to RH

[QFullDisplacementFiniteHeads](RH/QFullDisplacementFiniteHeads.lean) uses D_j, the difference between the actual Q and P fitted vectors at LCM stage j, and the full displacement D. For any fixed positive integer L and C > 0, `lcm_extension_iff_frequent_head_bound` identifies continuous profinite extendibility of D with the following finite-stage condition. For every H, arbitrarily late j satisfy |D_j(n)−D_j(m)| ≤ C for all positive n,m ≤ H in the same class modulo L. The good stages may depend on H. This holds for any monotone cutoff tending to infinity.

**Open.** Prove this bound for the actual matched projections, for example with L = C = 1. The extension theorem identifies it with D = 0, and `rh_of_lcm_frequent_head_bound` gives the ensuing RH implication. Finite CRT identities and existence of a representer for separately specified signed-moment data leave this premise open.

The coordinate changes in the projection and Gram theorems use finite synthesis. For infinite separated prime and carry series, `RH/QSimultaneousCRT.lean` states the required separate `HasSum` hypotheses. The signed-moment series above has its own summability proof.

### Mixed parity projection in carry coordinates

[MixedCanonicalCarryCapture](RH/MixedCanonicalCarryCapture.lean) expresses each corrected floor carry as the sum of its mixed divisor packets. Divisor induction proves equality of the carry and packet subspaces at every cutoff. Their projections therefore coincide in the Pareto inner product.

[MixedParityCarry](RH/MixedParityCarry.lean) realizes parity as the difference of two certified carries at conductor six. The full carry span has closure equal to the legal space. For the normalized mixed projection `projectedParity`, `norm_sq_add_error` gives its exact squared norm with the screened-target error retained, and `norm_sq_bounds` gives the conductor-241 enclosure.

**Open.** Equality at the upper norm endpoint requires arbitrarily accurate finite carry approximation of the constant in the complete Pareto norm. Equivalently the squared captures on corrected carry spans must converge to log(2) − log(2)².

## Provenance

S. Ramanujan, *On certain trigonometrical sums and their applications in the theory of numbers*, Transactions of the Cambridge Philosophical Society 22, No. 13 (1918), 259--276, section 2, (2.6)--(2.7), and section 16: https://ramanujan.sirinudi.org/Volumes/published/ram21.html . This supports the divisor/Moebius and cumulative-sum identities.

P. Haukkanen, *Discrete Ramanujan-Fourier Transform of Even Functions (mod r)*, Theorems 3.1–3.2. [Paper](https://arxiv.org/abs/1210.0295). L. Tóth and P. Haukkanen, *The discrete Fourier transform of r-even functions*, Application 8, equation (37). [Paper](https://emis.de/ft/40430). These give the finite Fourier and gcd-cell Parseval normalizations.

The category and carry assembly follow the user-provided argument. Wolfram finite checks support the normalization audit but are not used as formal premises.

Publication uses the managed full-project Bazel/BuildBuddy checkpoint.
