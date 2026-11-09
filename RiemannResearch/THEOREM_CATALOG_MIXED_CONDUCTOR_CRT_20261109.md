# Mixed-conductor screening and the full integer CRT

The Hilbert results use the complete Pareto law \(P(n)=1/[n(n+1)]\).
Write \(C_M\) for the span of the mixed Ramanujan packets through \(M\),
\(C\) for their closed span, \(S=I-P_C\), and \(V\) for the full legal
residue closure. A mixed conductor has at least two distinct prime factors.

## Lean declarations

| Module | Result |
| --- | --- |
| [PrimePowerRamanujanClosure](RH/PrimePowerRamanujanClosure.lean) | `finite_screened_error_eq_mean_covariance_projection_tail` gives the exact three-term split for a moving input and independent mixed cutoff. |
| [RamanujanPacketDilation](RH/RamanujanPacketDilation.lean) | `dilation_ramanujanPacket_fiber` selects precisely the output conductors \(t\) with \(t/\gcd(t,m)=q\). `dilation_ramanujanPacket_divisors` and `hilbertDilation_ramanujanPacket_divisors` give the equivalent divisor expansion, with repeated prime factors retained. |
| [MixedConductorDilation](RH/MixedConductorDilation.lean) | `hilbertDilation_mem_mixedClosure` proves invariance. `fullScreening_dilation_primePow` shifts the exponent by \(v_p(m)\). `coprimeDilationSpan_closure_eq_mixedClosure` and `mem_mixedClosure_orthogonal_iff_coprime_dilation` identify the generators and their annihilator. |
| [MixedConductorCovariance](RH/MixedConductorCovariance.lean) | `offDiagonalCovarianceMass_gain` and `offDiagonalCovarianceMass_split` retain the complete squared projection differences. `exists_finiteScreening_cutoffs` selects finite cutoffs for arbitrary moving inputs and positive tolerances. `fullScreening_tendsto_iff_exists_cutoffs` gives the resulting convergence equivalence. `exists_centered_mixed_dual_maximizer` attains the unit-ball dual bound for centered inputs. |
| [MixedConductorHead](RH/MixedConductorHead.lean) | `exists_mixed_exact_head_at` fits any head through \(H\) in the mixed window through \(s(H+1)\) for a prime \(s>H+1\). `mixed_exact_head_error_sq_ge` proves the complete squared error lower bound \(H+1\) for a mixed constant head. `centeredInput_exact_head_tail_product_lower` gives the complete dual tail bound for a mixed correction of the canonical centered input. |
| [ResidueConductorVariation](RH/ResidueConductorVariation.lean) | `norm_sq_le_of_residueConductorVariation` bounds a signed dyadic average by \(13\) in complete squared norm. `residuePairing_dyadic_variation_tendsto` proves vanishing dyadic mean absolute differences for every fixed Hilbert vector. |
| [DyadicAdditiveRigidity](NumberTheory/DyadicAdditiveRigidity.lean) | `eq_log_of_coprime_additive_of_dyadic_variation` identifies a coprime-additive function with vanishing dyadic variation as a multiple of \(\log\). |
| [MixedConductorRankOne](RH/MixedConductorRankOne.lean) | `fullScreening_packet_eq_mangoldt_smul` identifies each screened packet with \(\Lambda(q)u\). `mem_mixedClosure_iff_mem_closedSpace_and_mean_zero` identifies \(C\) with the mean-zero subspace of \(V\). `fixed_capture_tendsto_saturation_iff` gives the fixed-input criterion, and `covarianceMass_eq_fixed_error_add_diagonal_tail` retains the additional diagonal projection tail. |
| [FiniteGeneralizedCRT](NumberTheory/FiniteGeneralizedCRT.lean) | `exists_int_modEq_iff_pairwise` gives existence for arbitrary finite congruences under pairwise gcd compatibility. `int_solution_class` gives the exact lcm solution class. `existsUnique_int_modEq_of_pairwise` gives the normalized representative for positive moduli. |
| [ProfiniteGeneralizedCRT](NumberTheory/ProfiniteGeneralizedCRT.lean) | `exists_profiniteInt_iff_pairwise` lifts any indexed family of compatible positive-modulus congruences to a profinite integer. `profiniteInt_ext_of_lcm_cofinal` gives uniqueness when every positive modulus divides a finite lcm of the given moduli. |
| [ProfiniteCRT](NumberTheory/ProfiniteCRT.lean) | `profinitePadicEquiv` identifies the all-modulus inverse limit with the product of the \(p\)-adic integer rings. `padicProjection_toZModPow` identifies the reductions, and `isTopologicalRingCRT_profinitePadicEquiv` proves continuity in both directions. |

The weighted Gram entries use the complete progression weights in
[ParetoFullTailCRT](RH/ParetoFullTailCRT.lean). The CRT specifies the
compatible cells and their reductions.

## Rank-one full screening

Let \(u=S R_2/\log 2\). If \(h\in C^\perp\), the residue pairing
\(F_h(q)=\langle r_q,h\rangle_P\) is additive on coprime moduli.
For \(n<M\) every adjacent residue difference in the block \([M,2M)\)
vanishes. At any physical coordinate \(n\), the sum of its absolute
differences is at most \(\min(3n,2M^2)\). Splitting the complete weighted
norm at \(M^2\) gives
\[
\left(\frac1M\sum_{q=M}^{2M-1}|F_h(q+1)-F_h(q)|\right)^2
 \le 13\,\|h\mathbf1_{\{n\ge M\}}\|_P^2 .
\]
The right side tends to zero. The additive rigidity theorem then gives
\(F_h(q)=c_h\log q\). Möbius inversion and
\(\sum_{d\mid q}\Lambda(d)=\log q\) give \(S R_q=\Lambda(q)u\).
In particular \(Sx=\langle x,\mathbf1\rangle_P u\) for every \(x\in V\).
The logarithmic step is checked in Lean using Cesàro means along
arithmetic progressions. The classical additive rigidity result and its
short-interval version are discussed in I. Kátai,
[On additive functions](https://doi.org/10.5486/PMD.1978.25.3-4.10), equations
(1.1) and (1.2).

Put \(\delta=\|\mathbf1-P_V\mathbf1\|_P^2\), the repository's
`limitEnergy`. The checked identities are
\[
\|u-\mathbf1\|_P^2=\frac{\delta}{1-\delta},
\qquad
A_N(\infty)=\psi(N)^2\frac{\delta}{1-\delta}.
\]
Consequently \(A_N(\infty)/N^2\to0\) if and only if
\(\mathbf1\in V\). The diagonal value \(A_N(N)\) adds the entire
squared finite-to-full projection difference on the centered input.

## Fixed-conductor criterion

For \(y_M=(I-P_{C_M})R_2/\log 2\), the exact finite error is
\[
\|\mathbf1-y_M\|_P^2=
 \frac{\log 2-(\log 2)^2-\|P_{C_M}R_2\|_P^2}{(\log 2)^2}.
\]
The numerator tends to zero if and only if \(\mathbf1\in V\), which
implies Mathlib's `RiemannHypothesis`. The kernel-checked equivalence
with `BaezDuarte.NaturalApproximation` uses the existing complete
normalization transfer. The converse from RH follows on paper from
Báez-Duarte's [strong Nyman–Beurling theorem](https://arxiv.org/abs/math/0202141),
Theorem 1.1. The repository still treats that analytic direction as an
external provider.

**Open arithmetic estimate.** Prove that \(\|P_{C_M}R_2\|_P^2\) increases
to \(\log 2-(\log 2)^2\). This criterion has a fixed prime input. The
specific diagonal canonical family additionally needs decay of its
moving-input projection tail. Finite mixed exact heads alone are compatible
with growing complete error.

For the centered input \(Z_N\) and \(e=u-\mathbf1\), an exact-head mixed
correction \(c\in C\) through \(H\) satisfies
\[
\psi(N)^2\|e\|_P^4
\le \|e\mathbf1_{\{n>H\}}\|_P^2\,\|Z_N-c\|_P^2 .
\]
Thus exact heads with \(H_N\to\infty\) would imply RH if their complete
squared errors were merely \(O(\psi(N)^2)\). The checked theorem
`riemannHypothesis_of_bounded_centeredInput_exact_head` retains that
bound as an explicit hypothesis. A specific mixed correction family
with this bound remains Open.

## Finite Wolfram validation

The folded Gram computations use complete Pareto progression weights
evaluated through the digamma formula. For the fixed input \(R_2/\log 2\),
the rounded squared errors at \(M=6,12,16,24,32\) were respectively
\(0.39026475,\ 0.34962883,\ 0.29572248,\ 0.23328243,\ 0.21336861\).
Exact symbolic residue reductions also gave zero divisor-formula defect on
complete periods for the tested overlapping cases. The finite values
supply benchmarks for the fixed-input criterion. Wolfram symbolically
simplified the first mixed Gram entries to
\(\langle R_2,R_6\rangle_P=\log 2-\pi/(2\sqrt3)\) and
\(\|R_6\|_P^2=\pi/\sqrt3\), reproducing the first squared error.

## Unscreened size on paper

For \(x_N=\psi(N)^{-1}\sum_{p^k\le N}R_{p^k}\), the prime-power
sum telescopes for each prime to \(r_{p^{k_p}}\), where \(p^{k_p}\) is its
largest power at most \(N\). Thus
\(0\le x_N(n)\le\pi(N)\min(n,N)/\psi(N)\).
On \(n\le N/2\), primes in \((N/2,N]\) give the lower bound
\(n(\pi(N)-\pi(N/2))/\psi(N)\). The Pareto sum and the prime number theorem
then give \(\|x_N\|_P^2\asymp N/(\log N)^2\). For the prime number theorem
forms, see Leonard Tomczak's
[Analytic Number Theory lecture notes](https://math.berkeley.edu/~ltomczak/notes/Mich2022/AnaNT_Notes.pdf),
Section 5.
