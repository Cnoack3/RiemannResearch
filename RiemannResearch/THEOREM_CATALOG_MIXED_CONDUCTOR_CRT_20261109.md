# Mixed-conductor screening and the full integer CRT

The Hilbert results use the complete Pareto law \(P(n)=1/[n(n+1)]\).
Write \(C_M\) for the span of the mixed Ramanujan packets through \(M\),
and \(C\) for their closed span. Here a mixed conductor has at least two
distinct prime factors.

## Lean declarations

| Module | Result |
| --- | --- |
| [PrimePowerRamanujanClosure](RH/PrimePowerRamanujanClosure.lean) | `finite_screened_error_eq_full_add_projection_tail` separates the full-screening error from the finite projection tail. `finite_screened_error_eq_mean_covariance_projection_tail` further splits the full error into its squared mean defect and complete centered variance. |
| [FiniteGeneralizedCRT](NumberTheory/FiniteGeneralizedCRT.lean) | `exists_int_modEq_iff_pairwise` gives existence for arbitrary finite congruences under pairwise gcd compatibility. `int_solution_class` gives the exact lcm solution class, and `existsUnique_int_modEq_of_pairwise` gives the normalized representative for positive moduli. |
| [ProfiniteGeneralizedCRT](NumberTheory/ProfiniteGeneralizedCRT.lean) | `exists_profiniteInt_iff_pairwise` lifts any indexed family of compatible positive-modulus congruences to a profinite integer. `profiniteInt_ext_of_lcm_cofinal` gives uniqueness when every positive modulus divides a finite lcm of the given moduli. |
| [ProfiniteCRT](NumberTheory/ProfiniteCRT.lean) | `profinitePadicEquiv` identifies the all-modulus inverse limit with the product of the p-adic integer rings. `padicProjection_toZModPow` identifies the reductions, and `isTopologicalRingCRT_profinitePadicEquiv` proves continuity in both directions. |

The exact error identity applies to a moving unscreened prime-power
combination \(x_N\) with Pareto mean \(b_N\) and a separately chosen mixed
cutoff \(M_N\). Convergence to one is equivalent to \(b_N\to1\),
vanishing centered variance after full screening, and
\(\|P_Cx_N-P_{C_{M_N}}x_N\|_P^2\to0\). Strong convergence of the
mixed projections supplies a sufficiently large cutoff for each fixed input.
The same-cutoff schedule \(M_N=N\) requires control of the moving inputs.

The CRT declarations specify the compatible cells and their reductions.
The weighted Gram entries still use the complete progression weights
in [ParetoFullTailCRT](RH/ParetoFullTailCRT.lean).

## Consequences on paper

Write \(r_d(n)=n\bmod d\) and let \(D_s f(n)=s f(\lfloor n/s\rfloor)\).
For a prime \(s\ne p\),
\(R_{p^ks}=(D_s-I)R_{p^k}\) follows from
\(D_s r_d=r_{sd}-r_s\) and the prime-power divisor formula.
For \(s>H\), this gives a mixed replacement \(-R_{p^ks}\) for \(R_{p^k}\)
on the first \(H\) sites. Möbius inversion expresses the raw residues as
finite sums of Ramanujan packets. For \(t>H\), the head restrictions of
\(r_t\) and \(r_t-r_m=m\lfloor n/m\rfloor\), \(2\le m\le H\), form a
triangular basis. The mixed span therefore realizes any finite head.
For a mixed vector \(c\) with \(c(n)=1\) for \(1\le n\le H\),
the error \(1-c\) has mean one and lives on the tail of mass \(1/(H+1)\).
Cauchy–Schwarz gives \(\|1-c\|_P^2\ge H+1\).

For the psi-normalized trial let
\(x_N=\psi(N)^{-1}\sum_{p^k\le N}R_{p^k}\).
The prime-power sum telescopes for each prime to \(r_{p^{k_p}}\), where
\(p^{k_p}\) is its largest power at most \(N\).
Thus \(0\le x_N(n)\le\pi(N)\min(n,N)/\psi(N)\).
On \(n\le N/2\), primes in \((N/2,N]\) give
\(x_N(n)\ge n(\pi(N)-\pi(N/2))/\psi(N)\).
The Pareto sum and the prime number theorem then give
\(\|x_N\|_P^2\asymp N/(\log N)^2\).
The checked diagonal criterion in the
[Ramanujan Schur catalog](THEOREM_CATALOG_RAMANUJAN_SCHUR_LOG_20261109.md)
is that the total screened covariance mass is \(o(N^2)\). That estimate
remains Open. Equivalently, the mixed projection must remove
\(\|x_N\|_P^2-1+o(1)\) units of squared norm.

For the prime number theorem in the forms used here, see Leonard Tomczak,
[Analytic Number Theory lecture notes](https://math.berkeley.edu/~ltomczak/notes/Mich2022/AnaNT_Notes.pdf),
Section 5.
