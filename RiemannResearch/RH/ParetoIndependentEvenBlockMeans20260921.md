# Independent even corrections, exact block energy, and bounded first-point approximation

Continuation of the user's Pareto parity-closure handoff, 21 September 2026.
Starting published commit: `a3529bf6a9bcdeeeb9ac616e44080525856325ec`.

## Mathematical advance

The finite even dictionary now grows independently of the finite arithmetic
candidate. The complete norm, the full signed inverse-Gram contribution, and
the normalization cost are retained. The previously informal infinite parity
decomposition is connected to the actual Hilbert block projection.

No unconditional full-energy decay or uniform boundedness is supplied.
The Riemann Hypothesis remains open in this continuation.

## 1. A finite optimizer with an independent correction scale

Write `z = infiniteCoprimeCertificate 2`. For a finite linearly independent
dictionary v, let P_v be its actual orthogonal projection, q=P_v z and
K=||q||². The new general finite Hilbert construction is

    C_v(f) = f-P_v f - (<f-P_v f,z>/K) q.

When K is nonzero, <C_v(f),z>=0. The precise energy is

    ||C_v(f)||² = ||f-P_v f||² + <f-P_v f,z>²/K.

For every other feasible coefficient vector c, its energy is this minimum
plus the squared norm of the difference between the corrections. If the
dictionary spans are nested, the exact refinement identity is

    ||C_v(f)||² = ||C_w(f)||² + ||C_v(f)-C_w(f)||².

For the even tail-atom dictionary, positivity of K follows from the already
proved modulus-two observation. `independentEvenCorrection n f` realizes
this formula for any actual Hilbert vector f. Its squared energy is
nonincreasing in positive dictionary sizes. If <f,z>=0, its complete energy
is at most ||f||².

Modules: `Analysis/FiniteHilbertHeadConstraint.lean` and
`RH/ParetoIndependentEvenCorrection.lean`.

## 2. Preservation of every odd contrast

An even tail combination has identical pairing with the difference
certificate u_p and with z, for every odd physical p>=3. Consequently a
certificate-normalized even correction leaves every odd contrast unchanged.
This proves preservation of the entire convergent contrast series, not only
of a finite truncation.

The complete contrast series is now proved summable for every actual
Hilbert vector. It is nonnegative and no greater than the complete norm
squared. Define the complementary energy as full norm squared minus this
entire series; its nonnegativity is proved.

Module: `RH/ParetoFullContrastEnergy.lean`.

## 3. Exact geometric identity for the remaining energy

Let B be the actual dyadic block projection and L=T₂*/2 its half-adjoint.
The project now identifies the infinite contrast series with the actual
dyadic kernel-defect energy, including the first physical coordinate.
Precisely,

    remainingEnergy(f) = f(1)²/2 + ||Bf||²
                       = f(1)²/2 + 2||Lf||².

For every tail vector f(1)=0 this yields

    ||f||² = fullOddPairContrastEnergy(f) + 2||Lf||².

The factor two is exact. This identity is not a contraction estimate.
No term involving the full block means has been dropped.

Module: `RH/ParetoParityBlockEnergy.lean`.

## 4. The concrete two-scale Möbius family

Let F_P be the existing all-divisor Möbius tail vector, with odd moment one
and reciprocal head kappa. Put E_(P,m)=C_(m+1)(F_P), so that the sieve
conductor P and even-dictionary parameter m are completely independent.
Let

    S = sum_(odd p>=3) 1/p²,
    R_P = sum_(odd p>=3, coprime(p,2P)) 1/p².

For P nonzero and divisible by three, the exact complete energy is

    ||E_(P,m)||² = (S+1)² R_P/[2S(S-R_P)] + 2||L E_(P,m)||².

For P=(n+2)!, the first term tends to zero for every schedule m=m(n),
by the previously proved arithmetic contrast closure and the new invariance.
Thus the complete energy tends to zero if and only if

    ||L E_((n+2)!,m(n))||² -> 0.

This isolates the remaining question in an actual full Hilbert norm.
Increasing m decreases the complementary energy by precisely the squared
change in the corrected vector. It does not prove that the limiting
complementary energy is zero.

Key declarations: `independentEvenCorrection_refinement`,
`independentEvenCorrection_remaining_refinement`,
`independentlyCorrectedSieve_energy_exact`, and
`independentlyCorrectedSieve_fullEnergy_iff_blockMeans`.

## 5. The bounded exact-head route is sufficient

For an arbitrary submodule S, a uniformly norm-bounded family in S which
converges at every physical coordinate to x puts x in the norm closure of S.
The proof uses bounded convergence on dense Hilbert test vectors and
orthogonal complements; it does not assume strong convergence of the family.

Apply this to the original legal space and x=a e₁, a nonzero. A uniformly
bounded family of genuine legal vectors matching a e₁ on growing initial
heads therefore implies Mathlib's RiemannHypothesis. No RH-to-density
provider is used in this implication.

The source supplement's uniform bound remains an explicit **Open**
arithmetic premise. This theorem validates that research target; it does not
construct a bounded family.

Module: `RH/ParetoBoundedCoordinateClosure.lean`.

## 6. A quantitative obstruction under an off-line zero

If s is an actual zeta zero with beta=Re(s)>1/2, and a legal vector f agrees
with a e₁ through physical site N>=1, the complete energy satisfies

    ||f||² >= a²/2
      + [a²(2 beta-1)|1-2^(-s)|²/|s|²] (N+1)^(2 beta-1).

The full first-point Mellin factor is retained. Every occurrence of a
zeta zero is an explicit hypothesis; existence is not asserted. The proof
also yields an exact finite-energy criterion excluding a zero at s.

Module: `RH/ParetoFirstPointHeadObstruction.lean`.

## Verification and scope

Development and review were parallel; the coordinator serialized all Lean
verification submissions. Final installed-module acceptance is the single
publishing checkpoint for this continuation. Its receipt and commit are
recorded in the delivered handoff and in Git.

No `sorry`, `admit`, project-local axiom, unsafe declaration, RH assumption,
or zero-existence provider is introduced. Conditional RH endpoints retain
their substantive full-energy or boundedness obligations explicitly.

The next concrete target is a proved schedule m(n) for which the full
half-adjoint block-mean norm tends to zero, or a uniformly bounded complete
norm for a genuine growing exact-head first-point family. Neither follows
from the solved contrast limit alone.
