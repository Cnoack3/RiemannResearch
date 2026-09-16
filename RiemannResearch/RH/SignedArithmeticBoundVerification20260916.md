# Signed arithmetic energy: verified range and remaining target

This continuation does not prove the RH-equivalent arithmetic bound.
It supplies the complete prime-power enumeration and unconditional estimates
for the actual prescribed signed charges. The RH/Mellin equivalence in the
research report remains a separate formalization obligation.

## Exact objects

Let q_0=2<q_1<... enumerate the support of Mathlib's von Mangoldt function,
so every prime power occurs once. For cell i=[q_i,q_(i+1)], put

- w_i=1/q_i-1/q_(i+1),
- m_i=log(q_(i+1)/q_i)/w_i,
- D_i=psi(q_i)-m_i,
- v_i(s)=(q_i^(-s)-q_(i+1)^(-s))/s.

The signed charges are the existing `signedJump`; their cumulative sum
through index i equals D_i. In particular, the reference mean is the same
critical mean m_i for every damping exponent s. The bound is for the
prescribed arithmetic coefficients, not an optimized replacement family.

## Established without an RH hypothesis

`RH/PrimePowerEnumeration.lean` constructs the actual enumeration and proves
strict monotonicity, positivity, complete support through every endpoint,
q_0=2, and q_(i+1)<=2*q_i. The last assertion follows from the next power of
two; it needs no prime-gap theorem. `enumerated_cumulative_eq_psi` gives the
exact endpoint identification with Mathlib's Chebyshev function.

Let K=log(4)+4. `RH/PrimePowerEnergyBounds.lean` proves

    A_N = sum_(i<N) w_i D_i^2 <= K^2 (q_N-2),

and, for every real s>2 and every N,

    sum_(i<N) v_i(s) D_i^2 <= K^2 * 2^(2-s)/(s-2).

The corresponding infinite series is proved summable. These are baseline
unconditional estimates; no novelty or progress on the RH exponent is claimed.

Proof of the damped estimate: Mathlib's checked Chebyshev theorem gives
0<=psi(q_i)<=K*q_i. The interval mean satisfies 0<=m_i<=q_(i+1)<=2*q_i,
and K>=2. Thus D_i^2<=K^2*q_i^2. On its cell, q_i<=x, so

    v_i(s)D_i^2 <= K^2 integral_(q_i)^(q_(i+1)) x^(1-s) dx.

Summing telescopes, retaining the finite endpoint term before bounding it.
The geometric integral converges precisely in the range s>2 used here.

`Analysis/PowerCellEnergy.lean` proves the actual power-weight integral
formula and comparison. `Analysis/ReciprocalCellEnergy.lean` contains the
mean bounds and the reusable critical interval-energy estimate.

## Signs, reset corrections, and exact open propositions

`actual_damped_signed_abel_identity` keeps every signed earlier-current
cross term and the terminal subtraction. `actual_damped_total_reset_cost`
identifies the full squared norm of the existing canonical reset correction
with this damped arithmetic energy. `dampedCellWeight_one` recovers the
previous critical weight exactly.

The following definitions are propositions, not asserted theorems:

- `SignedArithmeticDampedBound`: for every epsilon>0, the prefix energies
  at s=1+epsilon have one finite bound independent of N.
- `SignedArithmeticSubpolynomialBound`: for every delta>0, there exists
  C>=0 with A_N<=C*q_N^delta for every N.

The first is currently proved here only for epsilon>1. The second's verified
linear estimate does not provide the exponents 0<delta<1. Extending either
estimate to all the exponents in its definition remains Open (mathematics).
No theorem of unprovability is claimed.

Still Open (formalization): the global prime-gap providers and geometric
summability, the real step-function identification inside every cell, and
the Mellin/zero/RH analytic links. The global enumeration and its endpoint
Chebyshev identification are now discharged.

## Verification and source

The combined proof passed Lean with exit code 0 and autoImplicit disabled.
Axiom inspection of the main enumeration, critical-energy, damped-energy,
summability, signed-Abel, and reset-cost theorems reported only propext,
Classical.choice, and Quot.sound. The project checkpoint checks the final
separated modules and their dependents.
No RH assumption, local axiom, proof placeholder, or unsafe declaration is
introduced. The publishing session reports the accepted checkpoint commit.

Target provenance: user-provided
V_Zeta_Vector_Spaces_Research_2026-09-16.md, Sections 15-18.
The quantitative input is
[Chebyshev.psi_le_const_mul_self](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html#Chebyshev.psi_le_const_mul_self).
It bounds psi itself linearly; it does not give an RH-strength error bound.
