# Reflection-pair Pareto variance: Lean verification

Date: 2026-09-11

This continuation formalizes the preceding law-of-total-variance argument in **86 public theorems across nine modules**. It includes the actual infinite Pareto variance, the explicit CRT covariance calculation, and the signed Jordan divisor objective. The existence of a legal approximating sequence remains open.

## Established identities

For the actual law P(N=n)=1/(n(n+1)), n>=1, and an even positive common period Q, the zero residue has weight W_Q(Q). All infinite progression tails are retained.

Given F(r)+F(Q-1-r)=C, the formalization sums over every residue and divides paired expressions by two. Thus each unordered reflection pair is counted once. The finite conditional-mean and conditional-variance expressions prove exactly

    Var(F(N)) = J_Q(F) + T_Q(F)
    0 <= T_Q(F) <= (pi^2/Q) U_Q(F)
    Var(F(N)) <= L_Q(F) <= (1+pi^2) Var(F(N))
    L_Q(F) = J_Q(F) + (pi^2/Q) U_Q(F).

The center of J is the actual Pareto mean; it is 1 for mean-one packets. The uniform residue mean is proved to equal C/2, so U is genuinely the uniform residue variance.

The proof uses the full weight estimates

    1/Q^2 <= W_Q(r)                   (1 <= r <= Q)
    W_Q(r) <= pi^2/(2 Q^2)           (0 < r and Q <= 2r).

The exact odd Basel series supplies the second constant.

## Actual CRT and Jordan coordinates

An explicit equivalence is constructed between residues modulo lcm(L,K) and the common gcd residue together with the two remaining CRT coordinates. This proves, under uniform residues on every positive common period,

    Cov(R_L,R_K) = (gcd(L,K)^2-1)/12.

This uniform covariance is used only to calculate U; the Pareto law is not replaced by uniform sampling.

For actual signed legal packets

    F(n) = sum_i c_i D_(m_i)(R_(a_i))(n)
    H_d  = sum_i c_i (1_[d divides a_i*m_i] - 1_[d divides m_i]),

the formalization proves

    U_Q(F) = (1/12) sum_[d divides Q] J_2(d) H_d^2
    E F(N) = sum_i c_i log(a_i)
           = sum_[d divides Q] Lambda(d) H_d.

Here Lambda is Mathlib's actual von Mangoldt function. The second Jordan totient is defined by its genuine Mobius divisor formula. Its divisor-sum identity, prime multiplication recurrence and strict positivity are proved. This is an equivalent normalization to the 2- and 3-power expression in the discussion; the von Mangoldt form avoids an extra prime-power reindexing.

All coefficients may have either sign. All positive integer dilations remain available. The H_d are defined from actual legal coefficients, not independent free variables. No mixed term is removed.

The final explicit arithmetic comparison is divisorLegalPacket_variance_jordan_comparison, with only positivity, common-period and mean-one hypotheses.

## Module inventory

| Module | Public theorems | Verified content |
|---|---:|---|
| LinearAlgebra/FinitePairVariance.lean | 15 | Exact two-point and finite conditional variance identities; coefficient and energy bounds |
| RH/ParetoReflectionWeightBounds.lean | 4 | Actual progression lower/upper bounds and odd Basel sum |
| RH/ParetoReflectionVariance.lean | 18 | Zero-residue convention, full Pareto variance, reflection identity, uniform mean, noise bound and comparison |
| RH/ParetoResidueUniformCovariance.lean | 12 | Explicit CRT equivalence, exact common-period uniform covariance and mean |
| RH/ParetoUniformJordanVariance.lean | 10 | Genuine Jordan weights, positivity, signed gcd kernel and divisor diagonalization |
| RH/ParetoJordanMeanCoordinates.lean | 5 | Exact von Mangoldt normalization and coprime support elimination |
| RH/ParetoUniformJordanIdentification.lean | 4 | Actual legal generator covariance and actual uniform variance equals Jordan energy |
| RH/ParetoReflectionLegalPackets.lean | 9 | Legal membership, boundedness, period, reflection, full mean, and explicit arithmetic comparison |
| RH/ParetoReflectionConvergence.lean | 9 | Equivalent convergence objectives, actual conditional RH corollaries, and fixed-witness limitation |

## Conditional research reductions and remaining obligation

paretoVariance_tendsto_iff_reflectionSurrogate proves that the two objectives have the same zero-limit sequences.

riemannHypothesis_of_legal_reflection_split_tendsto proves actual RH from a sequence of finite legal mean-one functions for which

1. reflection calibration tends to zero; and
2. uniform reflection variance divided by the period tends to zero.

The existing proved Pareto/Mellin implication is used. There is no assumed RH bridge. **The required sequence and both convergence providers remain Open.** This is a conditional research reduction, not a proof of RH or a new unconditional all-scale approximation bound.

reflectionCalibration_tendsto_variance_of_noise_tendsto_zero records the limitation: for a fixed witness, vanishing conditional noise makes calibration tend to the unchanged full variance. Changing the conditioning does not itself improve the witness.

## Verification evidence

Coherent source audit:

- Job: job_XnUE-GutWC7j5w8vi7XPXUKYc91Pt9FU.
- Result: succeeded, verified=true, exit code 0.
- Compilation: 6.004 seconds.
- Code SHA-256: 9fadb98554bb0161b12a0223f218c594fff65a73c19676f25da4316c4c5b170e.
- Ten decisive axiom checks: only propext, Classical.choice, and Quot.sound.
- Source scan: no unfinished proofs, added axioms, unsafe declarations, or blanket Mathlib import.

Verification submissions were serialized. Earlier failures concerned imports, rewriting, and elaboration; all were resolved. Each final proof body is included in the successful coherent audit. Final project publication additionally validates the actual module imports and affected dependents.

Base commit: d74dfddeec479a4fbd3839228ec314245400233e.

Source: Christian Noack's discussion of reflection-pair total variance and the Pareto/CRT approximation program, 11 September 2026. No mathematical novelty claim is made.
