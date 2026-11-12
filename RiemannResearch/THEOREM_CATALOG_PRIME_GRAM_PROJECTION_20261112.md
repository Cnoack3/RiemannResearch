# Prime CRT selectors and inverse-Gram Q projections

## Scope and source

Formalization of the user's finite-CRT and increasing-subspace projection argument (2026-11-12).
The result is unconditional for every `d : QHilbert`. It uses the actual physical
Q Hilbert space and its literal residue atoms `qResidue p`, not a Haar-space surrogate.

Write $g_p(n) = (n \bmod p)/p$, with Q(n) = 1/(ζ(2)n²) for positive n.
Let p_i be the increasing prime enumeration, starting at index zero in Lean.
For N ≥ 0 set

- W_N = span {g_{p_i} : i < N};
- W = closure(span {g_p : p prime});
- d_W = Π_W^Q d;
- G_N(i,j) = ⟨g_{p_i},g_{p_j}⟩_Q;
- b_N(i) = ⟨d,g_{p_i}⟩_Q;
- c_N = G_N⁻¹ b_N and S_N = Σ_{i<N} c_N(i) g_{p_i}.

The inner products and energies are complete Q quantities. There is no truncation of
the physical positive-integer variable in G_N or b_N.

## Proof

For a finite injective prime family and selected index i, finite CRT produces
a natural n whose residue is 1 at p_i and 0 at all other family primes.
This n is positive because its p_i residue is 1. Evaluation of a vanishing
linear combination at n gives c_i/p_i = 0. Thus the atoms are linearly independent.

The Gram matrix is positive definite, has positive determinant, and is invertible.
Existing finite Hilbert Gram theorems identify S_N with Π_{W_N}^Q d.
The prime enumeration exhausts all prime atoms, so increasing-subspace projection
convergence yields S_N → d_W in Q norm.

Every finite-family atom is in W, so d − d_W is orthogonal to it and
b_N(d_W) = b_N(d). The existing exact finite inverse-Gram residual formula,
applied to d_W, therefore gives

    ‖d_W − S_N‖_Q² = ‖d_W‖_Q² − b_Nᵀ G_N⁻¹ b_N → 0.

Finite CRT supplies the independence argument. Hilbert-space projection
convergence supplies the infinite limit; no infinite-series convergence is
deduced from the categorical CRT universal property.

## Declaration map

Namespace `RiemannResearch.NumberTheory.PrimeCRTSelectors`:

| Declaration | Content |
| --- | --- |
| `exists_positive_selector` | Positive CRT coordinate selector for any finite pairwise-coprime family of moduli at least 2 |
| `exists_positive_prime_selector` | Specialization to an injective finite prime family |

Namespace `RiemannResearch.RH.QPrimeGramProjection`:

| Declaration | Content |
| --- | --- |
| `primeResidue_linearIndependent` | Actual Q prime atoms are linearly independent, by CRT evaluation |
| `primeAt_prime`, `primeAt_injective`, `primeAt_covers` | Prime enumeration is prime-valued, injective, and exhaustive |
| `dictionaryClosure_eq_primeClosure` | Enumerated dictionary closure equals W |
| `gram_apply`, `rhs_apply` | Explicit entries of G_N and b_N |
| `gram_posDef`, `gram_det_pos`, `gram_isUnit`, `gram_mul_inverse` | Actual Gram invertibility |
| `approximant_eq_projection` | S_N = Π_{W_N}^Q d |
| `approximant_tendsto` | S_N → d_W in Q norm |
| `rhs_limitProjection` | b_N(d_W) = b_N(d) |
| `energy_identity` | Exact displayed inverse-Gram error identity |
| `squared_error_tendsto_zero` | Squared Q error tends to zero |
| `energy_deficit_tendsto_zero` | Inverse-Gram energy deficit tends to zero |

## Dependencies and logical scope

The general finite Gram results are in
`Analysis/FiniteHilbertGramMatrix.lean` and
`Analysis/FiniteHilbertGramProjection.lean`.
The exhaustion theorem is in `Analysis/ExhaustiveProjectionWalk.lean`.
The physical prime span is defined in `RH/PrimeTreeConstants.lean`.
Finite CRT is Mathlib's `Nat.chineseRemainderOfFinset`.

The coefficients c_N vary with N. This theorem does not assert absolute summability
of the canonical limiting prime coefficients or uniform convergence on a
profinite space. It adds no RH hypothesis and proves no new RH implication.

## Verification

The coherent candidate passed Lean in job
`job_KANV6sLLNaCtqwn2xRMAcSFkWX3Uw6r5` (Bazel/BuildBuddy, 58.665 seconds).
The saved modules and seven exact `#guard_msgs` axiom audits passed in job
`job_q04_ULdWy8ff2l18XcB0sY90RnhCKLAE` (Bazel/BuildBuddy, 48.301 seconds).

The audited declarations are the prime CRT selector, prime-atom independence,
Gram invertibility, projection identity, energy identity, norm convergence, and
energy-deficit convergence. Each depends only on `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom occurs.

The publication checkpoint performs the full Bazel/BuildBuddy project build and
any required integration validation before committing and pushing. Its job and
published commit are supplied with the completion report.
