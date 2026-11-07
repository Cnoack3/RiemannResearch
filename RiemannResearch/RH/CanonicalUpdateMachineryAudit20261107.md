# Audit of the existing machinery for canonical LCM updates

This is a read-only audit of existing project declarations after the explicit
Euler/Mellin estimates and the CRT instability results were checked. It does
not introduce an additional conditional RH theorem. The audit adds no new proof or verification job.

## Finding

The inspected machinery provides exact carry decompositions, complete-Q
conditional covariance identities, and a useful logarithmic inverse bound for
screened physical-head Gram matrices. It does not yet provide a bound for the
signed source or the high-head-null response of the actual CRT canonical
update. In particular, the uniformly bounded matched Q/P optimizer displacement
is a different vector from the canonical CRT leakage.

The new exact nested-cutoff identity isolates the remaining object:

    ||F_M-F_L||_Q^2 = L^(-2)-M^(-2) + ||r_M-r_L||_Q^2,    L|M,
    r_N = F_N - (1-1_{N divides the physical argument}).

The first term telescopes; the second does not have an established summable
bound. Its expansion retains -2<r_M,r_L>. None of the inspected results permits
that signed cross term to be discarded.

## 1. Matched optimizer control is not canonical collocation control

`RH/QSquarefreeFiniteDisplacement.lean` defines

    finitePFit N = pFit (paretoStage N) qOne,
    finiteDisplacement N = optimizer N - finitePFit N.

Both fits use the same masked squarefree legal dictionary. The actual CRT
canonical lift instead matches all divisor moments on the full divisor family
at a conductor L. Its test space is the gcd-cell space; equivalently, the
finite-difference images of the legal test vectors are used. These constructions
have neither the same defining equations nor the same target response.

Useful checked declarations and their exact limitations:

| Declaration | What is supplied | What remains |
|---|---|---|
| `finite_witness_mem_orthogonal` | `B(qOne-finitePFit N)-finiteDisplacement N` is orthogonal to `stage N` | No such reciprocal-B witness equation was found for canonical CRT leakage |
| `finite_resolvent` | `D_N-P_stage(B D_N)=movingCorrection N` | It is a change-of-metric resolvent for the two optimizers, not the collocation inverse |
| `finiteDisplacement_energy_bound` | `8*||D_N||^2 <= ||residual N||^2` | Uniform norm control of D_N does not control the different F_L or r_L |
| `finitePareto_residual_energy_bound` | `||qOne-finitePFit N||^2 <= (9/8)||residual N||^2` | An error comparison of two best fits, not a comparison with canonical collocation |
| `finitePFit_tendsto`, `finiteDisplacement_tendsto` | Norm convergence to the actual infinite optimizer/metric-displacement objects | Their limits are not proved to be qOne and zero respectively |

The prime-cutoff theorem just checked supplies a concrete test against an
incorrect identification: actual canonical norms grow at least like
sqrt(p)/log(p) along primes, while these matched optimizer displacements have
uniformly bounded Q energy. A conductor-uniform identity or bounded comparison
between these quantities cannot be assumed. A comparison restricted to the
LCM tower would require new arithmetic information.

`RH/QPrimeProjectionControl.lean` has the unconditional theorem
`finitePResidual_cube_le_prime_projection`:

    ||toPareto(qOne-finitePFit N)||^6
      <= max{ (8/(N+1))^3, 64 Z ||P_W finiteDisplacement N||^2 },

provided W contains all included prime atoms. The unresolved quantity is the
prime-visible displacement on the right. `RH/QPrimeProjectionLimit.lean`
passes this bound to the actual limits and proves equivalence of vanishing of
the prime projection and the full displacement; it does not prove vanishing.
`RH/QPrimeCarryProjection.lean` supplies the exact prime/carry orthogonal
split, with both terms retained, and norm convergence to their actual limits.

## 2. The strongest reusable inverse estimate is a different Gram problem

`RH/QSquarefreeSchurCoercivity.lean` proves
`squarefreeSchur_inverseGram_le` for the full physical-head-null screened Gram:

    b^T G^(-1)b <= coercivityConstant(H) sum_i b_i^2.

This estimate is unconditional and uniform in the outer stage N. It retains
all low squarefree conductors, including composites, and a legal high anchor.
The source of its arithmetic constant is `RH/QDivisorHeadCoercivity.lean`:

    coercivityConstant(H)
      = Z * (headDifferenceFactor(H) * mobiusMass(H))^2,
    headDifferenceFactor(H) = 2-1/H.

`Analysis/FiniteDivisorCoercivity.lean` proves
`headDifferenceFactor_bounds` and `mobiusMass_le_log`, hence

    coercivityConstant(H) <= 4 Z (1+log H)^2,    H>=1.

This is genuinely useful, but the inverse is of a screened Q Gram of anchored
physical-head vectors. It is not the gcd-moment matrix whose full inverse was
just proved unstable. To use it in a canonical update, one must construct the
corresponding signed source from the actual update equations and control the
remaining head-null response. The module explicitly leaves that source bound
open; no declaration proving it was found.

`RH/QFiniteEighthReconstruction.lean` similarly proves weighted coefficient
and reconstruction-diagonal estimates for the matched optimizer displacement.
The geometry quantity `reconstructionDiagonal N n`, and its fourth head moment,
remain on the right. Reusing these inequalities without bounding that quantity
would move the growth obligation rather than resolve it.

## 3. Exact carries do not supply their signed coefficient budget

`RH/QMatchedCRTCarry.lean` proves:

- `matched_carry_eq_deficits`: the common residual scalar cancels under a
  zero-drift Bezout certificate; the remaining signed Gram deficits survive.
- `matched_carry_eq_differences`: the same identity in difference coordinates.
- `matched_row_tail_bound`: for a legal test v with a zero physical head,

      (T+2)|<v,D_N>| <= ||v|| ||tail_T(qOne-finitePFit N)||.

- `matched_carry_tail_bound`: the floor-defined carry has head onset min(p,q),
  giving the corresponding reciprocal-tail gain.

These bounds concern pairings against the matched optimizer displacement and
require actual legal-stage membership plus a zero-head certificate. They do
not bound the norm of a canonical correction synthesized from many carries,
and do not control its possibly growing signed coefficients.

`RH/QRecursivePrimeCarry.lean` proves `carryFold_eq_sum` and
`recursivePrimeCarry_exact`. Every internal carry is multiplied by the product
of all later integer Bezout multipliers. Those products are retained exactly;
there is no bound on them in the theorem. Moreover, the certificate

    a*p + b*D = 1+t*D*p

forces gcd(D,p)=1. It cannot be used to adjoin another power of a prime already
dividing D. The ordinary digit carry in `QResidueConditional` does apply to
prime-power depth, but has different normalization and norm estimates.

`RH/QInfiniteRecursiveCarry.lean` proves absolute convergence at each fixed
physical integer n for a `NormalizedCarryChain`, under its explicit
normalization and `weight_bound`. The bound is of the form n*2^(-k). That is
not an L2(Q) dominating function in n: Q(n)*n^2 is constant, so its sum diverges.
Consequently the checked pointwise expansion alone gives no complete-Q
energy budget for the canonical update. Even a separately proved Hilbert
convergence statement for a chosen normalized carry chain would still need a
connection to the actual canonical coefficients.

## 4. Existing counterexamples block two tempting shortcuts

`RH/QResidueConditional.lean` proves:

- `conditionalValue_not_old_legal`: conditioning the new atom g_(Lp) on the
  old residue fibers gives a positive value on the old multiples cell, while
  every old legal vector vanishes there.
- `conditional_leakage_floor`: the resulting distance to every old legal
  vector has a positive complete-Q lower bound.
- `periodic_conditional_gram`: the full conditional/innovation Gram identity,
  including the zero fiber and all signed covariance terms.
- `carry_norm_sq_lower`: the unscaled digit carry obeys
  `||carry(d,p)||^2 >= (p-1)/(Z d^2)`.

Thus conditional expectation is not an old-legal-vector update, and the
unscaled carry is not uniformly small when its multiplier grows.

`RH/QCarryCoefficientEnergy.lean` proves `carry_norm_sq_upper`,
`normalizedCarry_energy_bounds`, `normalizedCarry_pointwise_tendsto_zero`, and
`normalizedCarry_weak_tendsto_zero`. These give explicit packets with growing
signed residue coefficients, bounded nonvanishing energy, and zero weak limit.
`normalizedCarry_error_minus_energy_tendsto_one` confirms that the packets do
not approximate qOne. Small pointwise coordinates or weak cancellation do
not establish strong energy convergence.

`Analysis/ScreenedCarry.lean` proves an additional exact invariance:

- `screen_carry_coefficients_eq`;
- `refit_coefficients_eq`;
- `gain_quotient_carry_eq`;
- `norm_screen_sum_carries`;
- `carry_projection_coefficients_eq`.

Once the old parent directions are screened out, all choices of Bezout
representatives have the same screened vector, enlarged-space best fit, gain
quotient, and signed block energy. Choosing smaller raw integer coefficients
cannot by itself improve the actual screened update. The genuine correlation
or Gram/source estimate must change.

## 5. Concrete remaining arithmetic task

The existing results can support an analysis of the actual source and its
screened new-conductor block, provided the exact CRT canonical equations are
used. What is still missing is a source-specific bound on either the new
leakage increment together with its correlation against old leakage, or the
canonical norm increase after each genuine prime-power admission.

A per-admission loss of size 1+O(1/p) is insufficient if charged at every new
power p^k of a fixed prime. A depth-decaying loss 1+O(1/p^k), or another proved
summable total depth budget, would be needed for that route. This is a new
arithmetic estimate to establish, not an existing premise that can safely be
silently supplied.

The published comparison remains Bagchi's full-residue density criterion and
Alouges–Darses–Hillion's explicit separation of approximation construction from
coefficient control. Neither supplies a bound for this specific CRT canonical
sequence. No noncircular provider for the missing LCM norm bound was identified
in the inspected owned declarations.
