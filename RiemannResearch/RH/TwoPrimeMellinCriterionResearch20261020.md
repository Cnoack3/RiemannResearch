# Two-prime Mellin criterion and signed-sieve investigation

20 October 2026. Source: the user-provided `PrimePowerTargetsResearch20261020.md`,
Section 2, and the present request. This is a conditional research reduction,
not a proof of RH.

## 1. Existing target infrastructure reused

The starting workspace is based on main commit
`a429a47ebfb7c10d5b8bebf8b1e2a32a554f8d27`, which is later than the cited
`75271daadaab4e33d7bf3c124be2713e3ac333a8`.
It already contains the actual target construction and transform:

- `RH/PrimePowerHilbertTarget.lean` constructs the unique contraction fixed
  point with physical coordinates F_p(n)=Nat.log p n, for every integer p>1.
  The exact Pareto mean is 1/(p-1) and the exact Pareto norm square is
  (p+1)/(p-1)^2.
- `RH/PrimePowerTargetMellin.lean` constructs `qTarget p hp` by `encodeQ`,
  proves `primePower_q_square_summable`, and identifies its Pareto image
  with that same fixed point. In particular, F_2 and F_3 are actual complete-Q
  vectors, with F_p(0)=0 and physical coordinates floor(log_p n).
- Its complete-Q bound is
  ||F_p||_Q^2 <= 2(p+1)/(zeta(2)(p-1)^2).
- Its exact normalized Mellin identity, `paretoTarget_mellin_exact`, is
  Phi_s(F_p)=s M_s(F_p)=1/(p^s-1), for Re(s)>1/2.

These declarations are reused, not duplicated under new target names.
`QMellinTransfer.qMellinContinuous` supplies the actual continuous Mellin
functional on Q; `ZetaTwoParetoTransfer.toParetoCLM` supplies its physical
norm transfer.

## 2. Newly formalized conditional theorem

Let H=`ZetaTwoOptimizerStage.closure`, the complete-Q closed real span of
all squarefree legal residue atoms. Define

C = closure(H + R*1).

The literal Lean object is
`(H ⊔ Submodule.span ℝ {qOne}).topologicalClosure`.
Thus every constant coefficient is real, and the closure is the norm
closure of the actual complete-Q Hilbert realization.

The new module `RH/PrimePowerTwoTargetCriterion.lean` proves

    qTarget 2 ∈ C -> qTarget 3 ∈ C -> RiemannHypothesis.

The exact declaration is

`PrimePowerTarget.riemannHypothesis_of_two_targets_mem_closureWithConstants`.

Its proof has no unproved Mellin, summability, zero-free-region, or
injectivity providers:

1. For an actual zero zeta(s)=0 with Re(s)>1/2 and s!=1, M_s vanishes on H,
   using the existing continuous physical Mellin annihilator.
2. The continuous real functional f -> Im(s M_s(f)) vanishes on H and on
   real constants. Its closed kernel therefore contains C.
3. Membership of F_p gives Im(1/(p^s-1))=0. Conjugation and injectivity
   of inversion give Im(p^s)=0.
4. If this holds at 2 and 3, conjugation gives equality of the negative
   complex powers of s and conj(s) at both bases. The existing
   `ArithmeticConductorCommonZeros.two_three_cpow_neg_injective` gives
   s=conj(s), hence Im(s)=0.
5. `RH/RealZetaNonvanishing.lean` excludes positive real zeros away from
   the pole. It applies the already proved first Mellin-difference series
   for g_2: all real summands are nonnegative, and the first is positive.
6. The existing right-half-strip zero-free equivalence concludes literal
   Mathlib `RiemannHypothesis`.

**Open:** F_2∈C and F_3∈C. Neither is inferred from radical-jump constraints,
pointwise convergence, or finite interpolation. No converse is claimed.

## 3. Separate checked finite signed-sieve identities

The new module `RH/QPrimePowerSignedSieve.lean` studies actual signed
finite combinations, for every prime p:

    B = sum_{H in S} w_H A_{p,H},
    A_{p,H} = sieveVector (primorial H) p.

Every B is in the finite squarefree legal span. All squarefree divisors
in each raw sieve synthesis are retained.

Write a_{p,H}=sieveSlope(primorial H,p). If every H in S is at least
max(p,x), then for all n<=x the exact head identity is

    B(n) = (sum w_H) F_p(n) - n sum w_H a_{p,H}.

Consequently the two finite balance conditions

    sum w_H=1,       sum w_H a_{p,H}=0

give an exact F_p head. The module proves that these conditions require
at least one negative coefficient, since every a_{p,H} is strictly positive.

The exact complete-Q energy is

    ||B||_Q^2
      = sum_{H,K in S} w_H w_K <A_{p,H},A_{p,K}>_Q.

This is the full infinite Q Gram energy, including all signed cross terms.
It is not a finite-head norm or a truncated tail estimate.

**Open:** find balanced growing-head choices with a uniform bound on this
complete Gram expression. Finite balance alone supplies no such bound.
The existing full-divisor-dictionary constrained optimizers can only improve
the energy of feasible signed seeds; their growing-head uniform bound is
also open.

## 4. Further ordinary analysis: bounded signed averaging is still obstructed

The arguments in this section are ordinary mathematical deductions, not
new Lean declarations. They sharpen the earlier positive-averaging warning.

Fix 1/2<sigma<1. The exact finite Euler-product Mellin identity of the
ordinary sieve is

    Phi_sigma(A_{p,H})
      = zeta(sigma) [
          p^(-sigma) product_{q<=H,q!=p}(1-q^(-sigma)) - a_{p,H} ].

Both products tend to zero: for q>=2, q^(-sigma)>=1/q, and the classical
prime harmonic product tends to zero. Hence Phi_sigma(A_{p,H})->0,
whereas Phi_sigma(F_p)=1/(p^sigma-1)>0.

Consider finite signed rows w_{j,H} satisfying

    sum_H w_{j,H} -> 1,
    sup_j sum_H |w_{j,H}| < infinity,
    for each fixed M, sum_{H<=M} |w_{j,H}| -> 0.

These regular signed rows preserve every convergent scalar limit.
Therefore B_j=sum_H w_{j,H} A_{p,H} converges pointwise to F_p, while
Phi_sigma(B_j)->0.

If a subsequence of B_j had bounded complete-Q norm, Hilbert-space weak
subsequence compactness would give a weak limit. Continuous coordinate
evaluations force that limit to be F_p; Mellin continuity then forces
Phi_sigma(F_p)=0, a contradiction. Thus ||B_j||_Q->infinity.
Adding constants c_j*1 with c_j->0 does not change this obstruction.

In particular, for x<y with a=a_{p,x}>b=a_{p,y}>0, the familiar signed
two-stage correction is

    T_{p;x,y} = (a A_{p,y} - b A_{p,x})/(a-b).

Its coefficient total variation is exactly

    (a+b)/(a-b).

If both cutoffs tend to infinity and b/a<=theta<1, the total variation is
bounded by (1+theta)/(1-theta); the preceding argument rules out norm control.
Thus any uniformly norm-bounded moving two-stage family would have to
satisfy b/a->1, forcing its coefficient total variation to diverge.

This does not prove norm control, or rule it out, in that near-equal-slope
regime. It isolates the needed stronger cancellation. Redesigning individual
conductor coefficients, or using the complete constrained optimizers,
is outside the bounded-total-variation averaging obstruction.

## 5. Verification ledger

The coherent conditional-theorem source check
`job_5HyIr2vY7-zwpZc13Nh6CLRdumWgY69C` succeeded with verified=true and exit 0.

Standalone staged-module import check
`job_ZtiduMFytOiXGO3pUEfgIRraXHMF4N98` built both new criterion modules and
succeeded with verified=true and exit 0. It inspected the real nonvanishing
lemma, the reused square-summability and exact transform, and the final
conditional RH theorem. All used only propext, Classical.choice, Quot.sound.

Separate coherent signed-sieve job
`job_JVh7lckC1sH3Q3a1EWRBSWidRscovVff` succeeded with verified=true and exit 0.
Staged import/axiom audit `job_nxyYWe9s5HW5wuXUeMo5GjLSkmiq764R` succeeded
with verified=true and exit 0. It imported all three new modules and checked
the final conditional theorem and the principal signed-sieve declarations;
each used only propext, Classical.choice, Quot.sound.
The final publication checkpoint is recorded
with the published result. Accepted or queued jobs are not verification.
No finite numerical computations are offered as evidence for the open bounds.
