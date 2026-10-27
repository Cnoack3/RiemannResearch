# Projection proofs and the exact remaining RH condition

Source: the user-provided prime-resampling research agenda and the two written
projection proofs recorded in `SingleConductorProjectionBound.md` and
`LegalSubspaceProjectionObstruction.md`. This continuation formalizes their
actual inverse-square-measure objects and strengthens the fixed-space result.
No claim of mathematical novelty is based merely on formalization.

## Exact setting

For positive integers n, Q(n)=1/(ζ(2)n²), g_d(n)=(n mod d)/d, and
Bf(n)=f(n)/(n+1). All norms and inner products below use this complete measure,
not a truncation. Physical sequence evaluation is the repository's `qSequence`.

## Fixed-space theorem and improvement

Let U be any fixed finite-dimensional subspace whose physical sequences are
bounded. Set W_d=U+span{g_d}. The formal result is

    ∃ C_U≥0, ∀ d≥2, ∀ f, ∀ n≥1,
      |[P_Wd B(I−P_Wd)f](n)| ≤ C_U ‖f‖ (1+log n).

`QSingleConductorUniform.exists_uniform_response_physical_bound` proves this
for arbitrary input f. Its two `stage_uniform_response_*` corollaries use
actual canonical squarefree stages and prove their boundedness hypotheses.
The weighted-energy theorem proves a complete, summable fourth-logarithm
energy bound by E_U‖f‖², uniformly in d and f.

The proof is shorter than the original written proof. With u_d=(I−P_U)g_d,
G_d=‖u_d‖², and r_d=(I−P_Wd)f, the exact projection formula is

    P_Wd Br_d = P_U Br_d + (<Br_d,u_d>/G_d)u_d.

Self-adjointness and contraction of the residual give

    |<Br_d,u_d>/G_d| ≤ ‖Bu_d‖ ‖f‖ / G_d.

The complete arithmetic estimates provide
‖Bg_d‖≤1/d, E_Q[g_d]≤(2+log d)/(ζ(2)d), and
‖g_d‖²≥(d−1)/(ζ(2)d²). Uniform evaluation on U implies
‖P_Ug_d‖=O_U(log d/d), so G_d≥1/(4ζ(2)d) eventually.
The physical estimate follows from
(2+log d)g_d(n)≤2+log n and boundedness of (2+log d)²/d.
Finitely many small conductors are handled without assuming a Gram lower
bound at those conductors.

A further formal strengthening is Hilbert operator-norm convergence:

    ‖P_Wd B(I−P_Wd) − P_U B(I−P_U)‖ → 0.

`QSingleConductorOperatorDecay` proves this and the actual fixed-stage
specialization. `Analysis.SingleDirectionResponseDifference` first proves
the exact signed difference, then bounds its operator norm by
2‖Bu_d‖/‖u_d‖, which tends to zero. The limit is the response of U;
it is not asserted to vanish.

**Scope:** C_U and E_U may depend on the entire fixed space U. In the stage
corollaries they may depend arbitrarily on N. No uniform estimate over the
growing canonical stages follows from these results. The general complete
bounded-subspace evaluation lemma is not presented as an additional source
of infinite-dimensional examples.

## Actual legal-subspace obstruction

For prime d>3 let

    W_d=span{g_2, g_3+10√d g_d},
    r_d=(I−P_Wd)1,  b_d=P_Wd Br_d.

`QLegalMixedConductorMoments.mixedSpace_le_legalSpan` proves actual
squarefree legality; the parity atom is in W_d. The subsequent modules
use these actual residuals and corrections throughout.

The complete deterministic conclusions are:

- ‖r_d‖≤1/2 and ‖b_d‖≤1/8.
- For a(n)=n/(8+log n)², the raw-source weighted energy is at most 1/1024.
- The complete weighted correction energy E_Q[a b_d²] tends to infinity.
  Its defining series is summable for every sufficiently large d.
- At n_d=(d+1)/2, for every fixed m and L, the prime-two correction
  increment exceeds L log 2 (6+log(d+1))^m at arbitrarily large prime conductors.
- No C≥0 controls E_Q[a b_d²] by
  C(E_Q[a(Br_d)²]+‖r_d‖²) over these legal squarefree subspaces.

The proof retains the exact actual coefficient

    β_d=(D_d G_d−a_d E_d)/G_d²,

before using estimates. All the eventual Gram, target, source, and
reciprocal-energy conditions for β_d≥7/(36·303²) are proved from the
actual vectors. The physical remainder bound is 4, a deliberately looser
constant than the paper's bound 1, sufficient for both divergences.
The energy proof uses a finite block inside [d/4,d/2], then explicitly
compares it with the summable complete weighted energy. No unproved
coefficient or decomposition is left as a premise of the final obstruction.

**Scope:** these are varying two-dimensional legal subspaces. They are not
the canonical full initial spans. Their failure rules out arguments based
only on legality and inclusion of g_2; it does not refute the canonical RH
provider. The formal energy exponent here is 2. The written extension to
all real logarithmic exponents greater than 1 is not claimed as a separate
Lean theorem.

The paper's resampling Dirichlet-form conclusions require the actual
countable prime-resampling construction and its Poincaré inequality.
The required missing providers are the actual kernel identification,
reversibility and exit-rate/exhaustion proofs, and the spectral-gap-one L²
Poincaré inequality. The limiting resampling criterion additionally needs
its extended L¹ form. Existing finite symmetric-kernel source bounds do
not instantiate these countable-kernel obligations.
The deterministic weighted-energy conclusions do not by themselves certify
that probabilistic layer. In particular, the paper's raw Dirichlet bound
1/128 and Dirichlet transfer failure must not be confused with the proved
weighted-energy statements above.

## Verified criterion and unresolved RH provider

Let V_N be the actual canonical squarefree stage, V its closure,
r=1−P_V1, and b_N=P_VN B(1−P_VN1). The strengthened sparse criterion needs
only one prime-factor parent of each integer:

    ∃ m∈ℕ, L≥0, ∀ n>1, ∃ prime p, q>0 with pq=n,
      for arbitrarily large N,
      |b_N(n)−b_N(q)| ≤ L log p (6+log n)^m.

The constants L and m are common to all n. The parent and the cofinal set
of stages may depend on n. The estimate is on the actual canonical
corrections, not arbitrary sequences or a substituted projection family.

`QSquarefreePrimeIncrement.riemannHypothesis_of_frequently_moving_prime_parent_increments`
concludes the literal Mathlib `RiemannHypothesis` from this condition.
For every fixed m and L>0,
`residual_zero_iff_frequently_moving_prime_parent_increments` proves that
this condition is equivalent to r=0. An equivalence does not establish
either side. No RH-to-squarefree-density converse is asserted here.

The dependency audit follows the complete physical polylogarithmic envelope
to the logarithmically scaled residual-tail criterion, the actual Q-to-Pareto
continuous inclusion, the legal-closure Mellin identity, and the proved
zeta reflection/strip equivalence. The unconditional Möbius defect-energy
estimate retains its factor N; it is not misread as norm convergence.

**Open:** prove the displayed common-L,m provider for the canonical stages,
or another previously verified residual-vanishing condition. Neither the
fixed-space theorem nor the noncanonical obstruction closes this obligation.
No unconditional proof of RH is obtained.

## Verification boundary

The Lean source is exported by `RiemannResearch.lean`; final publication
requires the server checkpoint's aggregate and changed-module validation.
Saved-module verification and the principal theorem/axiom audit succeeded
in server job `job_84v817miHsxCX18U2EnwUuu4-1J84882`. All inspected
principal results and the audited RH dependency chain report exactly
`propext`, `Classical.choice`, and `Quot.sound`; no project axiom or proof
placeholder occurs in these transitive dependencies. Definition lookup
resolved `RiemannHypothesis` to Mathlib/NumberTheory/LSeries/RiemannZeta.lean,
not a project replacement. The final response records the terminal verification job and
published commit. Markdown derivations outside the stated formal scope
are not certified by a Lean build.


Timing distinction: workspace-opening request round trip was 72.219 seconds.
The successful saved-module audit's server duration was 36.178 seconds,
including dependency-module preparation/compilation and the inspection
snippet. Its reported queue delay was approximately 0.001 seconds.
The client observed completion after 94.701 seconds because polling obeyed
the server's 30- then 60-second retry intervals. These measurements are not
interchangeable and are not reported as pure kernel-checking time.
