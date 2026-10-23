# Single-test normalization and finite-support dual continuation

Research continuation for Christian Noack, 22 October 2026.

## Result and remaining obligation

The attached UnitSignalBoundednessAudit20261022.md has been followed into
two further formal reductions. Neither supplies an unconditional RH proof.

1. The complete error of a unit-signal optimizer can be recovered from one
   nonzero legal test. For sampled admissible vectors, an exact formula retains
   both the squared sampling displacement and its signed testing correction.
   Vanishing of this one testing discrepancy and of sampling displacement
   implies strong target convergence, without a prior projection-limit or
   uniform-norm assumption.
2. A uniform inequality on finitely supported test vectors is equivalent to
   membership in the actual closed full legal Q span. For the constant target,
   any finite testing constant can be replaced by 1 once membership is proved.

The missing arithmetic provider remains Open. Compactness, a fixed competitor,
and increasingly accurate sampling do not provide that provider.

## 1. Exact identities

Let y be the target, m = ||y||^2, p its projection onto a legal trial space,
kappa = ||p||^2 > 0, and U = (m/kappa)p. Let v belong to that same trial
space and let s = <y,v> be nonzero. Then

    ||U-y||^2 = (m/s) <U-y,v>.

For any admissible F (the true signal and complement constraints of
ProjectionSignalModel.Admissible), the exact identity is

    ||F-y||^2 =
      (m/s)<F-y,v> + ||F-U||^2 - (m/s)<F-U,v>.

The final term is signed and must be retained. Independently of admissibility,
every F satisfies

    <F-y,v> = (m/kappa-1)<y,v> + <F-U,v>.

These statements are saved in Analysis/UnitSignalProjection.lean:

- optimizer_error_eq_single_test
- admissible_error_eq_single_test
- sampled_single_test_bias_split

The new admissible_tendsto_of_single_test assumes a fixed target, fixed mass,
one fixed test with nonzero target pairing that is legal in every trial space,
true admissibility, <F_j-y,v> -> 0, and F_j-U_j -> 0 in norm. Its conclusion
is F_j -> y strongly. It does not assume that the projections already converge.

The two further declarations
normalized_residual_single_test_iff_energy_eq_mass and
optimizer_single_test_iff_energy_eq_mass express finite and limiting energy
saturation through one test. The latter assumes the projection limit exists.

## 2. Concrete interpretation for the attached P-normalization

For y=1 under P and v=g_2,

    s = log(2)/2,
    ||U_j-1||_P^2 = (2/log(2)) <U_j-1,g_2>_P,
    <F_j-1,g_2>_P =
      (log(2)/2)(1/kappa_j-1) + <F_j-U_j,g_2>_P.

The abstract identities are formalized. The numerical evaluation
<1,g_2>_P=log(2)/2 is recalled from the audit, not newly formalized here.

Sampling heights can make the final displacement term vanish. The remaining
bias is exactly proportional to 1/kappa_j-1. Thus treating the whole parity
discrepancy as sampling error would assume the desired energy saturation.

All identities use one fixed inner product. A P-optimizer must not be treated
as a Q-optimizer merely because P and Q have equivalent norms.

RH/QUnitSignalTargetTest.lean supplies
riemannHypothesis_of_sampled_single_test for genuine Q projection models.
Besides the general hypotheses above, it requires each F_j to belong to the
actual full legal residue span. Strong convergence then feeds the existing
Q closure-to-RH theorem. This is a conditional research reduction.

## 3. Dense testing and finite support

For an orthogonally complemented real Hilbert subspace V, a target y, and any
dense family D of tests, the new general theorem proves

    y in V  iff  exists C, for every a in D,
      |<y,a>| <= C ||P_V a||.

Proof: membership gives <y,a>=<y,P_Va> and Cauchy-Schwarz. Conversely the
inequality extends by continuity to all tests. For r=y-P_Vy, the denominator
is zero, while <y,r>=||r||^2. Hence r=0.

This is Analysis/DenseProjectionTesting.mem_iff_dense_test_bound.

In the actual Q Hilbert realization, finiteHead M a is the finite sum of
coordinate atoms through the first M physical coordinates. The new module
RH/QFiniteSupportDualCriterion.lean proves its strong convergence to a,
its vanishing beyond its finite support, and density of these tests.

For the actual closed full legal span V, the principal specialization is

    1 in V  iff  exists C, for every M and a,
      |<1,finiteHead M a>_Q| <= C ||P_V(finiteHead M a)||_Q.

The unit-constant version is also equivalent to membership. Finite-support
tests are not asserted to be legal residue approximants. Only their
projections enter the right side.

The conditional RH declaration is riemannHypothesis_of_finite_test_bound.
The contrapositive not_RH_finite_test_violation proves: if RH is false, every
proposed constant C is violated by some finite-support test. This does not
assert a numerical algorithm to find that test.

## 4. Arithmetic formulation to investigate next

The following matrix descriptions are explanatory mathematical derivations,
not additional new Lean declarations in this continuation.

In this section a(n) denotes physical sequence values, rather than normalized
lp coordinates. For a finite dictionary D of distinct conductors >=2, let

    G_D(d,e) = <g_d,g_e>_Q,
    b_D(a)_d = <a,g_d>_Q.

Finite-dimensional projection and exhaustion give

    ||P_V a||_Q^2 = sup_D b_D(a)^T G_D^(-1) b_D(a).

Thus the arithmetic target can be written

    |sum_n Q(n)a(n)|^2
      <= C^2 sup_D b_D(a)^T G_D^(-1) b_D(a)

uniformly over all finite-support a, with one C. The complete Q Gram matrix
must be used, including all infinite periodic tails.

Equivalently, put e_n=1_{n}/sqrt(Q(n)),
t_M=(sqrt(Q(n)))_{1<=n<=M}, and
K_M=(<P_V e_n,e_m>_Q)_{m,n<=M}. The required rank-one matrix inequality is

    t_M t_M^T <= C^2 K_M.

When K_M is positive definite, it is equivalent to
sup_M t_M^T K_M^(-1)t_M < infinity. A uniform lower bound for every eigenvalue
of K_M is unnecessary: only this target direction must be controlled.

Open research tasks:
- Prove the uniform target-direction inverse-Gram bound, or a complete signed
  head-repair estimate implying it.
- Alternatively prove the single-test bias tends to zero from an arithmetic
  identity independent of energy saturation.
- Keep phase/sampling discrepancy separate from the deterministic bias.
- Preserve the signed term in the sampled error identity when estimating it.

## 5. Why valuation independence does not close the parity estimate

This paragraph is an ordinary calculation, not newly Lean-formalized here.
Let A=sum_{k>=0}(3k+1)^(-2), B=sum_{k>=0}(3k+2)^(-2), and Z=zeta(2).
Termwise comparison gives A>B. Direct summation gives

    E_Q g_3 = (A+2B)/(3Z),
    E_Q[1_even g_3] = (2A+B)/(12Z),
    Cov_Q(1_odd,g_3) = (B-A)/(12Z) < 0.

Consequently g_2 and g_3 are dependent even though the conductors are coprime.
Independence of prime valuations does not supply independence of residue
functions or preservation of the legal space under conditional expectation.

## 6. Verification and provenance

Source: the user-provided boundedness audit and standard Hilbert projection
arguments. No mathematical novelty is claimed. Classical background on the
Hilbert-space RH criterion is Bhaskar Bagchi, "On Nyman, Beurling and
Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis",
https://arxiv.org/abs/math/0607733. That reference does not supply the missing
arithmetic estimate above.

The coherent development submission
job_Vg8JI9Yrq8wUJhW31ad6kjnOGCWer1mo completed with exit code 0.
Its server-reported checking duration was 6.559 seconds; queue delay was
approximately 0.002 seconds. Earlier candidates had tactic, type-inference,
or declaration-lookup errors that were repaired. These timings exclude
workspace opening and the deliberate polling interval; the workspace-opening
round trip was not independently measured.

The saved-source import and axiom audit succeeded in
job_ayKkS5VXG_6UzG0tkXnkgqjxbuTvbm3q, exit code 0, with a server-reported
verification duration of 16.228 seconds and queue delay below 0.01 seconds.
All fourteen audited declarations, including both RH conclusions, reported
only propext, Classical.choice, and Quot.sound. There were no unfinished proofs
or project-local axioms. A pre-existing copyright-header style warning remains.

Final affected-source validation and publication are governed by the checkpoint
receipt. RH remains unproved; the scalar limit and uniform finite-test
bound are explicitly Open.
