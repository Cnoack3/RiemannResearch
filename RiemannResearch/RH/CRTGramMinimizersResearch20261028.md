# Constrained CRT Gram minimizers: certified finite gains and the uniform gap

28 October 2026. Base: `5ecd057b363caa6866b9b53537efa538161c68b7`.
Source: the user's request to optimize signed legal squarefree exact-head CRT approximants.

## Outcome and status

Signed correction dramatically improves the explicit coprime-counting seed at every nontrivial tested stage. Four finite minima now have exact rational certificates. Numerical full-tail computations extend through period 9,699,690. No bound uniform in the stage is proved, and divergence of the optimized family is not proved either.

The new `QCRTGramMinimizer.lean` connects the actual CRT seed to the existing exhaustive affine Gram machinery, distinguishes least norm from least approximation error, proves their squared displacement is bounded by the target tail, and proves the forced value 2 at an omitted prime. All Hilbert norms are the actual complete Q norms.

The decimal intervals below are rigorous rational-computation certificates with the paper proof described here and in the experiment README. They have NOT been turned into Lean declarations. Floating-point rows and conditioning checks are numerical evidence only.

## Full-tail numerical results

Let U minimize ||F||²_Q with exact head F(n)=1 for n<=H. The period is a primorial and H is one less than its next prime.

| L | H | Minimum norm² (numerical) | CRT seed norm² (numerical) | ||1-U||² (numerical) |
|---:|---:|---:|---:|---:|
| 6 | 4 | 1.0816442631 | 1.0816442631 | 0.0642517914 |
| 30 | 6 | 1.0734675033 | 2.3043596804 | 0.1096925992 |
| 210 | 10 | 1.0355550151 | 9.1377011840 | 0.0850096178 |
| 2,310 | 12 | 0.9838254108 | 77.2549946943 | 0.0628746605 |
| 30,030 | 16 | 1.0192543276 | 847.6057655417 | 0.0554012495 |
| 9,699,690 | 22 | 0.9954237043 | 217432.3579509589 | 0.0351512920 |

Each complete Gram entry uses periodic trigamma weights, not a cutoff in n. Wolfram independently reproduced the first two minima with 40-digit working precision:

- L=30: 1.073467503259688635559254561...
- L=210: 1.035555015131790242495017275...

The corresponding double-precision calculations used an independent nullspace solve and pairwise lcm-period checks. Across all seven stages the alternative solves differed in energy by less than 9e-16. Representative Gram entries agreed to relative error below 2.5e-15. The largest full Gram condition number was about 8.67e7, and the largest reduced Gram condition number about 1.11e7. These are diagnostics, not interval certificates.

## Exact rational certificates

| L | H | Certified lower bound for minimum | Certified upper bound for minimum |
|---:|---:|---:|---:|
| 30 | 6 | 1.073467493 | 1.073467514 |
| 210 | 10 | 1.035555014 | 1.035555017 |
| 2,310 | 12 | 0.983825410 | 0.983825411 |
| 30,030 | 16 | 1.019254327 | 1.019254328 |

Every endpoint is an exact rational terminating decimal. A feasible rational coefficient vector provides each upper bound. A rational Gram minorant, exact head-nullspace rank checks, and a positive rational LDL decomposition provide each lower bound for the TRUE constrained minimum, not merely for a trial vector.

All rounding remainders are enclosed. The infinite residue tails are bounded by elementary integral comparisons, and zeta(2) is enclosed rationally. No floating-point trigamma value enters the verification. Arbitrary signed coefficients are allowed because matrix comparison is established in Loewner order from positive rank-one residue terms.

The below-one value is consistent with the problem: a finite head does not force the complete squared norm to be at least one. The rise from L=2310 to L=30030 proves that the natural expanding-head diagonal is not monotone.

## The two optimization objectives

Write V for the exact-head minimizer of ||1-F||²_Q. Numerical comparisons are:

| L | ||1-U||² | ||1-V||² | ||V-U||² |
|---:|---:|---:|---:|
| 6 | 0.0642517914 | 0.0642517914 | 0.0000000000 |
| 30 | 0.1096925992 | 0.0606315610 | 0.0490610382 |
| 210 | 0.0850096178 | 0.0425021768 | 0.0425074410 |
| 2,310 | 0.0628746605 | 0.0196299220 | 0.0432447385 |
| 30,030 | 0.0554012495 | 0.0263872455 | 0.0290140040 |
| 510,510 | 0.0408867337 | 0.0117632877 | 0.0291234460 |
| 9,699,690 | 0.0351512920 | 0.0117691076 | 0.0233821844 |

The new Lean results certify the identities (not the displayed numerical values)

    ||V||² = ||U||² + ||V-U||²,
    ||1-U||² = ||1-V||² + ||V-U||²,
    ||V-U||² <= ||1-finiteHead(H,1)||² = Q(n>H).

Thus the two optimizers become close as the head grows, without any uniform-energy assumption. This does not bound ||U|| or ||V||. Error minima are also nonmonotone along the tested maximal-head stages.

## Lean scope

Module: `RiemannResearch/RH/QCRTGramMinimizer.lean`, namespace `RiemannResearch.RH.QCRTGramMinimizer`.

- `optimizer_feasible`: actual divisor-stage membership and the exact physical head, under an explicit prime-cover hypothesis.
- `completion`, `norm_completion`: exhaustive affine minimization and the full norm-square remainder for every feasible competitor.
- `energy_schur`, `optimizer_normal`: signed inverse-Gram value and normal equations in the compensated residue basis.
- `seed_energy_gain`, `energy_le_seed`: exact saved energy relative to the explicit CRT seed and its consequence.
- `objective_norm_gap`, `objective_error_gap`, `objective_gap_le_tail`: exact comparison of the two objectives and its unconditional tail bound.
- `missing_prime_value`: if p is prime, p does not divide L, and a divisor-stage vector equals 1 on every positive n<p, its value at p is exactly 2.
- `riemannHypothesis_of_bounded_energy`: CONDITIONAL research reduction. Open provider: a single finite B bounding `energy (N+1) (L N) (hL N)` for every N, with squarefree periods and the stated prime cover. The proof converts a squared-norm bound B to a complete error bound 2+2B and invokes the existing consumer. It does not prove hbudget.

Existing reused results include `QResidueHeadSpace.affineOptimizer_error_decomposition`, its independence theorem, `NormalizedResidueExactHeadCharges.residueFraction_zero_head_iff`, the coefficient extraction lemmas, and `QCRTCoprimeApproximation.coprimeApprox_exact_head`. The generic affine theory was already present; this development does not claim it as a new mathematical discovery.

Final isolated verification: job `job_4D6n8TMt3j3dVL5jcUzXyiV7ikIfpgbQ`, exit code 0, reported verification duration 6.895 seconds. The principal normal-equation, objective-tail, missing-prime, and conditional-RH declarations report only `propext`, `Classical.choice`, and `Quot.sound`. Request/queue/polling latency is separate from this verification time; workspace-opening elapsed time was not individually measured. Publication is gated by the subsequent final checkpoint, whose terminal job and commit are reported in the chat.

## Reproducibility

Experiment files are in the accompanying [CRT_Gram_Minimizers_Computations_2026-10-28.zip](https://chatgpt.com/library?file_id=libfile_80d99f68d3e88191b23ac720cfc32e9a&account_id=personal) bundle. The bundle contains `certificates/` and `numerics/` directories, including exact witnesses and completed verification logs.

- In `certificates/`, run `python exact_crt_certificate.py` and `python exact_minimum_certificate.py`. Only Python's standard library is required. Rational witness JSON files are committed. The optional `--discover` uses NumPy/SciPy only to propose witnesses.
- In `numerics/`, run `python primorial_gram.py --ks 2 3 4 5 6 7 8`, then `python crosscheck.py` and `python objective_comparison.py`. This regenerates local NPZ matrices and requires NumPy/SciPy. The largest stage enumerates a full period of 9,699,690 residues in blocks.
- JSON files record results. The downloadable bundle also includes NPZ matrices and coefficient caches. Both exact rational verifier scripts completed with exit code 0 on the final rerun.

## Exact derivation and limit audit

Let L be squarefree, D={d:d|L,d>1}, g_d(n)=(n mod d)/d, Q(n)=1/(zeta(2)n^2), F_c=sum_{d in D}c_d g_d. Let H be positive, suppose every prime at most H divides L, and suppose D_>={d in D:d>H} is nonempty. For the maximal primorial head H=p_next-1 these conditions hold starting at L=6.

## 1. Exact head constraints collapse to fixed coefficients and one equation

Put S(c)=sum_{d in D}c_d/d. Since g_d(0)=0 and

    g_d(n)-g_d(n-1)=1/d-1_{d|n}   (n>=1),

we have

    F_c(n)-F_c(n-1)=S(c)-sum_{d in D,d|n}c_d.

Consequently F_c(n)=1 for 1<=n<=H if and only if

    c_d=-mu(d) for d in D, d<=H,
    sum_{d in D}c_d/d=1.

Necessity: F_c(1)=S(c)=1; differences then give sum_{d|n,d>1}c_d=1 for 2<=n<=H, and induction over squarefree n gives c_n=-mu(n). Sufficiency: for every n<=H all squarefree divisors of n belong to D, and sum_{d|n,d>1}(-mu(d))=1 for n>1.

The first missing prime p makes a head reaching p impossible: F_c(1)=1 forces S(c)=1, but F_c(p)-F_c(p-1)=S(c)=1. Thus the maximal possible initial head is at most p-1. The special case L=2 cannot attain its nominal p_next-1=2 head because F_c(L)=0.

In particular all exact-head families automatically have coefficient convergence c_d -> -mu(d) at every fixed squarefree d. This coefficient convergence by itself supplies no energy bound.

A rational feasible seed is

    c^0_d=-mu(d)+phi(L)1_{d=L},

because sum_{d|L}mu(d)/d=phi(L)/L. For H<L its fixed small coefficients are correct and S(c^0)=1. This is the corrected coprime-counting construction.

## 2. Complete Gram matrix and positive definiteness

The complete Gram matrix is G_de=<g_d,g_e>_Q, with exact periodic representation

    G_de = 1/(zeta(2)L^2) sum_{a=1}^L psi_1(a/L) g_d(a)g_e(a).

The term a=L vanishes. Alternatively replace L by lcm(d,e) in each entry. This identity includes every infinite Q-tail.

The atoms are linearly independent. If F_c=0 then S(c)=F_c(1)=0 and all divisor sums sum_{d|n}c_d vanish. Induction over d in D gives c_d=0. Thus G is symmetric positive definite, as is each principal block.

## 3. Reduced exact Schur formula

Write c=(a,x), with a_d=-mu(d) for d<=H and x indexed by d>H. Partition

    G=[A B; B^T C], u_d=1/d (small), v_d=1/d (large),
    beta=1-u^T a=sum_{d<=H}mu(d)/d,
    b=B^T a, k=v^T C^{-1}v>0, alpha=beta+v^T C^{-1}b.

The unique optimum is

    x*=-C^{-1}b+(alpha/k)C^{-1}v,
    E*=a^T A a-b^T C^{-1}b+alpha^2/k.

The proof is completion of the square with the single constraint v^T x=beta. No signs have been discarded. The term -b^T C^{-1}b records exactly the signed improvement that an absolute-value tail estimate would lose.

For any feasible c0, let Z have columns forming a basis of the free correction space: corrections vanish on d<=H and satisfy sum z_d/d=0. With K=Z^T GZ and s=Z^T Gc0,

    c*=c0-Z K^{-1}s,
    E*=c0^T Gc0-s^T K^{-1}s.

K is positive definite when the correction space is nonzero. In dimension zero c0 is the unique feasible vector and no inverse is used. For any correction h in that space,

    E(c*+h)=E(c*)+h^T Gh.

For L=30,H=6 the correction dimension is 2. For L=210,H=10 it is 8.

## 4. KKT and primal-dual certificates

Let R c=y be any independent constraint representation (fixed small coordinates and the reciprocal row give one). Then

    Gc*=R^T lambda, Rc*=y,
    E*=y^T(RG^{-1}R^T)^{-1}y.

For any feasible c and any multiplier lambda,

    2 lambda^T y-lambda^T RG^{-1}R^T lambda <= E* <= c^T Gc.

The dual gap is the squared G-distance from c to G^{-1}R^T lambda. Floating-point solutions become genuine certificates only after feasibility and full-tail inequalities are established rigorously.

## 5. Rational full-tail enclosures retain all signed cross terms

For each residue a, after J complete periods put x=a+JL. Monotone-integral comparison gives

    1/(Lx) <= sum_{j=J}^infinity 1/(a+jL)^2 <= 1/(Lx)+1/x^2.

Add the finite rational sum j=0,...,J-1. Multiplying each scalar interval by the positive semidefinite outer product (g_d(a))_d (g_d(a))_d^T and summing gives rational Loewner enclosures for zeta(2)G. Rational upper/lower bounds on zeta(2) give G^- <= G <= G^+. This matrix ordering remains valid with arbitrary signed coefficient vectors.

A rational feasible c gives E* <= c^T G^+ c. A positive definite G^- and any rational multiplier lambda give

    E* >= 2 lambda^T y-lambda^T R(G^-)^{-1}R^T lambda.

The latter direction follows from (G^-)^{-1} >= G^{-1}. These are fully rational finite certificates; the inequalities producing the enclosure must be proved separately or formalized.

## 5A. Minimum norm and minimum error are different objectives

The numerical experiment minimizes ||F||_Q^2. Existing squarefree affine projection infrastructure also supports minimizing ||F-1||_Q^2. These objectives generally give different finite-stage coefficients: one must not replace one by the other using the unconstrained projection identity <F,1>=||F||^2, which need not hold for an affine exact-head minimizer.

Nevertheless their difference has an exact, vanishing bound. Let K be the legal head-zero correction subspace and P_K its orthogonal projection. For any feasible seed F0,

    F_N=F0-P_K F0,
    F_E=F_N+P_K 1,
    ||F_E-F_N||^2=||P_K1||^2 <= Q({n>H}),
    ||F_E||^2-||F_N||^2=||P_K1||^2,
    ||F_N-1||^2-||F_E-1||^2=||P_K1||^2.

The first two formulas are affine projection. The third uses P_K1=P_K1_{n>H}, since every element of K vanishes on the head, and orthogonal projections are contractions. The remaining identities are Pythagorean. Thus the two objectives produce asymptotically identical functions on expanding heads, even when no uniform energy bound is known. Their norm-energy budgets differ by at most the tail mass.

The repository already contains the abstract affine optimizer, its error decomposition and its minimizing property in QResidueHeadSpace, with the target-one specialization in QSquarefreeAffineHead (as identified by the coordinating agent). New formal work should instantiate that theory at target zero and the actual CRT seed, rather than duplicate generic Hilbert-space optimization.

## 6. What a uniform bound does and does not mean

Let L_m be primorials, V_m=span{g_d:d|L_m,d>1}, V=closure(union V_m), and define E_{m,H} as the constrained minimum, infinity when infeasible. For fixed H, E_{m,H} decreases in m. For fixed m, it increases with H on its feasible range. The natural diagonal E_{m,p_next-1} need not be monotone.

For fixed H let

    E_{infinity,H}=min{||F||_Q^2:F in V,F(n)=1 for n<=H}.

Then E_{m,H} decreases to E_{infinity,H}. Proof: the finite trace map T_H:V->R^H is continuous. The image of the algebraic union is a linear subspace of finite-dimensional R^H and hence closed, so it equals T_H(V). Choose a bounded linear right inverse into finitely many legal atoms. Approximating a feasible F in norm and repairing its finite trace with this right inverse gives legal exact-head approximants converging to F.

Therefore

    E_{infinity,H} increases to 1 if 1 belongs to V,
    E_{infinity,H} increases to infinity otherwise.

If 1 belongs to V, the upper bound is E_{infinity,H}<=1 and the lower bound is Q({1,...,H})->1. For the alternative see the residual certificate below.

Thus a bounded exact-head family with freely chosen cofinal periods is equivalent to 1 in V. At paper level this is RH-equivalent: Bagchi, arXiv:math/0607733, Remark 4 and final Remark 3, proves the reverse RH-to-squarefree-closure implication, while the discussion following Theorem 1 permits the comparable Q weights. The new Lean module uses only the existing forward RH consumer and does not newly formalize Bagchi's reverse implication. If 1 belongs to V, one can choose m_j sufficiently large for each H_j to obtain E_{m_j,H_j}<=1+epsilon_j. However squarefree closure does NOT automatically provide a bound along the prescribed maximal-head diagonal H_m=p_next-1. Passing from the two-index limit to that diagonal requires a quantitative approximation/repair estimate. Calling that specific diagonal bound equivalent to squarefree closure or RH would require an additional proof.

Any bounded subsequence on expanding heads already implies 1 in V by weak compactness and continuity of coordinate evaluation. Thus if 1 is not in V, the optimized energies along every expanding-head schedule tend to infinity, not merely become unbounded.

Uniform boundedness only guarantees weak convergence of an exact-head family to 1; it does not by itself guarantee that this particular family converges strongly. For an exact-head F with E=||F||^2, writing q=Q({n>H}) yields

    (sqrt(E-1+q)-sqrt(q))^2 <= ||F-1||^2
      <= (sqrt(E-1+q)+sqrt(q))^2.

Therefore along expanding heads E->1 is equivalent to strong convergence F->1. A uniform bound E<=C is sufficient for closure but is weaker than proving E->1 for that chosen family.

## 7. Exact residual obstruction

Let r=1-P_V1. For every legal exact-head F, orthogonality gives

    sum_{n>H} Q(n)F(n)r(n)=-sum_{n<=H}Q(n)r(n).

Writing A_H=sum_{n<=H}Q(n)r(n), R_H=sum_{n>H}Q(n)r(n)^2, Cauchy-Schwarz yields, when R_H>0,

    ||F||_Q^2 >= Q({1,...,H})+A_H^2/R_H.

If r is nonzero then A_H-><1,r>=||r||^2>0 and R_H->0, so this lower bound diverges. If R_H=0 and A_H is nonzero, no feasible exact-head F can exist. This is a rigorous obstruction conditional on a nonzero residual, not an unconditional proof of divergence for the optimized family.

## Conclusion

The divergent explicit seed leaves room for enormous finite-stage signed improvements. The reduced Schur complement identifies those improvements exactly and supports efficient computations and rational certificates. It does not settle whether the optimized maximal-head family is uniformly bounded. A finite-stage experiment cannot establish or refute that uniform statement. Existence of some uniformly bounded legal exact-head family (or the flexible two-index version) is exactly equivalent to squarefree closure, hence to RH using Bagchi's squarefree version. The converse for the chosen maximal-head diagonal is not established here.


## Best next analytic obligation

For the partition and notation in the reduced Schur formula, both

    a^T A a - b^T C^{-1}b >= 0,
    (beta + v^T C^{-1}b)^2 / (v^T C^{-1}v) >= 0

are nonnegative. Their sum is the exact optimum. A uniform bound must control that complete sum as the forced low coefficients and free dictionary both change. Dropping the negative cross correction, replacing it with absolute coefficient sums, or discarding the infinite tail loses the cancellation shown by the experiment.

The next rigorous route is to bound the two-index fixed-head repair problem quantitatively and choose a cofinal period schedule from that bound. For the prescribed maximal-head diagonal, one must additionally show that the available period is sufficiently large relative to the growing head. Neither positive definiteness of each finite Gram matrix nor monotonicity at a fixed head provides that missing estimate.

A second useful exact target is a cumulative balance between the energy saved by enlarging the divisor dictionary and the energy paid to extend the head. Both contributions must remain in the identity; there is no established stage-independent bound on their difference here.

## References and provenance

- Base repository memorandum: `CRTLegalApproximants20261028.md`, commit `5ecd057b363caa6866b9b53537efa538161c68b7`, for the explicit seed and divergence audit.
- NIST, [Trigamma function](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/trigamma.htm), for the positive series identity used in the periodic Gram formula. The finite regrouping and rational enclosures are derived above.
- Bhaskar Bagchi, [On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis](https://arxiv.org/html/math/0607733v1), Theorem 1, its comparable-weight discussion, Remark 4, and final Remark 3, for the paper-level squarefree RH equivalence. No new Lean verification of the reverse Bagchi implication is claimed.
