# Prime-power counting targets, radical jump geometry, and a divergent sieve family

Working research note, 20 October 2026. Sections 1–7 contain ordinary mathematical arguments. Section 8 records the narrower scope of the accompanying Lean development and its verification status. No RH proof is claimed.

## 1. Concrete nonperiodic elements of the radical-jump space

Let Q(n)=1/(ζ(2)n²), n≥1, and let H be the closed real span of g_d(n)=(n mod d)/d over squarefree d>1. Let K consist of Q-Hilbert vectors whose backward jumps at n,m≥2 agree whenever n and m have the same squarefree-divisor events (equivalently, the same radical).

For a prime p define

F_p(n)=#{j≥1:p^j≤n}=floor(log(n)/log(p)), n≥1, and F_p(0)=0.

Its backward jump is 1 at the positive powers of p and 0 elsewhere. For n≥2 that event depends only on rad(n), so F_p∈K. Its complete Q norm is finite. Partition into intervals p^j≤n<p^(j+1), on which F_p=j, and use Σ_{n≥m}n^(-2)≤2/m for m≥2. Then

||F_p||_Q² ≤ (2/ζ(2))Σ_{j≥1}j²p^(-j)
             = 2p(p+1)/(ζ(2)(p−1)³).

Likewise the capped functions min(F_p,J) satisfy the quantitative complete-Q bound

||F_p−min(F_p,J)||_Q² ≤ [2p(p+1)/(ζ(2)(p−1)³)]p^(-J).

The capped functions are ambient approximants; their jumps are not radical-invariant once the cap cuts off higher powers. They are not legal approximants.

## 2. Why adding constants does not freely solve closure

Use the normalized Mellin functional

Φ_s(f)=s∫_1^∞f(floor x)x^(-s−1)dx
      =Σ_{n≥1}f(n)[n^(-s)−(n+1)^(-s)], Re(s)>1/2.

The existing Pareto-to-Q comparison and Mellin Cauchy theorem give

|Φ_s(f)|² ≤ |s|²ζ(2)||f||_Q²/(2Re(s)−1).

The exact values are

Φ_s(1)=1,
Φ_s(g_d)=ζ(s)(d^(-1)−d^(-s)),
Φ_s(F_p)=Σ_{j≥1}p^(-js)=1/(p^s−1).

For F_p the calculation is absolutely justified already for Re(s)>0 by its logarithmic growth and the geometric series.

If ζ(s)=0 and Re(s)>1/2, Φ_s vanishes on H. Therefore F_p∈H would contradict its nonzero displayed transform and would imply RH through the usual zero-free-half-plane criterion.

For the larger space closure(H+R1), the imaginary part of Φ_s vanishes: it vanishes on every legal atom and on every real constant. Consequently membership of F_p forces 1/(p^s−1) to be real, hence p^s to be real. If both F_2 and F_3 belonged to closure(H+R1), then 2^s and 3^s would be real. Conjugating and using injectivity of the pair of complex powers at 2 and 3 gives s=conj(s), so s is real. The zeta function has no real zero in Re(s)>1/2. Thus the two memberships imply RH.

In particular, closure(H+R1)=K would imply RH, because both F_2,F_3 lie in K. It cannot be treated as a free structural density theorem. This argument does not establish a converse characterization of K.

Existing Lean ingredients located:

- RH/ParetoMellinFunctional.lean: paretoMellinContinuous, paretoMellin_norm_sq_le, paretoMellin_one.
- RH/ZetaTwoParetoTransfer.lean: toParetoCLM, toPareto_norm_sq_le, toPareto_qOne, toPareto_qResidue.
- RH/ArithmeticConductorCommonZeros.lean: two_three_cpow_neg_injective.
- Mathlib Complex.cpow_conj; an existing private helper appears in RH/SmallDualCriticalZeros.lean, lines 77–85.

## 3. An explicit pointwise legal sieve approximation

For squarefree L divisible by p, set

c_{p,L}(d)=1_{p|d}μ(d/p), d|L,
a_{p,L}=Σ_{d|L}c_{p,L}(d)/d
         =(1/p)∏_{q|L,q≠p}(1−1/q)
         =[∏_{q|L}(1−1/q)]/(p−1),
A_{p,L}(n)=−Σ_{d|L}c_{p,L}(d)g_d(n).

Finite divisor incidence and integration give the exact identity

A_{p,L}(n)=#{1≤m≤n:gcd(m,L)=p}−a_{p,L}n.

All nonzero terms have squarefree conductors d>1, so these are actual legal functions. For L_x=∏_{q≤x}q and each fixed n, the count eventually equals F_p(n). The scalar a_{p,L_x} tends to zero by Euler's divergence of prime reciprocals. Hence A_{p,L_x}(n)→F_p(n) pointwise.

## 4. The same family diverges in complete Q norm

This is an unconditional obstruction, not an RH-dependent conclusion.

First proof: fix a real σ∈(1/2,1). The exact Mellin transform is

Φ_σ(A_{p,L_x})=ζ(σ)[p^(−σ)∏_{q≤x,q≠p}(1−q^(−σ))−a_{p,L_x}].

Both finite products tend to zero. For the first, Σ_q q^(−σ) diverges because q^(−σ)≥q^(−1). Thus Φ_σ(A_{p,L_x})→0, whereas Φ_σ(F_p)=1/(p^σ−1)>0. A norm-bounded subsequence in a Hilbert space has a weakly convergent subsequence; continuity of coordinate evaluations and the known pointwise limit force that weak limit to be F_p. Continuity of Φ_σ contradicts the two transform limits. Therefore no norm-bounded subsequence exists, which is equivalent to ||A_{p,L_x}||_Q→∞.

Second proof: exact initial-segment energy. For every integer n≤x, all its prime divisors belong to L_x, so

A_{p,L_x}(n)=F_p(n)−a_{p,L_x}n.

For H=floor x, the elementary inequality (u−v)²≥u²/2−v² gives

||A_{p,L_x}||_Q²
 ≥ a_{p,L_x}²H/(2ζ(2))−||F_p||_Q².

Mertens' classical product theorem would immediately give divergence at least of order x/(log x)². But even that theorem is unnecessary: an elementary finite-product lower bound below yields a weaker sufficient power rate.

## 5. Elementary lower bound using reduced residues modulo six

All primes at least five are congruent to 1 or 5 modulo six. Put

b_k=(6k/(6k+1))((6k+4)/(6k+5)), k≥1.

Wolfram checked the exact rational identity

b_k³−(k−1)/k
 = [125+2575k+19440k²+63396k³+87696k⁴+42768k⁵]
   /[k(1+6k)³(5+6k)³] ≥0.

Therefore, for integer K≥1,

∏_{k=1}^K b_k ≥(60/77)K^(−1/3).

If 6K+5≥x, multiplying the factors at 2,3,5 and adding all composite candidate factors only decreases a product whose factors lie in (0,1), giving

∏_{q≤x}(1−1/q) ≥ (4/15)∏_{k=1}^K b_k
                      ≥ (16/77)K^(−1/3).

Choose K=ceil(x/6), so K≤x for x≥2. Consequently

a_{p,L_x}² x ≥ [16/(77(p−1))]² x^(1/3).

Combined with the exact initial-segment energy bound (taking integer x) this proves

||A_{p,L_x}||_Q²
 ≥ [128/(5929ζ(2)(p−1)²)]x^(1/3)
   −2p(p+1)/(ζ(2)(p−1)³).

This is deliberately coarse but unconditional and sufficient to rule out boundedness.

A subsequent declaration search located the already established project module `Analysis/FinitePrimeProductBounds.lean`, from the first-coordinate continuation of 19 September 2026. It already proves prime-product decay, the concrete finite bound

(4/15)³ ≤ [∏_{q≤H}(1−1/q)]³(2H+1),

and divergence of H[∏_{q≤H}(1−1/q)]². The new application therefore reuses that module; the independently drafted mod-six module will not be published as duplicate infrastructure. `RH/PrimeSievePointEnergy.lean` already applies these estimates to a different first-coordinate sieve. The present arithmetic provider selects gcd class two and the prime-power-counting target.

The modules `RH/QPrimePowerSieve.lean` and `RH/QPrimePowerPrimorial.lean` define the actual synthesis, prove the exact count-minus-slope identity and slope Euler product, and bound its complete Q norm by a finite head. Their exact verification scope is recorded in Section 8.

## 5a. Regular positive averaging cannot repair this family

Let B_j=Σ_x w_{j,x}A_{p,L_x} be finite convex combinations, with w_{j,x}≥0, Σ_xw_{j,x}=1, and Σ_{x≤M}w_{j,x}→0 for each fixed M. Such an averaging scheme preserves every scalar limit. In particular, B_j(n)→F_p(n) for each n, while Φ_σ(B_j)→0. The same weak-subsequence argument proves ||B_j||_Q→∞. Thus ordinary Cesàro averages and any other regular finite positive averages of these raw sieve vectors cannot supply a norm-bounded replacement. This does not address modified coefficients or different legal approximants.

## 6. Wolfram verification ledger

At p=2 and L=2,6,30,210,2310, the exact rational whole-period sieve identity passed. The complete-Q norm was evaluated using all infinite residue tails w_L(n)=PolyGamma(1,n/L)/(ζ(2)L²), with 60-digit arithmetic. No interval certificate is asserted.

|L|a exact|nonzero coefficients|complete Q norm squared|max period absolute value|
|---:|---:|---:|---:|---:|
|2|1/2|1|0.1875|1/2|
|6|1/3|2|0.1160118478214808444194|2/3|
|30|4/15|4|0.1451051544658737203319|14/15|
|210|8/35|8|0.1884678569568722997355|53/35|
|2310|16/77|16|0.2338227324487018642301|194/77|

The small finite values do not support a uniform bound: the proof above shows eventual divergence.

## 7. Literature scope

Luis Báez-Duarte, Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis, arXiv:math/0011254, studies several natural pointwise approximants that diverge in L². Its introduction and Section 4 establish this warning for its specified sequences. It is background, not a cited theorem directly identifying the present prime-power/primorial family.

https://arxiv.org/pdf/math/0011254

The elementary proof in Section 5 does not need Mertens' theorem or any deep zero-free estimate. For the sharper optional asymptotic, the classical Mertens product formula is stated in Ross Pinsky, Probabilistic Proofs of Some Generalized Mertens' Formulas Via Generalized Dickman Distributions, arXiv:1809.04888, and in Youness Lamzouri, A bias in Mertens' product formula, arXiv:1410.3777.

https://arxiv.org/abs/1809.04888
https://arxiv.org/abs/1410.3777

No novelty claim is made. The useful research conclusion is that finite inversion and pointwise convergence need a norm-controlled replacement of this sieve family; its unsmoothed coefficients cannot deliver that control.

## 8. Lean scope and verification

The accompanying development supplies the actual gcd-two primorial vector, rather than a theorem whose hypotheses assume its coefficient identity or norm estimate:

- `RH/QPrimePowerSieve.lean`: the divisor-inversion synthesis, coefficient formula, legality, exact count-minus-slope sequence, slope as φ(L/p)/L, exact logarithmic head under concrete prime coverage, and the complete-Q finite-head lower bound.
- `Analysis/PrimeProductDyadicGrowth.lean`: a quantitative rate derived from the existing finite Euler-product lower bound, sufficient to absorb a quadratic floor-log error along 64^m.
- `Analysis/PrimeProductHeadGrowth.lean`: monotonicity extends that quantitative rate to every cutoff, retaining the squared floor-log error.
- `RH/QPrimePowerPrimorial.lean`: the actual primorial supplies squarefreeness and prime coverage; the gcd-two slope is exactly the existing finite prime product. `primePowerTwoVector_pointwise` gives coordinatewise convergence to `Nat.log 2 n`. `primePowerTwoVector_norm_tendsto_atTop` asserts divergence of the complete Q norm at every cutoff.

The coordinator's coherent combined Lean check succeeded: job `job_7_5OzFtPU28n2psmZJTofM8AE2_VyPz6`, verified true, exit code 0, code SHA-256 `2e035444b75578d9d717a4565db6a493c3665af026ac1b910fb293878acb259a`. The exact pointwise-convergence and full-norm-divergence declarations were checked with only standard Lean/Mathlib axioms. This is a successful combined source check; the final separately staged project modules still require the publication checkpoint, whose job and commit are reported separately.

The global floor-log Q vector, its membership in K, the Mellin/two-target RH implication, the all-prime-p generalization, and the regular-convex-averaging obstruction remain ordinary arguments in this note. They are not claims certified by these four Lean modules.

## Final development verification

Standalone-import job `job_04vz-YUURs6_1xaxISqRinrrHIJYGNqd` succeeded
with `verified=true` and exit code 0. It built the staged prime-power sieve,
full-cutoff head-growth, and primorial assembly modules independently, and
imported the staged signed-tail and quantitative parity modules. The inspected
pointwise, full-norm-divergence, parity-bound, and signed-tail-ratio declarations
depended only on `propext`, `Classical.choice`, and `Quot.sound`.
Publication is gated separately by the server source audit and incremental
aggregate/changed-module checkpoint; its terminal job and exact commit are
reported with the published result.
