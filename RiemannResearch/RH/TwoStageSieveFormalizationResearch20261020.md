# Uniform two-stage prime-power obstruction: completed formalization

20 October 2026. Baseline main: `5c0f749a410837f1145efa4a93ec5f8f5c5b3924`.
This completes the infinite-limit tasks identified in
`TwoStageSieveObstructionResearch20261020.md`.

## 1. Principal result and exact scope

Let Q(n)=1/(Z n²), n≥1, with Z=ζ(2). Fix a prime p and 1/2<σ<1.
Use the actual vectors and slopes

    A_(p,H) = sieveVector (primorial H) p,
    a_(p,H) = sieveSlope (primorial H) p,
    F_p = qTarget p hp.one_lt.

Their physical target coordinates are F_p(n)=Nat.log p n. Define

    T_(p;H,K) = [a_(p,H) A_(p,K) - a_(p,K) A_(p,H)]
                / [a_(p,H)-a_(p,K)].

The new `sieveTwoStageVector` is an actual complete-Q Hilbert vector and is
in the finite squarefree legal span. For H≥p, K≥H and unequal slopes,
it agrees exactly with F_p at every n≤H. At p=2 it equals the existing
`twoStageVector`, by `sieveTwoStageVector_two`.

The final theorem is

    ∃ N≥p, ∀ H≥N, ∀ K≥H with a_(p,H)≠a_(p,K),
      ||T_(p;H,K)-F_p||_Q² ≥ c_(σ,p) H^(2σ-1),

    c_(σ,p) = (2σ-1) / [4 Z σ² (p^σ-1)²] > 0.

Its declaration is
`QPrimePowerSieve.sieveTwoStageVector_quantitative_lower` in
`RH/QPrimePowerTwoStageObstruction.lean`.
There is no slope-gap lower bound, coefficient-variation hypothesis,
Mellin-decay assumption, closure assumption, or RH assumption in its type.
The cutoff N is existential; this work does not compute a numerical N.

The same module proves
`sieveTwoStageVector_norm_tendsto_atTop`: if H_j→∞ and eventually
H_j≤K_j with unequal slopes, then ||T_(p;H_j,K_j)||_Q→∞.
In particular, the formerly unresolved near-equal-slope regime is excluded.
For σ=3/4 the squared-error bound is

    ||T-F_p||_Q² ≥ [2 / (9 Z (p^(3/4)-1)²)] sqrt(H).

## 2. Elementary Euler decay: a shorter proof

Write P_σ(H)=∏_(q≤H, q prime)(1-q^(-σ)). All factors are positive for σ>0.
The proof uses Mathlib's absolutely convergent geometric-series expansion
over integers supported on a fixed finite prime set. It never exchanges an
infinite prime product with a limit.

Every integer 1≤n≤H is supported on the primes at most H, so

    P_τ(H)^(-1) ≥ Σ_(1≤n≤H) n^(-τ) ≥ H^(1-τ),
    P_τ(H) ≤ H^(τ-1).

For τ>σ and a fixed natural number m, eventually q^(τ-σ)≥m. Bernoulli's
inequality gives

    1-q^(-σ) ≤ 1-m q^(-τ) ≤ (1-q^(-τ))^m.

The finitely many earlier positive factors cost only a constant C>0:

    P_σ(H) ≤ C P_τ(H)^m.

Taking τ=(1+σ)/2 and m=3 proves

    0 ≤ H^(1-σ) P_σ(H) ≤ C H^(-(1-σ)/2) → 0,

for 0<σ<1. Removing the fixed prime p multiplies this by the fixed factor
p^(-σ)/(1-p^(-σ)). These are kernel-checked declarations in
`Analysis/PrimePowerEulerDecay.lean`, particularly
`primePowerEulerProduct_scaled_tendsto_zero` and
`primePowerEulerProduct_erase_scaled_tendsto_zero`.

This replaces the memorandum's prime-reciprocal and reduced-residue proof.
Neither prime-reciprocal divergence, PNT, nor Bertrand's postulate is needed
in the final analytic argument.

## 3. The requested fixed-modulus limit, proved separately

For every fixed positive integer L, including nonsquarefree L,
`Analysis/ReducedResiduePowerSum.lean` proves

    N^(σ-1) Σ_(1≤n≤N, gcd(n,L)=1) n^(-σ)
      → (φ(L)/L)/(1-σ),              0<σ<1.

The principal declaration is
`ReducedResiduePowerSum.reduced_residue_power_sum_tendsto`.
An integral squeeze first proves the normalized ordinary power-sum limit.
Exact finite Möbius inversion then gives

    Σ_(1≤n≤N, gcd(n,L)=1) n^(-σ)
      = Σ_(d|L) μ(d) d^(-σ) Σ_(1≤k≤floor(N/d)) k^(-σ).

The limit floor(N/d)/N→1/d and
Σ_(d|L) μ(d)/d=φ(L)/L finish the proof.
Only a finite divisor sum is passed through the limit. No uniformity in
a moving modulus L=L(N) is asserted or needed.

## 4. Actual arithmetic Mellin identities and all-second-cutoff uniformity

Let Φ_σ(f)=σ M_σ(f), using the existing continuous physical Mellin functional.
The new finite identity is proved for the actual sieve synthesis, rather than
assumed as an arithmetic provider:

    Φ_σ(A_(p,H)) = ζ(σ)[t_(p,H)(σ)-a_(p,H)],
    t_(p,H)(σ)=p^(-σ)∏_(q≤H,q≠p)(1-q^(-σ)).

`RH/QPrimePowerSieveMellin.lean` establishes this first for every squarefree
period and divisor p. `RH/QPrimePowerSievePrimeStep.lean` specializes to
primorials, proves positive slopes and the prime/nonprime successor rules.

For q=H+1 prime and H≥p,

    a_(p,H+1)=a_(p,H)(1-1/q),
    t_(p,H+1)=t_(p,H)(1-q^(-σ)),
    I(a_H,a_(H+1);t_H,t_(H+1))=t_H(1-q^(1-σ)).

For q not prime both stages are unchanged. The existing secant algebra is
extended in `RH/PrimeSieveSecantLimits.lean` to nonincreasing positive slopes
with constant probes on repeated stages. Adjacent decay implies an epsilon
bound simultaneously for every later second endpoint.

Since H+1≤2H for H≥1, the adjacent bound is

    |I_(H,H+1)| ≤ 2^(1-σ) H^(1-σ)t_H → 0.

No compression to prime cutoffs and no prime-gap theorem is required.
The identity for the actual complex Mellin transform is

    Φ_σ(T_(p;H,K))=ζ(σ) I(a_H,a_K;t_H,t_K).

Consequently `sieveTwoStageVector_mellin_uniform` proves

    ∀ε>0, ∃N≥p, ∀H≥N, ∀K≥H, ||Φ_σ(T_(p;H,K))||<ε.

The uniform theorem even includes degenerate pairs, whose inverse-zero
definition is the zero vector. Exact head matching and the energy lower
bound explicitly require nondegeneracy.

## 5. Complete-Q tail estimate and constant audit

The existing continuous kernel integral gives a direct proof, avoiding any
new exchange of a discrete infinite sum. If f(n)=0 for n≤H, H≥1, then

    ||M_s(f)||² ≤ [Z ||f||_Q² - metricCorrection(f)]
                  H^(1-2 Re(s))/(2 Re(s)-1).

Here the bracket is exactly ||toPareto(f)||² and the metric correction is
nonnegative. Dropping it and multiplying by σ² gives

    ||Φ_σ(f)||² ≤ ||f||_Q² [Z σ²/(2σ-1)] H^(1-2σ).

These statements are in `RH/ParetoMellinTail.lean` and
`RH/QMellinTail.lean`. The exact target formula gives

    ||Φ_σ(F_p)|| = C_p = 1/(p^σ-1)>0.

Apply the tail estimate to f=T-F_p. Uniformity eventually gives
||Φ_σ(T)||≤C_p/2, so ||Φ_σ(T-F_p)||≥C_p/2. Inverting the tail bound produces
the displayed c_(σ,p), with no omitted factor of σ or Z. The actual target
norm is finite by the pre-existing target construction. The triangle
inequality then gives the moving norm-divergence theorem.

## 6. What is excluded, and what remains open

Kernel-checked exclusion: every exact two-stage correction in this actual
raw prime-power sieve family, with the first cutoff tending to infinity
and unequal slopes. It cannot supply a uniformly complete-Q bounded seed,
even though every prescribed finite head is matched exactly.

The following broader signed-row analysis is an ordinary mathematical
deduction; its general finite-row representation is not a new Lean theorem
in this change. For strictly decreasing positive slopes a_0,...,a_m, let

    B=Σ_i c_i A_i,     Σ_i c_i=1,     Σ_i c_i a_i=0,
    S_k=Σ_(i≤k)c_i a_i,
    λ_k=-S_k(1/a_(k+1)-1/a_k).

Finite summation by parts gives exactly

    B=Σ_(k<m) λ_k T_(k,k+1),     Σ_(k<m)λ_k=1.

Thus any number of cutoffs with S_k≤0 is still a convex mixture of adjacent
corrections and inherits the same Mellin obstruction. More generally,
for rows whose least cutoff tends to infinity, bounded Σ|λ_k| forces the
Mellin transform to zero. Complete-Q boundedness with the exact growing
head would instead force it to C_p. Such a bounded family therefore needs
unbounded total variation in these adjacent coefficients. This is stronger
than a restriction on total variation of the original raw weights.

With three raw cutoffs one has B=λ T_01+(1-λ)T_12, with λ allowed to be any
real number. If the two adjacent real Mellin values m_0,m_1 differ, then
λ=(C_p-m_1)/(m_0-m_1) matches that single Mellin value exactly. This describes
an algebraic escape using large signed adjacent weights; it supplies no
complete-Q energy estimate, simultaneous control of other Mellin values,
or target closure result.

Independent coefficients on the full squarefree-divisor dictionary are
not restricted to these raw-sieve mixtures. Their constrained optimizers
and signed complete-energy estimates remain possible research directions.

Open, unchanged: qOne in the squarefree closed span; membership of F_2 and
F_3 in the relevant squarefree closure (with constants for the existing
two-target consumer); the actual cofinal signed-energy budget; and RH.
The new theorem excludes a proposed approximation mechanism. It neither
proves nor disproves these closure statements or RH.

## 7. Verification ledger

Successful server checks, all `verified=true`, exit 0:

- `job_TrD0QDF-i5xVDIWfRX2u2b-EqZE41ioX`: actual finite Mellin/Euler formulas.
- `job_LFn0DtGP83uQYa6RavhSfvwVO31j1M8U`: elementary Euler decay, prime-step
  arithmetic, repeated-stage secant limits, and complete-Q tail bounds.
- `job_AT4WCM6ngz2E2xkYSfckrqyqY99U6Tl9`: full fixed-modulus residue limit.
- `job_eb22Pr4Z79Pg7fTordbEZ57W55fhi86Z`: coherent actual uniform-Mellin and
  quantitative complete-Q theorem, including the explicit target constant.
- `job_ZOLUmEXlAHl8lGBPzHvxi5M9SBkbiqcY`: staged application-module imports,
  fixed-modulus module, and the actual moving norm-divergence corollary.

Final staged import/axiom audit `job_3vRdgkwYETp-cBXwh7lK3XpJAWryflzA`
succeeded with verified=true and exit 0. All six inspected principal
results depend only on propext, Classical.choice, and Quot.sound.
The final publication checkpoint is separately reported with its commit. Snippet success alone is not the
publication gate. New modules contain no sorry, admit, unsafe declaration,
or project-local axiom. General signed-row conclusions in Section 6 are
explicitly distinguished from the checked two-stage declarations.
