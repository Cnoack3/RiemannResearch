# Moving two-stage prime-power sieves: a uniform obstruction

**Completion:** `TwoStageSieveFormalizationResearch20261020.md` records the
kernel-checked infinite limits, explicit lower bound, and moving norm divergence.
The proof uses integer cutoff steps and a simpler elementary Euler comparison.
Original status statements later in this note are historical and superseded.

20 October 2026. Baseline: main `497c83d7c88a323b617ebccc6b7394fe2077b39e`.
This continues Section 4 of `TwoPrimeMellinCriterionResearch20261020.md`.
There is no earlier weekly report in this conversation to compare; current
repository results, including the older secant method, were checked instead.

## Outcome and exact status

The near-equal-slope two-stage repair can also be ruled out by the ordinary
argument below. The new Lean results certify the finite secant identities,
the uniform finite adjacent-intercept bound, the exact Euler step, and the
specialization to real linear probes of the actual gcd-two sieve vectors.
The infinite Euler-product decay, Mellin-tail estimate, and full moving-cutoff
norm-divergence theorem are now formalized in the linked completion.

This extends the earlier bounded-total-variation obstruction for these
prime-power targets. It adapts, rather than claims novelty for, the reciprocal
secant strategy already discussed for a different constant-target sieve in
`IndependentPrimeResearchContinuation20261007.md`, equations (10)--(15).
No constant-target closure, prime-power target membership, or RH is proved.

## 1. Actual family, target, and remaining RH consumer

Q(n)=1/(Z n^2), n>=1, Z=zeta(2). Fix a prime p. Write

    F_p(n)=floor(log_p n),
    a_H=(1/p) product_(q<=H, q prime, q!=p) (1-1/q),
    t_H(sigma)=p^(-sigma) product_(q<=H, q prime, q!=p) (1-q^(-sigma)),
    A_H=-sum_(d|primorial H, p|d) mu(d/p) g_d.

For H>=p, these are actual squarefree legal vectors and

    A_H(n)=F_p(n)-a_H n,   n<=H.

For prime cutoffs H<K with p<=H, a_H>a_K>0. Define

    T_(H,K)=(a_H A_K-a_K A_H)/(a_H-a_K).

Then T_(H,K)(n)=F_p(n) for n<=H. Repeated primorial stages add no new
vectors and can be compressed to prime cutoffs.

The existing exact RH consumer is

    PrimePowerTarget.riemannHypothesis_of_two_targets_mem_closureWithConstants

in `RH/PrimePowerTwoTargetCriterion.lean`: membership of both actual
F_2 and F_3 in closure(H_sq^Q + R*1) implies literal Mathlib RH.
Both memberships remain Open. The present work tests one proposed provider,
rather than assuming that provider or re-proving the conditional consumer.

## 2. Exact positive secant subdivision

For scalars define I(a,b;x,y)=(a y-b x)/(a-b).
If a>b>c>0, then, exactly,

    I(a,c;x,z) = alpha I(a,b;x,y) + beta I(b,c;y,z),
    alpha=c(a-b)/[b(a-c)],  beta=a(b-c)/[b(a-c)],
    alpha>0, beta>0, alpha+beta=1.

Iterating over the distinct prime stages indexed i,...,j yields

    T_(i,j)=sum_(k=i)^(j-1) lambda_k T_(k,k+1),
    lambda_k=[a_i a_j/(a_i-a_j)] (1/a_(k+1)-1/a_k)>0,
    sum lambda_k=1.

This is a vector identity: write X_k=A_k/a_k and telescope X_j-X_i.
It also holds after applying any real linear functional.
Large signed coefficients in the original pair therefore do not avoid
convexity in the adjacent-correction coordinates.

The Lean theorem `intercept_abs_le_of_adjacent` certifies the finite
consequence: a common bound |I_(k,k+1)|<=e on an interval implies
|I_(i,j)|<=e. Its hypotheses are only positive strictly decreasing slopes
and the stated finite adjacent bounds; no asymptotic or RH assumption is hidden.

## 3. Exact Mellin formula and prime step

Fix 1/2<sigma<1, and put alpha=1-sigma>0. The normalized real Mellin
functional is

    Phi_sigma(f)=sum_(n>=1) f(n)[n^(-sigma)-(n+1)^(-sigma)].

It is continuous on complete Q space. The actual target and raw sieve obey

    Phi_sigma(F_p)=C_p=1/(p^sigma-1)>0,
    Phi_sigma(A_H)=zeta(sigma)[t_H(sigma)-a_H].

These formulas use finite synthesis and the existing atom Mellin identity.
For q the next prime after H, q!=p,

    a_q=a_H(1-1/q),   t_q=t_H(1-q^(-sigma)),
    T_(H,q)=q A_q-(q-1)A_H,
    Phi_sigma(T_(H,q))
      =zeta(sigma)t_H(1-q^(1-sigma)).                 (1)

All signed terms are retained. The Lean lemma `intercept_euler_step`
checks the corresponding exact rational algebra, with the Euler factor
q^(-sigma) represented by an arbitrary scalar r. It does not assert the
asymptotic decay used next.

## 4. Elementary Euler-product decay; no Mertens asymptotic needed

For 0<sigma<1 let

    E(H)=product_(q<=H, q prime) (1-q^(-sigma))^(-1).

Claim:

    E(H)/H^(1-sigma) -> infinity,
    equivalently H^(1-sigma) t_H(sigma) -> 0.         (2)

Here p is fixed and H>=p, so t_H differs from 1/E(H) by the fixed
positive factor p^(-sigma)/(1-p^(-sigma)).

Proof. Fix a finite prime cutoff Y and L_Y=primorial Y. The finite Euler
product has its absolutely convergent positive geometric-series expansion.
Every n<=H coprime to L_Y has only prime factors in (Y,H]. Therefore

    E(H)>=E(Y) sum_(n<=H, gcd(n,L_Y)=1) n^(-sigma).

For this fixed L_Y, counting its finitely many reduced residue classes
and comparing power sums with integrals gives

    H^(sigma-1) sum_(n<=H, gcd(n,L_Y)=1) n^(-sigma)
      -> [phi(L_Y)/L_Y]/(1-sigma).

Moreover

    E(Y) phi(L_Y)/L_Y
      =product_(q<=Y) (1-1/q)/(1-q^(-sigma)) -> infinity.

Indeed for all sufficiently large q, q^(1-sigma)>=2 and each ratio is
at least 1+1/q. Divergence of the prime reciprocal series and
log(1+1/q)>=1/(2q) imply divergence of this positive product.
Given any proposed lower bound, first choose a fixed Y, then let H grow.
No simultaneous-limit interchange, PNT, RH, or zero-free estimate is used.

Bertrand's postulate gives q<=2H for the next prime. Applying (2) to (1)
shows that the adjacent Mellin values tend to zero.
The positive subdivision in Section 2 now gives

    sup_(K>H, distinct prime stages) |Phi_sigma(T_(H,K))| -> 0.       (3)

The supremum is over a tail of convex averages of a convergent scalar
sequence, hence is finite and tends to zero. This is uniform in K,
regardless of a_K/a_H or the signed coefficient total variation.

Background formalized elementary inputs available in Mathlib:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html
  (`Nat.exists_prime_lt_and_le_two_mul`).
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumPrimeReciprocals.html
  (`Nat.Primes.not_summable_one_div`).

The weighted reduced-residue power-sum asymptotic and the assembly above
still need a Lean formalization; availability of the background inputs
does not certify this assembly.

## 5. Quantitative complete-Q tail obstruction

This avoids a weak-compactness argument. If f(n)=0 for n<=H, H>=1,
weighted Cauchy--Schwarz gives

    |Phi_sigma(f)|^2
      <= ||f||_Q^2 Z sum_(n>H) n^2
           [n^(-sigma)-(n+1)^(-sigma)]^2
      <= ||f||_Q^2 [Z sigma^2/(2sigma-1)] H^(1-2sigma).            (4)

The first estimate is justified by absolute convergence via
Cauchy--Schwarz, since sigma>1/2. The second uses the mean-value bound
0<n^(-sigma)-(n+1)^(-sigma)<=sigma n^(-sigma-1), followed by the
decreasing-integrand bound sum_(n>H)n^(-2sigma)<=H^(1-2sigma)/(2sigma-1).

Apply (4) to f=T_(H,K)-F_p, which has an exactly zero head. With
eta_H=sup_(K>H)|Phi_sigma(T_(H,K))| from (3), we obtain

    ||T_(H,K)-F_p||_Q^2
      >= [(2sigma-1)/(Z sigma^2)] H^(2sigma-1) (C_p-eta_H)_+^2.  (5)

Thus, uniformly over the second cutoff, eventually

    ||T_(H,K)-F_p||_Q^2
      >= [(2sigma-1) C_p^2/(4Z sigma^2)] H^(2sigma-1).

In particular every moving nondegenerate pair H_j<K_j, H_j->infinity,
has ||T_(H_j,K_j)||_Q->infinity, by the reverse triangle inequality
and the already finite complete-Q norm of F_p.
The case sigma=3/4 gives a square-root lower rate for squared error.
General nonprime cutoffs compress to their last prime; Bertrand compares
that prime with the original cutoff if a rate in the original cutoff is desired.

This rules out the near-equal-slope regime left open in the previous note.
It does not rule out general signed mixtures or a redesigned full divisor
coefficient vector. An upper bound for those richer families is still Open.

## 6. Circularity audit and best next step

The finite identities, positive Euler expansions, fixed-modulus residue
counts, prime reciprocal divergence, Bertrand's postulate, and Mellin
continuity are unconditional. No Q_N->1, RH, target closure, coefficient
limit -mu(d), or desired complete-energy upper bound is assumed.
Every finite probe retains its arithmetic drift before the exact cancellation.

Best next step: stop pursuing two raw sieve cutoffs as bounded seeds.
Use the actual full-divisor rational minimizer and seek the signed provider

    S_(L_j) >= -theta E_(L_j)-epsilon_j,
    theta<1 fixed, epsilon_j->0, stages cofinal,

for the existing `closure_of_cofinal_signed_budget` consumer in
`RH/QRationalSignedTailClosure.lean`.
That estimate remains an RH-facing arithmetic obligation; its existing
equivalence to closure is not evidence that it is proved.
The exact within-class tail differences in
`QRationalTailDirichlet.lean` are a concrete place to look for new input.

## 7. Lean verification scope

Coherent server snippet `job_plyXN2GIWDtP2oM300djFafThEoz1jwr` succeeded:
verified=true, exit_code=0, code SHA-256
`dee28db58d65c1eba67db0c95dfb7b473fa1cff638bc2b1a8f9f213d2114eda1`.
The inspected principal declarations used only propext, Classical.choice,
Quot.sound. This checked the finite scalar lemmas together with the actual
Q-vector linear-probe specialization before staging.

Project changes extend the existing owning modules:
- `RH/PrimeSieveSecantAlgebra.lean`: intercept_split, split_weights_sum,
  intercept_abs_le_split, intercept_abs_le_of_adjacent, intercept_euler_step.
- `RH/QPrimePowerTwoStage.lean`: linear_twoStage_intercept,
  linear_twoStage_split.

The final server checkpoint separately determines staged/integrated validation
and publication; report its terminal receipt and commit with the result.
Sections 4--5 and their infinite-limit conclusion remain ordinary mathematics,
not certified by these finite Lean lemmas.
