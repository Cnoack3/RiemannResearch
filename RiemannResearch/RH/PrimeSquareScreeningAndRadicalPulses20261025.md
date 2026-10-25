# Prime-square screening with effective truncation

25 October 2026. Continuation of the arithmetic-kernel screening handoff at
commit 9dc1bd75aa9a7b2dd74819811a1ab2b8256bc859.

**Status: RH is not proved.** The actual uniform signed-response bound and
uniform error-weighted surviving-energy bound remain **Open**. This
continuation proves complete prime-square screening and an effective
finite-truncation estimate. It also records an ordinary obstruction to
replacing the actual coupled problem by a generic evaluation bound on the
locally radical-compatible space.

## Actual objects

Use Q(n)=1/(zeta(2)n^2), n>=1; Bf(n)=f(n)/(n+1). V_N is the actual masked
squarefree stage with conductors 2<=d<=N+1. Write

    r_N=1-P_N1, epsilon_N=||r_N||_Q^2,
    k_N,n=P_N e_n, u_N,n=(I-P_N) B k_N,n,
    b_N=P_N B r_N, Lambda_N,n=||u_N,n||_Q^2.

All norms and sums below include the complete infinite physical tail.
The new module uses physical n directly, except kernel tail and cutoff
bounds are stated at physical n+1 to avoid a redundant positivity premise.
The cutoff P is a prime cutoff, not a conductor cutoff.

## Verified arithmetic family

For every odd prime p set

    z_p=e_(p^2)-e_(p^2-1)-e_p+e_(p-1).

The squarefree divisor identity d|p^2 iff d|p proves that z_p annihilates
every legal atom. It also annihilates the constant target. Thus it
annihilates both V_N and r_N at every actual stage. The construction does
not assume squarefree target membership.

Distinct odd-prime rows have disjoint supports. Their B-images also have
disjoint supports. The exact norms and quantitative estimates are

    ||z_p||^2=zeta(2)(2p^4-2p+2) >= zeta(2)p^4,
    ||Bz_p||^2 <= 4zeta(2).

The full Gram matrix is diagonal for this particular family. No
independence claim is made for arbitrary omitted-coordinate families.

## Exact finite and complete screening

Define

    G(k,p)=|<Bk,z_p>|^2/||z_p||^2,
    Lambda_infinity(N,n)=Lambda_N,n - sum_(p odd prime) G(k_N,n,p).

For each finite distinct prime family, the normal coefficients are
<z_p,Bk>/||z_p||^2. The finite theorem gives the exact norm of the screened
kernel and the coupled Cauchy--Schwarz estimate. It retains the signed
residual pairing through <r_N,z_p>=0.

The complete sum is summable, the complete energy is nonnegative, and

    |b_N(n)|^2 <= epsilon_N Lambda_infinity(N,n).

The complete energy has the exact expression

    ||Bk_N,n||^2 - ||P_N Bk_N,n||^2
      - sum_(p odd prime) |<Bk_N,n,z_p>|^2/||z_p||^2.

Both the original full Schur subtraction and all arithmetic screening
squares are retained. The infinite coupled inequality is obtained by
passing the actual finite inequalities through the convergent sum.
The module does not identify the closed prime-square span with the full
annihilator or with all omitted-coordinate constraints.

## Effective truncation: the substantive quantitative advance

For every QHilbert vector k and every integer P>=1,

    sum_(p odd prime, p>P) G(k,p) <= 4||k||^2/P^4.

The proof applies weighted Bessel to the orthogonal vectors Bz_p. It
uses ||Bz_p||^2/||z_p||^2 <= 4/P^4 before summing, so there is no loss from
summing individual Cauchy--Schwarz bounds.

For the actual evaluation kernel this gives, uniformly in N,

    sum_(p odd prime, p>P) G(k_N,n,p) <= 4 zeta(2)n^2/P^4.

Let Lambda_P(N,n) retain only odd primes p<=P. The actual finite cutoff
is defined in Lean as primeCutoff P. Then exactly the difference from
complete screening is the omitted nonnegative gain, and

    0 <= Lambda_P(N,n)-Lambda_infinity(N,n) <= 4 zeta(2)n^2/P^4.

In particular, n^2<=P^4 implies this gap is at most 4 zeta(2).
Choosing P=ceil(sqrt(n)) is an ordinary explicit corollary; the ceiling
selection itself is not separately formalized. Multiplication by the
already established epsilon_N<=1 preserves this additive bound.

Consequently, a uniform error-weighted bound for complete prime-square
screening could be transferred to this explicit finite cutoff, with an
additive 4 zeta(2). **The complete bound itself has not been proved.**
A bound on the gain omitted by truncation is not a bound on the energy
that survives screening.

## Source map and formal status

All named declarations below are in namespace
RiemannResearch.RH.QPrimeSquareKernelScreening unless stated otherwise.

- RH/QPrimeSquareKernelScreening.lean:
  primeSquareSupport_disjoint;
  primeSquareVector_inner_residue, primeSquareVector_inner_stage,
  primeSquareVector_inner_one, residual_inner_primeSquareVector;
  primeSquareVector_norm_sq, primeSquareVector_orthogonal,
  smoothed_primeSquareVector_orthogonal;
  smoothed_primeSquareVector_norm_sq_le,
  primeSquareVector_norm_sq_lower, smoothed_primeSquareVector_ratio;
  primeSquareGain_complete_tail, kernel_primeSquareGain_complete_tail;
  finite_primeSquare_screening;
  primeSquareGain_summable, completePrimeSquareEnergy_nonneg,
  completePrimeSquareEnergy_exact,
  movingCorrection_sq_le_completePrimeSquare;
  primeSquareGain_truncation, primeCutoff_covers,
  finite_complete_energy_gap, finite_complete_energy_gap_le_constant.
- Analysis/OrthogonalKernelScreening.lean:
  orthogonal_norm_sum; weighted_bessel_finite and weighted_bessel_complete;
  orthogonal_normal, orthogonal_screening_norm_sq,
  pairing_sq_le_orthogonal.

The general weighted Bessel statement allows arbitrary positive
denominators d_i and a common ratio bound ||t_i||^2<=rho*d_i. It handles
zero numerator vectors without introducing normalization assumptions.

The coherent combined proof candidate succeeded on the user's Lean
server in job_p62hC85lPj36tDCyCwd_DHy65x7HW32J, verified=true,
reported verification duration 7.872 seconds. This is snippet evidence;
the final project checkpoint is the publication gate. The final response
records its terminal job, validation scope, and exact published commit.

The persisted-module import/type/axiom audit also succeeded in
job_HoxVrRknTSSTZWRLCsF8gQtrqvzXt_Vg, verified=true, with reported
verification duration 20.480 seconds. It built both changed Lean modules,
printed the full types of the finite screening, complete tail, complete
coupled bound, and finite-cutoff gap declarations. The three central
axiom checks report only propext, Classical.choice, and Quot.sound.
Those declarations have no RH or target-membership hypothesis. Their
conclusions are the displayed estimates, not RiemannHypothesis.

Wolfram checked the elementary prime-square norm polynomial and the two
geometric-series identities in the pulse argument below. These outputs
are diagnostics, not Lean proofs. Wolfram's context operation returned
an internal error; its evaluator succeeded.

## Research agenda after this continuation

1. **Open, primary provider:** prove C>=0 and
   epsilon_N*Lambda_infinity(N,n)<=C^2 for every 1<=n<=N, or the
   corresponding common bound for Lambda_P at the explicit cutoff.
   The tail theorem now removes arbitrary truncation uncertainty from
   this particular family. It does not control the surviving term.
2. **Open, alternative provider:** bound the actual signed shrinking-head
   response with its complete uniformly vanishing remainder, using the
   full nested normal equations. No new signed bound was obtained.
3. **Open, larger families:** determine whether including mixed-prime
   radical rows supplies a bound missed by prime-square screening.
   Preserve their full Gram matrix; do not add overlapping normalized
   squares as if the rows were orthogonal.
4. **Established here only as an ordinary argument:** local radical
   compatibility permits nearly point-concentrated prime-power pulses;
   see the full proof below. A generic sublinear evaluation estimate on
   W cannot replace a stage-specific estimate on (P_W-P_N)BP_Ne_n.
5. The dyadic infinite block formula, full inverse-response obstruction,
   and a single sublinear head selector were not formalized in this
   continuation; none supplies the missing provider by itself.
6. Only after an actual provider is discharged should the existing
   moving-head consumer be applied and an exact assumption-free theorem
   of type RiemannHypothesis audited. No such theorem is asserted here.

For the fully local constraint space W, neither W=V nor density of the
legal span has been assumed. The following ordinary obstruction concerns
general elements of W; it is not a counterexample to the actual kernel
estimate.

---

# Radical-compatible prime-power pulses: a complete-tail obstruction

This note is an ordinary mathematical proof, not a Lean-verified result. It does not establish the uniform correction bound or RH.

Put `Z = zeta(2)` and `Q(n) = 1/(Z n^2)` for positive integers. For an integer `a >= 2`, define

\[
F_a(n)=\#\{k\ge1:a^k\le n\}=\lfloor\log_a n\rfloor.
\]

Fix integers `2 <= p < q`, write `D=q-p`, and put `h=F_p-F_q`. The norm estimate below does not require primality; primality is needed for radical compatibility.

## Exact pulse identity and a universal complete norm estimate

For `k >= 1`, let `I_k = [p^k,q^k) intersect N`. Then

\[
h(n)=\sum_{k\ge1}\mathbf1_{I_k}(n).
\]

The intervals need not be disjoint. At any fixed `n`, if `A=F_p(n)` and `B=F_q(n)`, their active indices are exactly `B+1,...,A`. Consequently

\[
\sum_{k\ge1}(2k-1)\mathbf1_{I_k}(n)=A^2-B^2
\ge(A-B)^2=h(n)^2.                                      \tag{1}
\]

For positive integers `a < b`, telescoping gives

\[
\sum_{n=a}^{b-1}\frac1{n^2}
\le\left(1+\frac1a\right)\sum_{n=a}^{b-1}\frac1{n(n+1)}
=\left(1+\frac1a\right)\left(\frac1a-\frac1b\right).
\]

Using `q^k-p^k <= k D q^(k-1)`, this yields

\[
\sum_{n=p^k}^{q^k-1}\frac1{n^2}
\le\left(1+\frac1p\right)\frac{kD}{q p^k}.                \tag{2}
\]

All summands are nonnegative, so Tonelli's theorem applies without an advance summability assumption. Combining (1), (2), and

\[
\sum_{k\ge1} k(2k-1)x^k=\frac{x(1+3x)}{(1-x)^3},
\qquad 0<x<1,
\]

proves the complete infinite-tail bound

\[
\boxed{\displaystyle
\|F_p-F_q\|_Q^2
\le \frac{D(1+1/p)(1+3/p)}{Z\,p q\,(1-1/p)^3}.}          \tag{3}
\]

In particular, the sequence belongs to the actual Q-Hilbert space. No physical-tail truncation or assumption that the pulse intervals are disjoint has been made. There is no condition `q <= p^2` in (3).

## Explicit control of every remote pulse

If `q <= p^2`, then `h(n)=1` on `p <= n < q`, and `h(n)=0` below `p`. For `n >= q` one has `B=F_q(n)>=1`; the active-index identity strengthens to

\[
h(n)^2\le\sum_{k\ge2}(2k-3)\mathbf1_{I_k}(n),
\]

because the sum on the right equals `(A-B)(A+B-2)` and `A+B-2 >= A-B`. Thus

\[
0\le\|h\|_Q^2-\frac1Z\sum_{n=p}^{q-1}\frac1{n^2}
\le\frac{(1+1/p)D}{Zq}\,
\frac{p^{-2}(2+3/p-1/p^2)}{(1-1/p)^3}.                   \tag{4}
\]

Here the geometric identity is

\[
\sum_{k\ge2}k(2k-3)x^k
=\frac{x^2(2+3x-x^2)}{(1-x)^3}.
\]

For `D/p -> 0`, inequalities (3) and the first-pulse lower bound give

\[
\|F_p-F_q\|_Q^2\sim\frac{D}{Zp^2}.
\]

The estimate (4) shows directly that all remote pulses together contribute `O(D/p^3)` in this regime.

## Membership in the local radical space

Let `W` be the closed subspace of the actual Q-Hilbert space satisfying

\[
\Delta f(j)=\Delta f(\operatorname{rad}j)
\quad\hbox{for every nonsquarefree }j\ge2,
\qquad \Delta f(j)=f(j)-f(j-1).
\]

When `p` is prime,

\[
\Delta F_p(j)=\mathbf1_{\{p,p^2,p^3,\ldots\}}(j)
=\mathbf1_{\{\operatorname{rad}j=p\}}.
\]

Hence for distinct primes `p<q`, the sequence `h=F_p-F_q` satisfies every radical relation. Together with (3), this proves `h in W`. Also `h(p)=1`.

Let `ev_p` denote physical evaluation on `W`. Therefore

\[
\boxed{\displaystyle
\|\operatorname{ev}_p|_W\|^2
\ge\frac{Z p q(1-1/p)^3}
{(q-p)(1+1/p)(1+3/p)}.}                                  \tag{5}
\]

The ambient upper bound remains `||ev_p||^2 <= Z p^2`.

## Consequence using bounded prime gaps

Polymath's theorem supplies infinitely many pairs of consecutive primes `p<q` with `q-p<=246`:

- D. H. J. Polymath, *Variants of the Selberg sieve, and bounded intervals containing many primes*, Research in the Mathematical Sciences 1 (2014), article 12; arXiv:1407.4897; DOI:10.1186/s40687-014-0012-7.
- Primary URL: https://arxiv.org/abs/1407.4897

For `p>=5`, `(1+1/p)(1+3/p)/(1-1/p)^3 <= 15/4`. Thus along such an infinite subsequence,

\[
\frac{4Z}{15\cdot246}\,p^2
\le \|\operatorname{ev}_p|_W\|^2
\le Zp^2.                                               \tag{6}
\]

So imposing every local radical constraint does not improve the order of the evaluation cost: its norm is still of order `p` along an infinite subsequence. This rules out a uniform evaluation bound on `W`, or a sublinear universal evaluation estimate on `W`.

This is **not** a counterexample to the actual screened-energy target. The vectors in (3) are general elements of `W`, not the specific residualized kernels `(P_W-P_N) B P_N e_n`. A proof of that target may still exploit smoothing, the full nested stage normal equations, and the coupling with `epsilon_N`.


## Retained workspace

    workspace_token: ws_zCyeA026LTyKnPjK1elHwt1yH05NCoqO
    project_root: /home/cri_2025/lean-agent-workspaces/ws_zCyeA026LTyKnPjK1elHwt1yH05NCoqO/RiemannResearch

Resume this token if valid, and follow any continuation workspace returned
by publication. Verification submissions remain serialized across agents.
