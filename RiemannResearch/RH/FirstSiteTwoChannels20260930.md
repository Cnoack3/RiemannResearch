# Two gain channels, balanced nonprime trials, and the next research stages

Date: 2026-09-30 (America/Los_Angeles).
Requested base: 4f4ede96e4e8fd5167f4f389bf03c64ee47670cc.
Continuation of its published descendant be45e99a22abe009356faf7dd686248b4ebb77d5.

## Outcome and mathematical boundary

This investigation combines the exact repository budgets with classical
Burnol/PNT estimates. It proves on paper that the separate mean-channel
alternative is redundant once the survivor slope tends to zero. It also
derives an actual signed lower certificate for nonprime Schur gains, with a
concrete binary-bucket application. Neither argument supplies the remaining
arithmetic divergence. RH is not proved; no claim of mathematical priority
or a breakthrough toward resolving RH is made.

Lean formalizations are in Analysis/VanishingRegressionSlope.lean,
RH/ParetoFirstSiteAngularTwoChannels.lean, and RH/ParetoBalancedSchurTrial.lean.
The formalizations' analytic rate and RH-to-approximation inputs remain explicit.
The verification ledger below distinguishes the paper proofs from execution.

## 1. Preserved exact quantities

Use w_n=primeSchurWeight n, delta_n=factorialPrimeDelta n,
kappa_n=factorialPrimeError n and eta_(n+1)=delta_n+kappa_n at prime stages.
Every w_n is the actual inverse Schur pivot, and is zero at nonprime stages.
Put
```
U_N = sum w_n delta_n^2
X_N = sum w_n delta_n kappa_n
G_N = sum w_n eta_(n+1)^2
tau_N = (U_N+X_N)/U_N
R_N = (U_N+X_N)^2/U_N
W_N = sum_(n<N) Gamma_n
```
Real division by zero gives tau_0=R_0=0. The established full identities are
```
G_N = R_N + W_N
C_(N+1) = C_1 + R_N + sum_(n<N) Gamma_n + J_N
Gamma_n = w_n*(U_n*kappa_n-X_n*delta_n)^2 /
          [U_n*(U_n+w_n*delta_n^2)]
kappa_n = base_n + sum_(m<n) factorialPrimeCrossGram(n,m).
```
No determinant factor, screened CRT row, historical slope, initial capacity
or nonprime gain is omitted. The physical tails remain in the Hilbert vectors.

The survivor form of the complete scatter is exact:
```
W_N = sum_(n<N) w_n [eta_(n+1)-tau_N delta_n]^2.
```
It follows either by shifting the error fit, or by applying the finite
centered-square quotient to the source/survivor pairing U_N+X_N.

## 2. How Burnol and PNT constrain the actual scale

These are unconditional classical inputs. Their analytic proofs and the
complete rate transfer are not asserted to be newly kernel-formalized.

Burnol's Theorems 1.2–1.3 give the approximation-distance lower bound
d_M >= c/sqrt(log M) eventually, for c>0. If RH fails, the distance has a
positive limiting obstruction, so the lower bound remains true. Thus it
does not assume RH as a premise.

For the actual point approximant f_N, let T=(1/2)D_2, q=1/sqrt(2),
S_K=sum_(k<K)T^k and Delta_N=1/(C_N+2). First keep the complete equality
```
1-S_K f_N = T^K 1 + S_K(e_1-f_N)
||1-S_K f_N||^2 =
 ||T^K 1||^2 + 2< T^K 1,S_K(e_1-f_N)> + ||S_K(e_1-f_N)||^2.
```
Only then use
d_M <= q^K+(1-q)^(-1)sqrt(Delta_N), with M<=(N+1)2^K.
Taking K=ceil(log_2(N+1)) gives M<=2(N+1)^2 and q^K<=(N+1)^(-1/2).
Burnol therefore gives Delta_N >= c'/log(N+1), and C_N=O(log(N+1)).
The embedding of centered integer residues is isometric, so this transfer
does not replace the Pareto norm by an unrelated Haar norm.

For a fresh prime p and P=(p-1)!, the exact factorial Euler product is
```
M_P = product_(q>=p, q prime) (1-q^(-2))^(-1)
delta_p = M_P/[p^2(M_P-1)].
```
PNT and partial summation yield sum_(q>=p)q^(-2) ~ 1/(p log p).
Expanding log M_P retains an error O(sum_(q>=p)q^(-4)), which is negligible.
Hence M_P-1 ~ 1/(p log p), and delta_p ~ (log p)/p.
The checked pivot estimate sigma_p<=2/p implies
w_p delta_p^2 >= (1/2-o(1))(log p)^2/p.
A second partial summation gives
sum_(p<=x)(log p)^2/p ~ (1/2)(log x)^2.
Consequently U_N >= (1/4-o(1))(log N)^2, and
```
C_(N+1)/U_N -> 0.
```

The repository already contains an unconditional PNT development in
NumberTheory/PrimeNumberTheorem/Consequences.lean (WeakPNT', WeakPNT'',
chebyshev_asymptotic and prime-count consequences), ported from
AlexKontorovich/PrimeNumberTheoremAnd at
a5154676af9aa3095150ee410cdda80555aa0642. This investigation read the proof
chain; a new endpoint axiom audit could not run during the execution outage.
The factorial tail/product and capacity-rate assembly still needs a Lean proof.

Source: J.-F. Burnol, A lower bound in an approximation problem involving
the zeros of the Riemann zeta function, arXiv:math/0103058, Theorems 1.2–1.3.
https://arxiv.org/abs/math/0103058
The transfer above is a deduction using repository identities.

## 3. New finite-head theorem and two-channel consequence

The exact completion gives 0<=R_N<=G_N<=C_(N+1). Since
tau_N^2=R_N/U_N for N>0, the capacity/source limit implies tau_N->0.

Suppose W_N<=B for all N and tau_N->0. Fix M. For every N>=M,
```
sum_(n<M) w_n [eta_(n+1)-tau_N delta_n]^2 <= W_N <= B.
```
Take N->infinity on this fixed finite sum. It gives G_M<=B.
Every G_M is therefore bounded, so the nonnegative prime-gain series is
summable. This argument never exchanges a growing sum and a limit.

Conversely, G_N=R_N+W_N and nonnegativity show that summable prime gains
imply summable Gamma. Thus, under tau_N->0,
```
Summable Gamma <-> Summable factorialPrimeGain.
```
When Gamma is summable, take B=sum' Gamma in the fixed-head argument:
```
G_N <= sum' Gamma
R_N <= sum' Gamma - sum_(n<N) Gamma_n.
```
The repository's finite-head/tail pairing theorem, together with U_N->infinity,
then gives R_N->0. Taking limits in G_N=R_N+W_N gives the exact equality
sum' factorialPrimeGain = sum' Gamma.

These statements hold independently of whether the nonprime series converges.
If both series are summable, the entire capacity satisfies
```
C_(N+1) <= C_1 + sum' Gamma + sum' factorialCompositeGain.
```
The three-channel criterion consequently becomes
```
C_N -> infinity <->
 (Gamma is not summable) OR (factorialCompositeGain is not summable).
```
With the published Báez-Duarte RH-to-natural-approximation theorem this is
also a classical RH equivalence. The Lean declaration retains both
hBaezDuarte and C_(N+1)/U_N->0 explicitly; it installs neither as an axiom.

This does not assert that the mean term is negligible relative to angular
energy at all stages, or that prime divergence alone is necessary for RH.
The initial capacity and every J_N remain in the exact ledger.

## 4. An actual balanced nonprime Schur test

Write t_q for the tail atom with conductor q, and z_n=tailMinimum n.
For an old row i<n choose a so that a/(i+2)=1/(n+2), and put
v=t_(n+2)-a t_(i+2). The old reciprocal constraint gives exactly
```
eta_n = -<v,z_n>.
```
For the complete old Gram coefficient vector c=a times the i-th coordinate,
the exact minimization identity is
```
||v||^2 = sigma_n +
 ||synthesis(c-inverseCoeff(t_(n+2)))||^2.
```
The full projection remainder precedes the inequality sigma_n<=||v||^2.
For any K>0 with ||v||^2<=K,
```
< v,z_n >^2/K <= eta_n^2/sigma_n.
```
If n+2 is composite, the right side is exactly its nonprime gain.
RH/ParetoBalancedSchurTrial.lean contains this general finite certificate.
It makes no assumption about the sign of v or z_n.

A particularly concrete paper specialization is q=2p, p>=2:
```
v_p=t_(2p)-(1/2)t_p = (1/p)D_p g_2
v_p(k)=(1/2) indicator{ k mod (2p) >= p }
||v_p||^2=log(2)/(4p).
```
The head values cancel exactly. The vector identity follows from
residue(2p)-residue(p)=p*residue(2)(floor(k/p)).
The repository's exact integer dilation norm gives the displayed norm.
Equivalently, retain every bucket period and telescope its positive weights:
```
||v_p||^2 = (1/4) sum_(j>=0)
 [1/(2jp+p)-1/(2jp+2p)] = log(2)/(4p).
```
Thus at the actual stage n=2p-2, without discarding screening,
```
gain_(2p) = <v_p,z_(2p-2)>^2/sigma_(2p-2)
          >= (4p/log 2) <v_p,z_(2p-2)>^2.
```
The complete infinite pairing is
(1/2)sum_{k>=1, k mod 2p>=p} z_(2p-2)(k)/[k(k+1)],
which converges by Hilbert Cauchy–Schwarz. It is a signed pairing with the
actual adaptive minimum vector; no positivity of that vector is assumed.

For prime p these are distinct composite conductors 2p. Nonsummability of
the lower bucket-pairing energies on those primes would force J_N unbounded,
hence capacity divergence and RH. This is a concrete sufficient arithmetic
task. The doubling identity, exact norm and infinite-prime subset transfer
are paper deductions here; the Lean candidate proves the general old-row
certificate, not the complete specialized series provider.

## 5. Numerical screening, with full physical tails

Exploratory double-precision computation used the checked full-period
digamma formula for g_d,g_e, subtracted the exact head term 1/(2de), and
Cholesky-factorized the full tail Gram for every conductor 2,...,258.
No finite physical-tail truncation was used. A Cholesky row gives
sigma_i=L_ii^2, eta_i=L_ii*(L^(-1)b)_i, with b_d=1/d.
The exact factorial Euler product supplies delta at prime rows.

Rounded results (budget N uses capacity C_(N+1)):

| N | C_(N+1) | U_N | R_N | sum Gamma | J_N |
| --- | ---: | ---: | ---: | ---: | ---: |
| 16 | 30.139085 | 29.621774 | 0.028958 | 1.424953 | 23.507776 |
| 32 | 38.191376 | 58.817982 | 0.122954 | 2.040215 | 30.850808 |
| 64 | 45.357567 | 113.345618 | 0.361659 | 2.628936 | 37.189573 |
| 128 | 51.485069 | 231.978972 | 0.387224 | 3.384711 | 42.535735 |
| 256 | 59.940413 | 474.031777 | 0.425007 | 4.542433 | 49.795574 |

C_1 is about 5.177399. The ledger residual was below 3e-14.
The condition number reaches about 1.62e5, so these are exploratory values,
not interval certificates. Agreement of two rearrangements does not certify
the underlying entries or their asymptotics.

| block | full angular sum | internal scatter | historical drift | pooled split test | nonprime gain |
| --- | ---: | ---: | ---: | ---: | ---: |
| [16,32) | 0.615262 | 0.602793 | 0.012468 | 0.070709 | 7.343033 |
| [32,64) | 0.588722 | 0.574551 | 0.014170 | 0.069154 | 6.338764 |
| [64,128) | 0.755774 | 0.701624 | 0.054151 | 0.099066 | 5.346162 |
| [128,256) | 1.157722 | 1.103615 | 0.054106 | 0.011836 | 7.259840 |

At these cutoffs most angular energy is internal scatter, and the simple
pooled half-block test captures only a small part. Nonprime gains dominate
total capacity. Several large late nonprime gains occur at 2p:
202=2*101 gives about 0.420784; 194=2*97 gives about 0.348966.
Other composites also contribute. These observations motivate keeping
all-row contrasts and the nonprime bucket route together. They establish
no uniform lower bound, limit, or divergence.

## 6. A sequence of research stages

1. **Complete the scale transfer in Lean.**
   Use the existing PNT endpoint to prove the factorial prime-square tail
   estimate and a dyadic source lower bound. Formalize the Burnol
   point-to-constant reconstruction transfer with its full norm square.
   Then supply the explicit C/U->0 premise of the new two-channel theorem.
   This stage is an analytic/formal bridge, not the remaining RH step.

2. **Attack internal prime-block scatter with balanced tests.**
   Use the existing automatically source-balanced c_j and exact
   Q_j=L_j^2/D_j. Retain the full screened CRT expansion of L_j.
   A concrete sufficient target is D_j<=K(j+1), |L_j|>=ell>0 on enough
   dyadic blocks for the resulting harmonic lower mass to diverge.
   Alternatively prove sum_{j=m}^{2m-1}Q_j>=c>0 eventually.
   PNT gives lower source mass in both half-blocks, but cannot give the
   signed pooled slope separation. The finite pooled test is therefore
   a comparison tool rather than the sole target.

3. **Develop the 2p nonprime bucket route in parallel mathematically.**
   Formalize v_p=(1/p)D_p g_2 and its exact norm, instantiate the balanced
   Schur test, and transfer distinct prime-indexed 2p energies into J.
   Then seek a lower bound on sums of actual bucket pairings with z_(2p-2).
   These vectors already contain the full earlier dictionary screening.
   A large-sieve upper bound could control the norm of a combined signed
   test; a separate signed pairing lower estimate is still needed.

4. **Use the signed CRT/Abel route as an independent closing target.**
   DerivativeMobiusCRT.lean already proves complete conductor-one
   lcm-intersection cancellation uniformly in the optimization dimension.
   The surviving reciprocal correction charge is not removed by that
   cancellation. Target the exact endpoint-plus-harmonic primitive charge
   A_n=q_n: for every epsilon>0 and N, find n>=N with A_n>-epsilon.
   The repository proves that this condition kills the actual residual
   and implies RH. Transfer any new arithmetic estimate to that combined
   charge before using it; bounding only its CRT remainder is insufficient.

5. **Compare smoothing and polynomial-density results with actual costs.**
   Alouges–Darses–Hillion prove unconditional generalized NB density for
   exponentially decaying Mellin kernels. Their Theorem 3 also requires
   quantitative approximation and kernel-tail conditions:
   M_n^(2sigma_0-1)||phi-G_n^x||_2^2->0 and
   M_n^(sigma_0-1)integral_{M_n}^infinity|G_n(t)|dt->0.
   Their Theorem 6 supplies density, not this second rate. Choose the kernel
   and coefficient construction, retain its entire signed tail and
   conductor cost, and check both rates before transferring to RH.
   The block-Hankel Gram recurrence is a possible computational bridge,
   not a positive inverse-Gram bound by itself.

6. **Only pursue Li/Weil/operator synthesis with a concrete bridge.**
   The repository has the actual Li equivalence, full signed zero formulas
   with multiplicities, and an operator core. A usable new result must
   control actual Li positivity, the reflected Weil correction, or both
   dense shifted ranges plus a spectrum-to-zeta identification. The
   presence of these imports alone supplies no arithmetic growth.

The remaining RH-strength step is at stages 2, 3 or 4 (or the quantitative
tail estimate in stage 5), not at the generic finite-head limit.

## 7. Primary literature reviewed and admissible uses

- Burnol, arXiv:math/0103058, Theorems 1.2–1.3:
  unconditional distance lower bound used in the scale deduction above.
- Burnol, arXiv:math/9910055, Theorem 1.2:
  continuous projection product over off-line zeros; compatible with the
  repository's explicit projection-identity premise. It does not make
  that product equal one unconditionally.
- Alouges, Darses, Hillion, arXiv:2006.02953v2, Theorems 3 and 6:
  https://arxiv.org/abs/2006.02953
  separate unconditional polynomial density from the required quantitative tail.
- Darses, Hillion, arXiv:1805.06733v4:
  https://arxiv.org/abs/1805.06733
  probabilistic/general NB criteria require explicit support, moment or
  coefficient conditions; randomization does not supply them automatically.
- Darses, Hillion, arXiv:2004.10086:
  https://arxiv.org/abs/2004.10086
  exact exponentially averaged Vasyunin/Gram formula, useful for comparing
  smoothing constructions, not a proved inverse-Gram lower bound.
- Ehm, arXiv:2405.06349v2, exact Gram formulas and Proposition 8.1:
  https://arxiv.org/abs/2405.06349
  moment-centering corrections are useful comparisons; Section 8 identifies
  the unproved product estimates needed for the complete quadratic form.
- Bettin, Conrey, Farmer, arXiv:1211.5191, Theorem 1:
  https://arxiv.org/abs/1211.5191
  optimal mollifier error assumes RH and a reciprocal zeta-derivative
  moment bound. It is not used as an unconditional RH provider.
- Repository large-sieve imports pinned in ResearchImports20260930.md:
  exact finite Parseval/DFT and conductor-averaged upper energy bounds.
  The actual CRT Fourier/weighted-tail transfer and signed pairing lower
  estimate still have to be proved.

## 8. Verification and continuation ledger

The initial serialized source checks timed out with zero diagnostics. Those
timeouts did not establish or refute a proof. The original publishing checkpoint
`job_e71bWLxwW6Ko2zCxGEFTavC_Q3fdNMdI` was subsequently recovered as terminal
`interrupted`: its worker exited while it was pending and it was not replayed.
Its dirty workspace and all source candidates were preserved.

On October 1, 2026 UTC, source execution recovered. Two coherent ephemeral Lean
checks compiled the complete declaration bodies with their intended imports:

- `job_ZsK2rFhy2jzVtSlv1C5A7di2gYzpU3y3`: balanced old-row trial and adjacent
  Schur bound; terminal success, exit 0, verified true, 5.397 seconds.
  Code SHA256: `33511cdde63e677aa5024b9853248f3a2755b2caad99edd2eef1b82727eb8846`.
- `job_ml0tBTMOse-XCO-XkCQFdGgFwJ3W5DPG`: generic fixed-head limit and the
  two-channel application; terminal success, exit 0, verified true, 3.648 seconds.
  Code SHA256: `a63c16f3ae7b0147adc6e21ab1775cd7c20f0024db502127a9ca142fe075026e`.

An earlier two-channel check caught a rewriting error in the total-mass limit:
the bare function needed eta expansion before the finite-sum equality could
rewrite it. Adding the explicit function form repaired the proof without
changing its statement or hypotheses. The installed source includes this repair
and the current Mathlib spelling `tendsto_finsetSum`.

The audited declarations were:
`square_le_of_bounded_centered_prefixes`,
`primeMeanMismatchBudget_le_angular_tail`,
`primeAngularInnovation_summable_iff_gain_of_slope_zero`,
`RH_iff_two_gain_channels_of_sublinear_source`,
`adjacentInnovationLower_sum_le_capacity`, and
`factorialPrimeSourceEnergy_ge_adjacent_harmonic`.
Each printed only `propext`, `Classical.choice`, and `Quot.sound`.
The combined adjacent check also compiled the full balanced completion and
actual composite-gain certificate.

These are isolated kernel checks of the declaration bodies. Final integrated
acceptance and publication use the prescribed checkpoint, which validates
installed modules and affected dependents before committing and pushing.
The exact type of `RH_iff_two_gain_channels_of_sublinear_source` still exposes
both `hBaezDuarte` and the capacity/source limit. An axiom audit does not
discharge these local hypotheses. Burnol/PNT scale arguments remain paper
deductions, and the actual arithmetic divergence provider remains Open.

The recovered adjacent assembly is documented separately in
`AdjacentSchurResearch20260930.md`. No RH or mathematical-priority claim is made.
