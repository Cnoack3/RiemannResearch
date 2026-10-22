# RH agenda execution: exact projections, weighted minima, and reciprocal charges

Prepared for Christian Noack, 24 September 2026.

Baseline: `b9386b3fedbd0a5d08191366052702960209e4d5` in
`Cnoack3/RiemannResearch`, matching both the supplied agenda and GitHub main
when this continuation began. No newer baseline changes were omitted.

**RH remains unproved.** This continuation attempts every agenda track,
completes several concrete formalization tasks, and separates the remaining
arithmetic estimates from missing classical representation imports.

## 1. Scope and status

All eleven new modules passed serialized Lean proof-batch checks. Principal
axiom inspections reported only `propext`, `Classical.choice`, and `Quot.sound`.
Final publication is gated by the repository checkpoint, which checks the
individual module imports and affected reverse dependencies.

| Agenda task | Result | Still missing |
|---|---|---|
| 1. Scalar Schur correction | Exact signed recurrence; exact two projection budgets; absolute mixed variation at most sqrt(2) | Signed saturation: the mixed sum equals 1, or equivalently r(1)=0 |
| 2. Independent weighted approximation | Actual positive cell weights, complete weighted Gram matrix, exact inverse minimum, cutoff monotonicity, closure transfer, optimized convergence for u>=2 | Vanishing minima at weights approaching 1; no fixed 1<u<2 convergence established |
| 3. Residual tails | Exact dyadic shells, signed legal observations, arithmetic Abel identity at complete periods | A cofinal upper bound for N T_N, or actual Noor regularity |
| 4. Charges | One-sided mass criterion; Balazard's ordered reciprocal identity; explicit bounds for its representing vectors | An unconditional estimate of the actual residual's one-sided charge mass |
| 5. Classical imports | Primary-source audit and the targeted Balazard import | Burnol projection representation, full BSY boundary passage, local RH-to-integer-density converse |

The actual RH-strength conditions in the final column are not assumed true
or installed as axioms. Completed conditional implications keep their
arithmetic premise explicit in their Lean type.

## 2. Exact signed recurrence and absolute mixed variation

Use the agenda's paper cutoff V_N=span{g_2,...,g_N}. Lean stage n=N-1.
For d=N+1, the actual Schur complement and two numerators are

```math
\sigma_N=a_N-k_N^\top G_N^{-1}k_N,
\qquad
\eta_t=\frac1d-k_N^\top G_N^{-1}t_N,
\qquad
\eta_b=\frac{\log d}{d}-k_N^\top G_N^{-1}b_N.
```

`RH/ReciprocalSchurVariation.lean` proves

```math
W_{N+1}-W_N=\frac{\eta_t\eta_b}{\sigma_N}+\frac{\mu(d)}d.
```

The signed product is preserved. The finite Cauchy--Schwarz inequality is
proved on every finite set of stages, with the two squared-numerator sums
identified with their actual projection budgets. In particular,

```math
\sum_N\left|\frac{\eta_t\eta_b}{\sigma_N}\right|\le\sqrt2,
\qquad
\sum_N\frac{\eta_t\eta_b}{\sigma_N}=1-r(1).
```

These are statements about the complete mixed series beginning with the
empty span. The absolute-summability assertion does not include the separate
Möbius increments. The signed value remains undetermined: absolute convergence
does not show that this sum is 1.

Principal declarations: `reciprocalEta_eq_gram_schur`,
`reciprocalCorrection_schur_step`, `mixedSchur_prefix_budgets`,
`mixedSchur_sum_abs_sq_le_budgets`, `mixedSchur_norm_summable`,
`mixedSchur_tsum_eq_one_sub_residual`, `mixedSchur_abs_tsum_le_sqrt_two`.

## 3. Actual weighted finite optimization

`RH/ParetoWeightedCells.lean` constructs the exact cell weights

```math
w_u(k)=\frac{k^{-u}-(k+1)^{-u}}u>0\quad(u>0,k\ge1).
```

For every actual Hilbert vector and u>=1, the complete infinite weighted
integral is identified with its cell sum. At u=1 it is exactly the original
Pareto norm squared; the target's weighted energy is exactly 1/u.

`RH/ParetoWeightedGram.lean` transports this norm using a positive diagonal
contraction, proves injectivity, and derives independence of the actual
finite residue family. Thus positive definiteness of the weighted Gram
matrix is proved, rather than supplied as an additional premise.

```math
G_N^{(u)}(d,e)=\sum_{k\ge1}w_u(k)g_d(k)g_e(k),
\qquad b_N^{(u)}(d)=\sum_{k\ge1}w_u(k)g_d(k),
```
```math
c_N^{(u)}=(G_N^{(u)})^{-1}b_N^{(u)},
\qquad
D_N(u)=\frac1u-(b_N^{(u)})^\top(G_N^{(u)})^{-1}b_N^{(u)}.
```

The constructed legal vector attains the minimum over every finite coefficient
vector in the complete weighted norm. The minimum decreases with cutoff.
Continuity in the original Pareto topology proves that allowing its original
legal closure does not lower the infimum over finite legal vectors.

The existing actual PNT approximants give, unconditionally,

```math
\forall u\ge2,\qquad D_N(u)\longrightarrow0.
```

The new criterion `riemannHypothesis_of_minima` connects these particular
optimizers to the previously verified independent-weighted-approximation
criterion. Its premise for weights tending to 1 remains open. No bounded
inverse for the diagonal embedding is used, and no estimate is transferred
back to the stronger critical norm without justification.

Principal declarations include `complexPhysicalStep_weighted_energy`,
`weightedCellWeight_pos`, `embedding_inner`, `matrix_posDef`, `matrix_entry`,
`minimum_eq_matrix_inverse`, `approximant_minimizes`, `minimum_antitone`,
`finite_legal_approximation_iff_closure`, `minimum_tendsto_zero_of_two_le`.

## 4. Exact shells and arithmetic tail-average observations

`RH/ParetoResidualShell.lean` proves the requested identity

```math
(2N)T_{2N}=2NT_N-2N\sum_{N<k\le2N}\frac{r(k)^2}{k(k+1)}.
```

For legal f and g with exact heads through N and N+M, respectively, it also
proves the complete signed cancellation

```math
\sum_{N<k\le N+M}\frac{r(k)(1-f(k))}{k(k+1)}
=-\langle r_{>N+M},(g-f)_{>N+M}\rangle_P.
```

The corresponding Cauchy--Schwarz bound retains the whole correction tail,
and the theorem is specialized to the actual canonical Möbius family.

`RH/ParetoTailAverageArithmetic.lean` further uses the genuine residue jump.
With B_n=tailAverage(r,n)/(n+1), at a complete period m|N,

```math
\sum_{n<N}\left(\frac1m-\mathbf1_{m\mid n+1}\right)B_n
=-\langle r_{>N},(g_m)_{>N}\rangle_P.
```

The general finite Abel identity includes its boundary term. The two component
infinite sums are never separated without a convergence argument. These
identities constrain the tails; they do not supply the required upper rate.

## 5. One-sided mass and the reciprocal charge identity

`RH/MobiusResidualOneSidedMass.lean` proves that

```math
\sum_{m\ge2}\max(-\delta_m(r),0)\,\|g_m\|_P<\infty
\quad\Longrightarrow\quad\mathrm{RH},
```

and proves the positive-sign counterpart. The proof reconstructs the summable
part and applies the existing order theorem to the remaining one-sign vector.
Under failure of RH, both finite weighted sign masses tend to positive infinity.
Neither actual summability premise is established.

The targeted classical import is Balazard, arXiv:1812.04309, Propositions 5--7.
The new chain consists of `NumberTheory/QuotientWindowSquareBound.lean`,
`RH/MobiusQuotientEnergy.lean`, `RH/MobiusReciprocalChargeBridge.lean`, and
`RH/BalazardReciprocalCharge.lean`. For the actual reciprocal-charge Riesz vector
Q_N it proves

```math
\|Q_N\|_P^2\le42,\qquad Q_N\rightharpoonup0,
\qquad
\sum_{m=1}^N\frac{\delta_m(f)}m\longrightarrow0\quad(f\in H_P).
```

The uniform bound comes from an explicit quotient-window square bound 10;
fixed-coordinate decay uses the existing PNT provider. Removing the first
charge gives the exact limit -f(1). The representation also proves

```math
Q_N(N)=N+1,\qquad \frac{N+1}{N}\le\|Q_N\|_P^2\quad(N\ge1).
```

Thus these vectors do not converge to zero in norm. Ordered reciprocal charge
cancellation does not imply convergence of legal reconstructions or charge
vanishing. The final reciprocal-sum theorem has no unproved arithmetic premise.

## 6. Fixed raw residuals: what is and is not now formalized

`RH/NaturalMobiusPhysicalTests.lean` uses the raw residual A_N, not the optimized
projection and not the boundary-corrected canonical family. It proves

```math
A_N(k)=k\sum_{d\le N}\frac{\mu(d)}d\quad(1\le k\le N),
\qquad |A_N(k)|\le\min(N,k)\quad(N\ge1),
```

and pointwise convergence to zero. It also proves full inner-product convergence
for the explicit test class satisfying

```math
\sum_{k\ge1}\frac{k|f(k)|}{k(k+1)}<\infty.
```

Periodic residue generators do not satisfy this test condition. Therefore the
fixed Gram-source limit is not silently discharged. The missing formal steps
are the logarithmic Möbius sum tending to -1, the centered periodic Abel identity,
and divisor-dominated passage to the limit. The logarithmic Möbius theorem is
classical, not an open arithmetic conjecture; NIST DLMF 27.11.15 records it.

## 7. Remaining classical imports and the RH obstruction

Burnol's Theorem 1.2 is a projection product for the continuous all-parameter
Nyman--Beurling space. Applying it to the integer-step projection requires the
appropriate representation theorem; the integer membership criterion alone
does not identify the two projection norms. The Beurling--Lax/inner--outer
argument remains unformalized in this local chain.

The BSY identity still needs global integrability and boundary passage. Local
logarithmic integrability and radial normalization are not the full theorem.
The local Báez-Duarte converse still needs its RH-dependent approximation
argument. None of these statements was inserted as an axiom.

The compact outstanding arithmetic statement remains r(1)<=0. The existing
two-sided relation between r(1) and residual energy then forces r=0 and RH.
This continuation does not determine that sign, prove a weighted minimum tends
to zero below u=2, bound N T_N cofinally, or prove actual residual regularity.

## 8. Further mathematical research: the exact limiting Riesz energy

A separate written proof establishes

```math
\|Q_N\|_P^2\longrightarrow\sum_{n\ge1}\frac{\mu(n)^2}{n^2}=\frac{15}{\pi^2}.
```

This full limit is **not yet Lean-verified**. The complete proof is preserved in
`ReciprocalChargeNormLimit20260924.md`, with exact quotient-window separation
and the signed mixed term retained. It is a concrete next unconditional
formalization target. No novelty claim is made. It quantifies persistent energy
in the weak-zero representing vectors; it does not prove RH. Wolfram values at
N=10,100,1000,10000 were approximately 1.42462585, 1.49167650, 1.51897350,
1.52106211, compared with 15/pi^2 approximately 1.51981775. These computations
are corroboration only.

## 9. Verification and continuation

Lean development was parallel; verification submissions were serialized in one
isolated workspace. A first 90-second import check timed out; an import-free
test succeeded, and subsequent full proof batches returned actionable compiler
diagnostics. Timeouts were not treated as mathematical refutations.

All persisted Lean sources prohibit `sorry`, `admit`, project-local axioms, and
unsafe declarations. Principal axiom checks must report only `propext`,
`Classical.choice`, and `Quot.sound`. A successful snippet checks its exact
statements; final repository publication separately requires the changed-module
and reverse-dependency checkpoint.

Next concrete work: formalize the remaining classical logarithmic Möbius mean
and periodic source-decay argument; develop a quantitative estimate for the
signed mixed sum or the independently optimized weighted errors. The explicit
reciprocal-charge norm bounds can support further convergence analysis but
do not themselves resolve either arithmetic target.

Primary sources reviewed:

- Balazard, Propositions 5--7: https://arxiv.org/pdf/1812.04309
- Burnol, Theorems 1.2--1.3 and Section 2: https://arxiv.org/pdf/math/9910055
- Báez-Duarte, Theorem 1.1 and its proof: https://arxiv.org/pdf/math/0205003
- Manzur--Noor--Quintero: https://arxiv.org/abs/2606.16097
- Classical logarithmic Möbius limit: https://dlmf.nist.gov/27.11.E15

Wolfram independently confirmed the finite Schur algebra and exact cell integral.
Those computations supplement, and do not replace, Lean verification.
