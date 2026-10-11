# Actual prime coefficient sensors and ordinate lag phases: Lean continuation
Prepared: 2026-10-11

Source: the user-provided
`RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11.md`.
The initial working base was `0f4dae4e7eaa8766ec5346fe1eddd03c707036b3`.
The additions are integrated onto `b56e06ee6bbeecb11d56166b8c5adabb4a9124a1`,
preserving its aggregate imports and existing catalog entries.

## Scope and status

This continuation extends the actual Pareto two-seed development. It does not
assume RH, prove a quantitative actual residual-gain provider, or declare
unproved mathematical claims as axioms. The historical signed cumulative
kernel, Fourier-energy, zero-jet and dyadic endpoint modules remain the
existing foundations; they have not been replaced by a diagonal Haar norm.

The six new modules contain 48 public supporting theorems. Arithmetic
coordinates, finite-family obstruction, and finite joint coefficient
stability are unconditional. The RH consumers require an explicit
nonsummable actual gain or actual prime coefficient-mass provider. The lag
phase limits expose endpoint counting control and marginal-limit assumptions
in their types.

| New module | Public theorems | Main declaration or role |
|---|---:|---|
| `RH/TwoSeedPrimeCoefficients.lean` | 5 | `prime_coefficient_error_identity`, `prime_coefficient_sum_tendsto` |
| `RH/ResidualCutoffSchedule.lean` | 7 | `cutoff_distance_tendsto_zero_iff`, `riemannHypothesis_of_cutoff_gain_divergence` |
| `RH/CombinedPrimeSensors.lean` | 12 | `completedBudget_prime_family_error_identity`, `actual_distance_prime_family_lower_bound` |
| `RH/PrimeCoefficientStability.lean` | 8 | `primeNormalizedSynthesis_norm_sq`, `legal_primeCoefficient_l2_bound` |
| `RH/PrimeCoefficientGain.lean` | 3 | `primeFitEnergy_le_distance_drop`, `riemannHypothesis_of_primeFitEnergy_minorant` |
| `Analysis/OrdinateLagPhase.lean` | 13 | `lag_gap_sum_identity`, `phase_selfCorrelationMean_tendsto_one` |

## 1. Exact correlated prime obstruction

Write
\[
\ell_q(f)=f(q)-f(q-1)-f(1),\qquad k_q=\ell_q^*.
\]
For primes greater than 3 the actual Pareto Riesz Gram is
\[
\langle k_q,k_r\rangle=2+2q^2\mathbf1_{q=r}.
\]
The common physical coordinate 1 contributes the off-diagonal term 2; it
must not be discarded.

For any finite prime set \(P\), all of whose members exceed
\(\max(M,3)\), put
\[
s_P=\sum_{q\in P}q^{-2},\qquad
u_P=\sum_{q\in P}q^{-2}k_q.
\]
For every \(F\) in the completed fixed budget plus all seed contrasts,
\[
\boxed{\|1-F\|^2=\frac{s_P}{2(1+s_P)}
+\left\|1-F+\frac{u_P}{2(1+s_P)}\right\|^2.}
\]
In particular \(D_M\ge s_P/[2(1+s_P)]\). This combines all tested
directions before squaring. Its bound depends on the moving prime set, and
does not give a positive limiting residual or a lower bound on
\(D_M-D_{2M}\).

## 2. Necessary coefficient behavior, with a joint bound

For an arbitrary finite legal representation, let \(A_q\) be the sum of
the two seed coefficients at index \(q\), with absent coefficients zero.
Dependence of the generator family creates no ambiguity in this sum at a
prime, because \(\ell_q(F)=qA_q\).

The full energy has the exact one-coordinate split
\[
\|1-F\|^2=\frac{(qA_q+1)^2}{2(q^2+1)}
+\left\|1-F+\frac{qA_q+1}{2(q^2+1)}k_q\right\|^2.
\]
Thus \(F_n\to1\) implies \(A_{n,q}\to-1/q\) for every fixed prime
\(q>3\).

The finite joint strengthening is
\[
\boxed{\sum_{q\in P}|A_q+1/q|^2
\le2(1+s_P)\|1-F\|^2,}
\]
for every finite set of primes greater than 3. Its underlying synthesis
identity retains the complete signed cross charge:
\[
\left\|\sum_{q\in P}\frac{c_q}{q}k_q\right\|^2
=2\sum_{q\in P}c_q^2+2\left(\sum_{q\in P}\frac{c_q}{q}\right)^2.
\]
The module proves finite observation bounds. It does not separately construct
the infinite-prime observation operator or claim that prime coordinates
alone separate the entire Hilbert space.

## 3. A concrete new arithmetic gain target

Let \(A\le B\), \(F_B\) be the actual full-budget orthogonal
projection of 1, and \(P\) any finite set of primes exceeding
\(\max(A,3)\). Define the invariant actual coefficient energy
\[
E_{P,B}=\sum_{q\in P}\left(\frac{\ell_q(F_B)}q\right)^2.
\]
At a prime this is the squared sum of its two seed coefficients, independently
of the chosen finite representation. The projection is the full Pareto
optimizer before the prime restriction.

The actual prime-sensor estimate and exact nested projection identity give
\[
\boxed{E_{P,B}\le2(1+s_P)(D_A-D_B).}
\]
This is a direct lower gain test, unlike the residual energy floor in
Section 1. A prime beyond \(B\) contributes zero, so useful observation
sets lie in the newly visible prime window.

For any nondecreasing cutoff schedule \(M_n\), write
\[
\delta_n=\frac{D_{M_n}-D_{M_{n+1}}}{D_{M_n}}.
\]
The exact product and endpoint are
\[
D_{M_N}=D_{M_0}\prod_{n<N}(1-\delta_n),\qquad
D_{M_n}\to0\ \Longleftrightarrow\ \neg\operatorname{Summable}(\delta).
\]
Consequently it suffices to provide finite prime sets \(P_n\) above
\(\max(M_n,3)\) and a nonnegative nonsummable schedule \(a_n\) satisfying
\[
\boxed{a_n\le
\frac{E_{P_n,M_{n+1}}}{2(1+s_{P_n})D_{M_n}}.}
\]
The theorem `riemannHypothesis_of_primeFitEnergy_minorant` proves that this
provider implies RH. The provider itself remains **Open**. This target
retains actual optimizer coefficients and old-space reoptimization, and
allows variable or sparse enlargements without a dyadic cutoff constraint.

## 4. Exact lagged phase control

For any nondecreasing real sequence \(\gamma_j\) and natural lag
\(\ell\), the complete boundary-strip identity is
\[
\sum_{j<J}(\gamma_{j+\ell}-\gamma_j)
=\sum_{i<\ell}(\gamma_{J+i}-\gamma_i).
\]
For \(J>0\) it yields
\[
\frac1J\sum_{j<J}|e^{iu\gamma_{j+\ell}}-e^{iu\gamma_j}|
\le |u|\frac{\ell(\gamma_{J+\ell}-\gamma_0)}J.
\]
The module permits moving lags and proves that vanishing endpoint control
transfers any same-height correlation limit to the lagged correlation.
Same-frequency correlation tends to 1 under endpoint control alone,
without a marginal equidistribution premise.

The actual-zero multiplicity-counted sorted enumeration, its global
counting asymptotic, and the height-cutoff-to-prefix marginal bridge are not
instantiated here. In particular the paper consequence for sublogarithmic
lags is not advertised as a newly checked actual-zero theorem. These are
unscaled phases; no claim about microscopic gap independence follows.

## 5. Remaining obligations

| Obligation | Status |
|---|---|
| Actual nonsummable residual relative-gain provider | Open |
| Actual prime-fit-energy nonsummable minorant in Section 3 | Open |
| Actual legal normalized witnesses with divergent reciprocal costs | Open; existing conditional consumers retained |
| Uniform growing-support Landau and zero-density providers in the source note | Not completed here |
| Actual-zero instantiation of the lag endpoint and marginal inputs | Not completed here |
| RH-to-two-seed density | Existing explicit classical density-from-RH provider remains required |

Neither a prime sensor lower floor, necessary coefficient convergence,
fixed-test Haar convergence nor the lagged phase identities discharges the
actual coefficient-mass lower schedule. No unsupported novelty claim is made.

## Verification

Exact-module import and axiom-audit job
`job_tuoD2lCM0tuG4R0nzrxDxe0gR6sTRVEI` completed successfully on the user's
Lean server with `verified=true`. It compiled all six final modules and
issued `#print axioms` for all 48 public supporting theorems.
Supplemental audit `job_wWB01nzr67W3V-l42MBIPrD-37PmlSZ6` also completed
with `verified=true` and displayed all initially cropped reports. Across
both outputs, every new public theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. Substantive hypotheses in the
conditional theorem types remain hypotheses, not discharged providers.

The project source audit and affected-module publication validation are
performed by the publication checkpoint. A queued checkpoint is not a
successful publication; its terminal result is reported in the task's final
response. No fresh full-repository build is claimed here.
