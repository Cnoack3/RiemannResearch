# Signed sources: exact dyadic accounting and a masked RH criterion

Date: 14 November 2026.
Base commit: `485da6cdff8a886556631afa26fe2e387d6e3462`.
Retained workspace: `ws_FORguE7ZeEWRBMEHezcT0XdjWF855Bob`.

This continues `THEOREM_CATALOG_SIGNED_HEAD_CRITERION_20261114.md`.
The earlier continuation is already published at the base commit.
**The new arithmetic lower bound is still open; RH has not been proved.**
The user has authorized committing and pushing this continuation, with standing
authorization to publish future verified Lean research updates automatically.
Publication uses the managed server checkpoint; the arithmetic status is unchanged.

## 1. Exact objects and signed accounting

Use the existing actual two-seed Pareto projections, without identifying them
with a full-conductor Q residual:
\[
f_M=P_{V_M}\mathbf1,\quad r_M=\mathbf1-f_M,\quad
E_M=\|r_M\|^2,\quad G_M=E_M-E_{2M}.
\]
For every integer \(p\ge1\), set
\[
I_{M,p}=f_{\lfloor2M/p\rfloor}-f_{\lfloor M/p\rfloor},\quad
u_{M,p}=D_p I_{M,p},\quad
s_{M,p}=\langle r_M,u_{M,p}\rangle.
\]
The new exact pairing identity is
\[
s_{M,p}=\langle I_{M,1},u_{M,p}\rangle.
\]
This follows because \(u_{M,p}\in V_{2M}\) and \(r_{2M}\perp V_{2M}\).
Consequently the complete signed energy identity is
\[
\|I_{M,1}-u_{M,p}\|^2
=G_M+p\bigl(E_{\lfloor M/p\rfloor}
             -E_{\lfloor2M/p\rfloor}\bigr)-2s_{M,p}.
\]
The squared mismatch is retained; no sign assumption is made on the source.

Let \(M_j=2^{J+j}\), and define the exact endpoint differences
\[
\Delta_N=E_{M_0}-E_{M_N},\qquad
\Delta_{p,N}=E_{\lfloor M_0/p\rfloor}
              -E_{\lfloor M_N/p\rfloor}.
\]
Lean verifies
\[
\sum_{j<N}G_{M_j}=\Delta_N,\qquad
\sum_{j<N}T_{M_j}=2\Delta_{2,N}+3\Delta_{3,N},
\]
and, with every signed term retained,
\[
2\sum_{j<N}s_{M_j,p}
=\Delta_N+p\Delta_{p,N}
 -\sum_{j<N}\|I_{M_j,1}-u_{M_j,p}\|^2.
\]

## 2. Unconditional summability

Cauchy--Schwarz and the arithmetic--geometric mean inequality give
\[
\sum_{j<N}|s_{M_j,p}|
\le \frac{\Delta_N+p\Delta_{p,N}}2.
\]
Since every endpoint energy is nonnegative, this proves
\[
\sum_jG_{M_j}<\infty,\quad
\sum_jT_{M_j}<\infty,\quad
\sum_j|s_{M_j,p}|<\infty
\quad\text{for every fixed }p\ge1.
\]
In particular,
\[
\sum_j S_{M_j}<\infty.
\]
For *every* cutoff sequence \(K_j\), the existing Cauchy magnitudes and
squared two-source certificates also satisfy
\[
\sum_j m^{\rm CS}_{M_j,p,K_j}<\infty,\qquad
\sum_j J^{\rm CS}_{M_j,K_j}<\infty.
\]


Even trace normalization alone remains summable (zero-trace terms are zero):
\[
\sum_j\frac{S_{M_j}}{T_{M_j}}<\infty,\qquad
\sum_j\frac{J^{\rm CS}_{M_j,K_j}}{T_{M_j}}<\infty.
\]
The proof is the unconditional, zero-trace-safe comparison
\(S_M/T_M\le G_M\). Thus the additional division by \(E_M\) is
essential in the normalized-divergence criterion below.

These are unconditional results for the actual residuals. They do not
refute the previous normalized logarithmic target: summability of a raw
numerator is compatible with divergence after division by a shrinking
energy scale. They rule out using raw source divergence as that target.

## 3. Normalized detection, including zero trace

Define
\[
q_M=\begin{cases}
 S_M/(E_MT_M),&T_M>0,\\
 0,&T_M=0,
\end{cases}
\qquad
q^{\rm CS}_{M,K}=\begin{cases}
 J^{\rm CS}_{M,K}/(E_MT_M),&T_M>0,\\
 0,&T_M=0.
\end{cases}
\]
The Lean definitions use real division, whose zero-denominator convention
gives precisely this extension because \(E_M>0\) and \(T_M\ge0\).
The existing zero-trace theorem also forces both raw source columns to vanish.

The following estimates require **no separate positivity hypothesis**:
\[
0\le q^{\rm CS}_{M,K}\le q_M\le G_M/E_M.
\]
Together with the exact residual product recurrence, Lean proves
\[
\neg\operatorname{Summable}(j\mapsto q_{M_j})
\ \Longrightarrow\ \mathrm{RH},
\]
and the same implication for \(q^{\rm CS}_{M_j,K_j}\).

These are conditional research reductions. No theorem in this continuation
provides the required normalized divergence.

## 4. Detection on selected stages suffices

Let \(A\subseteq\mathbb N\), \(a_j\ge0\), and assume
\[
\sum_{j\in A}a_j=\infty.
\]
Only at stages \(j\in A\), require
\[
T_{M_j}>0,\qquad
a_jE_{M_j}T_{M_j}\le J^{\rm CS}_{M_j,K_j}.
\]
Then RH follows. The formal nonsummability hypothesis is
`¬ Summable (good.indicator a)`.

There is no trace-positivity or certificate hypothesis at stages outside
\(A\). Thus infinitely many failed or zero-trace stages are allowed.
A merely infinite or cofinal set is insufficient; its chosen weights must
have divergent sum. For harmonic weights this means a divergent harmonic
subseries over the selected stages.

## 5. Saved declarations

All names lie in `RiemannResearch.RH.Pareto.CoupledResidual`.

| File | Principal declarations | Classification |
|---|---|---|
| `RH/CoupledResidualDyadicAccounting.lean` | `source_eq_inner_innovation`, `innovation_transport_norm_sub_sq`, `dyadic_signed_source_sum` | Unconditional exact signed identities |
| Same file | `dyadic_priorGain_sum`, `dyadic_gain_sum`, `dyadic_trace_sum` | Unconditional exact endpoint balances |
| Same file | `summable_abs_dyadic_source`, `dyadic_abs_source_sum_le`, `summable_dyadic_trace`, `summable_dyadic_sourceSquare`, `summable_dyadic_cauchyMagnitude`, `summable_dyadic_cauchySquare`, `summable_dyadic_sourceSquare_div_trace`, `summable_dyadic_cauchySquare_div_trace` | Unconditional summability and bounds |
| `RH/DyadicGainEndpoint.lean` (existing, reused) | `dyadic_distance_recurrence`, `dyadic_distance_tendsto_zero_iff`, `riemannHypothesis_of_dyadic_gain_divergence` | Established recurrence and RH consumer |
| `RH/CoupledResidualHeadCriterion.lean` | `normalizedSourceSquare`, `normalizedCauchySquare`, `normalizedSourceSquare_le_relativeGain` | Zero-trace definitions and unconditional comparison |
| Same criterion file | `riemannHypothesis_of_nonsummable_normalizedSource`, `riemannHypothesis_of_nonsummable_normalizedCauchy`, `riemannHypothesis_of_masked_cauchySchedule` | Conditional RH reductions; normalized divergence remains open |

There are 28 new public theorems and two definitions. The accounting module
is exported from `RiemannResearch.lean`.

## 6. Next substantive task

Prove nonsummability of the *actual* normalized source squares, or find
selected stages with a provably divergent weight sum and the certified lower
bound from Section 4. This weakens the need to prove positive trace at every
late stage. It does not supply an arithmetic detection estimate.

`CompleteSourceLogBound` remains open and is still a sufficient stronger
target. Two-probe blindness remains possible. The new upper summability
bounds, exact telescoping, finite tables, and the former fixed-stage cutoff
existence theorem do not discharge this obligation.

## 7. Verification and publication

The receipts below establish the pre-publication verification. The user has
explicitly authorized automatic publication of verified repository work; this
standing instruction is recorded in root AGENTS.md. Resume the retained
workspace above and use the managed checkpoint with push enabled. Any
integration with newer main must pass server validation before publication.
The terminal checkpoint result is the authoritative publication receipt.

Suggested commit title:

> Prove dyadic signed-source accounting and masked RH detection criteria


### Saved-source and assumption audit

- State: succeeded, compiling the two saved Lean modules and their transitive imports.
- Job: `job_QV6o9uE7Nlzy_aGjjmfcluqLlKtOeKEa`.
- Backend: Bazel with BuildBuddy.
- Server verification duration: 52.190 seconds, excluding queue and polling.
- Receipt: https://app.buildbuddy.io/invocation/7e198bd0-6756-44f6-914a-b2e8255968a3 .
- All 28 new public theorems passed guarded axiom inventories exactly
  `[propext, Classical.choice, Quot.sound]`.
- This inventory does not discharge hypotheses in conditional theorem types.
- No proof placeholders, project-specific axioms, or unsafe declarations were added.
- The recurrence and endpoint equivalence are reused from
  `RH/DyadicGainEndpoint.lean`, which is unchanged.

### Full-project acceptance

- State: succeeded.
- Scope: `bazel build --config=buildbuddy //:RiemannResearch`, including
  both saved Lean modules, all root exports, and all existing project packages.
- Job: `job_1TljpCAlEPmopfkU556-7n5srOFjtTYV`.
- Server-reported full build duration: 178.706 seconds, excluding polling.
- Receipt: https://app.buildbuddy.io/invocation/97a9456d-a693-44e6-bdc5-9abec0f0ca39 .
- The accepted tree is based on `485da6cdff8a886556631afa26fe2e387d6e3462`.
- Subsequent changes add documentation receipts only; Lean source is unchanged.
- Six repository files comprise this continuation: the new accounting module,
  the extended criterion module, their root export, this new catalog, the
  continuation link in the prior catalog, and the standing authorization in AGENTS.md.
- These are pre-publication receipts. The user subsequently authorized the
  managed checkpoint with push enabled. No Site update is requested.
