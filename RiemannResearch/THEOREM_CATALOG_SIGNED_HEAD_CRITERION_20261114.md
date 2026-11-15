# Signed-head detection: sharper tails and the RH criterion

Continuation: [exact dyadic source accounting and masked RH detection](THEOREM_CATALOG_SIGNED_SOURCE_DYADIC_20261114.md).
The continuation proves unconditional summability and permits zero-trace stages;
the normalized arithmetic divergence remains open.

Date: 14 November 2026.
Base commit: `cf60e52ec04283928cfd5e335da151632237ad93`.
Retained workspace: `ws_FORguE7ZeEWRBMEHezcT0XdjWF855Bob`.

This continues `THEOREM_CATALOG_SIGNED_HEAD_DETECTION_20261114.md`.
The original results are published at the base commit. The present continuation
adds unconditional estimates and conditional RH reductions. **The arithmetic
lower bound remains open; RH has not been proved.** The user explicitly approved committing and pushing these six files.
Publication is gated by the managed server checkpoint and its full-project
verification, including any integration with newer main.

## 1. Actual objects and the exact signed identity

Keep the existing two-seed Pareto projection sequence:
\[
r_M=\mathbf1-P_{V_M}\mathbf1,\qquad E_M=\|r_M\|^2,\qquad
G_M=E_M-E_{2M}.
\]
For \(p\in\{2,3\}\), let
\[
B=\lfloor2M/p\rfloor,\quad v_{M,p}=D_pr_B,\quad
s_{M,p}=A_{M,p}-\langle r_M,v_{M,p}\rangle,
\quad S_M=s_{M,2}^2+s_{M,3}^2.
\]
The exact floor, zero anchoring, complete energies, and signed correlations
are the existing repository objects. \(T_M\) is the sum of the squared norms
of the two transported innovation columns, as in the earlier catalog.

Let \(Q_K f\) be the shifted Hilbert-coordinate tail beyond physical site \(K\).
The new generic identity is
\[
\langle f,g\rangle
=\sum_{n=1}^{K}\frac{f(n)g(n)}{n(n+1)}
 +\langle Q_Kf,Q_Kg\rangle,
\]
where \(f(n),g(n)\) denote physical coordinates in this display.

Define the finite center and tail radius
\[
c_{M,p,K}
=A_{M,p}-\sum_{n=1}^{K}
 \frac{r_M(n)\,p\,r_B(\lfloor n/p\rfloor)}{n(n+1)},
\qquad
R_{M,p,K}=\|Q_Kr_M\|\,\|Q_Kv_{M,p}\|.
\]
Then the primary, exact signed statement is
\[
s_{M,p}=c_{M,p,K}
-\langle Q_Kr_M,Q_Kv_{M,p}\rangle.
\]
No remainder is dropped in this equality.

## 2. A sharper finite-head interval

Cauchy--Schwarz applied only to the tails gives
\[
c_{M,p,K}-R_{M,p,K}\le s_{M,p}
 \le c_{M,p,K}+R_{M,p,K}.
\]
Its squared radius is exactly
\[
R_{M,p,K}^2=
\bigl(E_M-F_K(r_M)\bigr)
\bigl(pE_B-F_K(v_{M,p})\bigr),
\quad
F_K(f)=\sum_{n=1}^{K}\frac{f(n)^2}{n(n+1)}.
\]
Thus the radius can be determined from complete energies and finite head
observations. This is not a replacement of complete energy by a finite sum.

The original sum/difference interval has the same center and radius
\[
\frac{\|Q_Kr_M\|^2+\|Q_Kv_{M,p}\|^2}{2}.
\]
The new radius is no larger by the arithmetic--geometric mean inequality.

Set
\[
m^{\rm CS}_{M,p,K}=\max(0,|c_{M,p,K}|-R_{M,p,K}),\qquad
J^{\rm CS}_{M,K}=\sum_{p=2,3}(m^{\rm CS}_{M,p,K})^2.
\]
The checked inequalities are
\[
m_{M,p,K}\le m^{\rm CS}_{M,p,K}\le |s_{M,p}|,\qquad
|s_{M,p}|-2R_{M,p,K}\le m^{\rm CS}_{M,p,K},
\]
and
\[
J_{M,K}\le J^{\rm CS}_{M,K}\le S_M,\qquad
J^{\rm CS}_{M,K}\le T_MG_M,\qquad
J^{\rm CS}_{M,K}\longrightarrow S_M
\quad(K\to\infty,\ M\text{ fixed}).
\]
This strengthens the original finite sum/difference certificate. The
separate coarse certificate \(H_M\) and its maximum with \(J_{M,K}\) remain
available unchanged.

## 3. Finite cutoffs do not require a uniform rate

For every real \(\theta<1\) and every \(M\), Lean proves
\[
\exists K,\qquad \theta S_M\le J_{M,K}.
\]
This includes \(S_M=0\). Classical choice also gives a single function
\(K:\mathbb N\to\mathbb N\) satisfying this at every budget. For the useful
interpretation take \(0<\theta<1\). Neither computability nor a uniform
upper bound on \(K(M)\) is asserted.

More precisely, for \(0<C<D\), \(L>1\),
\[
E_MT_M\le C\log(L)S_M
\quad\Longrightarrow\quad
\exists K,\ E_MT_M\le D\log(L)J_{M,K}.
\]
The proof chooses \(\theta=C/D\). Hence an arbitrarily small multiplicative
enlargement of the constant supplies the needed strict margin.

Using \(L=2M\), Lean proves the exact equivalence between these two
**open provider propositions**:

| Provider | Required statement |
|---|---|
| `CompleteSourceLogBound` | There exist \(C>0,M_0\) such that every \(M\ge M_0\), \(M\ge1\), satisfies \(T_M>0\) and \(E_MT_M\le C\log(2M)S_M\). |
| `FiniteHeadLogBound` | There exist \(D>0,M_0\) such that at every such \(M\), \(T_M>0\) and some finite \(K\) satisfies \(E_MT_M\le D\log(2M)\max(H_M,J_{M,K})\). |

The equivalence permits different constants. The forward finite-to-complete
direction keeps the constant; the reverse proof uses \(D=2C\), while the
stronger pointwise theorem permits every \(D>C\).

This closes the cutoff-existence portion of the route. It does not supply
the common arithmetic constant or eventual positivity of the trace.

## 4. Checked conditional implications to actual RH

Both provider propositions imply Mathlib's `RiemannHypothesis`.
The proof uses
\[
S_M\le T_MG_M,\qquad
E_M\le C\log(2M)G_M,
\]
then the established dyadic harmonic-loss and actual two-seed closure
theorems. No full-conductor Q residual is identified with this two-seed
Pareto residual.

There is also a more general checked criterion on the actual dyadic chain.
For \(M_j=2^{J+j}\), assume at **every** \(j\):
\[
T_{M_j}>0,\quad a_j\ge0,\quad
a_jE_{M_j}T_{M_j}\le J^{\rm CS}_{M_j,K_j},
\qquad \sum_j a_j=\infty.
\]
Then RH follows. The formal hypothesis is `¬ Summable a`.
The proof compares \(a_j\) with \(G_{M_j}/E_{M_j}\) and uses the exact
residual product recurrence. Nonsummability is an explicit input:
cofinality of some independently chosen scale does not replace it.

## 5. Files and principal declarations

All new names below except the first two lie in
`RiemannResearch.RH.Pareto.CoupledResidual`.

| File | Principal declarations | Status |
|---|---|---|
| `RH/ThresholdHilbertTail.lean` | `Pareto.hilbertTailShift_inner_sub_head`, `Pareto.hilbertTailShift_correlation_bound` | Unconditional |
| `RH/CoupledResidualCauchyHead.lean` | `source_tail_correlation_identity`, `sourceTailRadius_sq`, `source_cauchy_interval`, `finiteSourceMagnitude_le_cauchy`, `cauchySourceMagnitude_lower`, `cauchySourceSquare_le_trace_gain`, `cauchySourceSquare_tendsto` | Unconditional |
| `RH/CoupledResidualHeadCriterion.lean` | `exists_cutoffs_capture_sourceSquare`, `finite_head_bound_of_complete_source`, `finiteHeadLogBound_iff_completeSourceLogBound` | Unconditional structural results |
| Same criterion file | `riemannHypothesis_of_completeSourceLogBound`, `riemannHypothesis_of_finiteHeadLogBound`, `riemannHypothesis_of_cauchyHeadLogBound`, `riemannHypothesis_of_nonsummable_cauchyHead` | Conditional research reductions; arithmetic inputs open |

There are 29 new public theorems: 2 generic tail identities/bounds,
16 Cauchy-certificate theorems, and 11 cutoff/criterion theorems.
The three modules are exported from `RiemannResearch.lean`.

## 6. Remaining research obligation

The next substantive target is a provider of `CompleteSourceLogBound`,
or directly a nonsummable lower bound for the actual normalized Cauchy
certificates along the dyadic chain. A common constant must hold at every
sufficiently late stage. Finite tables, conditioning of the two-column Gram
matrix, positivity of total energy, and fixed-stage convergence do not
supply this.

Two-probe blindness remains a possible obstruction. A proof for the full
enlarged correction space could succeed even if these two sources fail
the logarithmic bound. The sharper tail interval improves certified
observation; it does not add missing correction directions.

## 7. Verification and publication boundary

The saved criterion file and all transitive imports passed Bazel with
BuildBuddy:
- Job: `job_ZF8mnoTHGIvfmgaGqNhO8F3fB6lZ201x`.
- Server verification: 57.716 seconds.
- Receipt: https://app.buildbuddy.io/invocation/74bd9393-f8c3-4216-8918-1735c2883f0b .

Guarded axiom inventories and full-project results are recorded below. The user has now explicitly approved committing and pushing this continuation.
Use the managed checkpoint with push enabled; any integration with newer main
must pass its server verification.

### Guarded assumption audit

Fifteen principal declarations passed exact guarded axiom inventories.
Each inventory is exactly `[propext, Classical.choice, Quot.sound]`.
No proof placeholders or project-specific axioms occur in the new source.
This audit does not discharge hypotheses in conditional theorem types.

- Job: `job_P3iTkH4reMzV0zmkbKO_3516gPJkNBf6`.
- Server verification: 23.555 seconds.
- Receipt: https://app.buildbuddy.io/invocation/e49131ef-92a6-45f6-b67b-594eeb23dd62 .

### Full-project acceptance

- Scope: `bazel build --config=buildbuddy //:RiemannResearch`, including
  all three new exports and the complete existing development.
- Terminal state: success.
- Job: `job_jfmpZij2J731njer3Qwt4Crn_zjsih78`.
- Server-reported build duration: 170.053 seconds.
- Receipt: https://app.buildbuddy.io/invocation/3281b928-b2d4-44b3-994b-1e4f04bf72f3 .
- Subsequent changes only add these documentation receipts; Lean source is
  unchanged after this successful check.
- The only changes are the three new Lean modules, their root exports, this
  new catalog, and the continuation link in the earlier catalog: six files.
- These are the pre-publication verification receipts. The user subsequently
  approved committing and pushing the six files; the terminal managed-checkpoint
  result is the authoritative publication receipt. No Site update is requested.

The focused file check and axiom audit durations above are server durations,
not total session wall time. The initial workspace reopen took about
2.7 seconds at the tool boundary; queue, transport, and polling time are
separate from the reported verification times.

### Resuming this work

Resume workspace `ws_FORguE7ZeEWRBMEHezcT0XdjWF855Bob`; do not start from
the older attachment's uncommitted baseline. The published base is
`cf60e52ec04283928cfd5e335da151632237ad93`. The pre-publication build is terminal.
The user approved the managed checkpoint; inspect its terminal publication result
before deciding whether an additional commit is needed.

The next research task is to prove `CompleteSourceLogBound`, or supply a
nonsummable lower schedule for the actual Cauchy certificates. Repeating
fixed-stage cutoff existence will not advance that remaining arithmetic task.

Publication was explicitly approved by the user. The managed checkpoint with
push enabled must verify any integrated source before publication.
Approved commit title:

> Sharpen signed-head tail certificates and prove conditional RH criteria
