# Option 4: Möbius coefficient identification in Lean

Date: 2026-09-20.
Source: the user-provided **RH_Eight_Ranked_Research_Candidates_2026-09-20.pdf**,
Candidate 4, Section 6.
Starting published snapshot: a1ce7b06ae717ddaa73103035611a2df0d4ce9d2.

Module: `RiemannResearch/RH/MobiusCoefficientDefect.lean`.
Application namespace: `RiemannResearch.RH.Pareto.CoefficientStabilization`.

## Mathematical status

**RH has not been proved.** This continuation proves new conditional consumers
and necessary obstructions for the actual coefficient-identification route.
The missing arithmetic provider is not replaced by an axiom or a proof placeholder.

Use physical conductors \(d\ge2\), the full Pareto Hilbert space with
\(w_n=1/(n(n+1))\), and \(g_d(n)=(n\bmod d)/d\). Let
\(S=\overline{\operatorname{span}}\{g_d:d\ge2\}\),
\(r=1-P_S1\), and
\[
 b_d=c_{\infty,d}+\mu(d),\qquad
 B_N=\sum_{d=2}^{N+1} b_dg_d.
\]
Lean index \(i\) denotes conductor \(i+2\).
The existing absolutely convergent mode series gives
\(c_{\infty,d}=\sum_j\alpha_j a_{j,d}\) without evaluating its sum.
The exact continuous coefficient relation is \(C_d(r)=-b_d\).

## Established extension 1: finitely many exceptions do not matter

If \(c_{\infty,d}=-\mu(d)\) for every sufficiently large \(d\), then \(r=0\)
and the existing Mellin bridge proves Mathlib's `RiemannHypothesis`.

Proof: the residual then has only finitely many nonzero residue coefficients.
Synthesize the corresponding finite combination of \(g_d\). Joint injectivity
of the continuous Möbius coefficient functionals identifies it with \(r\).
Thus \(r\in S\cap S^\perp=\{0\}\).

Declarations:
- `riemannHypothesis_of_eventual_mobius`.
- `riemannHypothesis_of_eventual_mode_mobius_tsum`, in the exact
  Gram-Schmidt series notation of the candidate.
- `coefficient_defects_unbounded_of_not_rh`: if RH is false, erroneous
  coefficients occur beyond every conductor bound.

This does **not** say that checking a finite initial segment proves RH.

## Established extension 2: a cofinal signed Gram bound suffices

The precise new arithmetic target is
\[
 \exists C\in\mathbb R\ \forall N_0\ \exists N\ge N_0:
 \quad
 \sum_{d,e=2}^{N+1} b_db_e\langle g_d,g_e\rangle\le C.
\]
The left side is exactly \(\|B_N\|^2\), including every signed mixed term and
the infinite spatial tails in each Gram entry.

`riemannHypothesis_of_cofinal_defect_gram_bound` proves that this target
implies RH. It requires boundedness only along a cofinal subsequence, not
convergence or vanishing of the finite energies.

The proof establishes totality of the Möbius Riesz test vectors in the
whole Hilbert space. This is a statement about **dual test vectors**, not
an assumption that the residue atoms have dense span.
Every fixed coefficient of \(-B_N\) eventually equals the coefficient of \(r\).
Along a bounded subsequence, convergence on this total family extends to
weak convergence against every Hilbert vector. But all \(B_N\) lie in \(S\)
and pair to zero with \(r\). Their putative weak limit \(-r\) then forces
\(\|r\|^2=0\).

General support:
- `RiemannResearch.RH.Pareto.mobiusRiesz_total`.
- `coefficientCLM_ext` and `coefficient_tsum_reconstruction`.
- `inner_tendsto_of_bounded_coefficients`.
- `zero_of_cofinally_bounded_coefficientPartialSum`.

## Established extension 3: a sharp qualitative obstruction under not RH

`defectPartialSum_norm_tendsto_of_not_rh` proves
\[
 \neg\mathrm{RH}\quad\Longrightarrow\quad \|B_N\|\longrightarrow+\infty.
\]
This is divergence along the full sequence, not merely the absence of a
known uniform estimate. Monotonicity of the finite energies is not asserted.

The general theorem `coefficientPartialSum_norm_tendsto` applies to
every nonzero vector in \(S^\perp\).

## Established extension 4: explicit scalar regularity suffices

The atom bound
\[
 \|g_d\|^2\le\langle g_d,1\rangle=\frac{\log d}{d}
\]
follows from \(0\le g_d\le1\). Consequently,
\[
 \sum_{d\ge2}|b_d|\sqrt{\frac{\log d}{d}}<\infty
 \quad\Longrightarrow\quad r=0
 \quad\Longrightarrow\quad\mathrm{RH}.
\]
This is `riemannHypothesis_of_summable_weighted_defect`.
It is a sufficient scalar condition; necessity of this particular estimate
is not used in the proof.

## Exact remaining obligation and unsuccessful shortcut

**Open:** prove at least one arithmetic provider, for the actual
\(c_{\infty,d}\):
1. eventual Möbius identification;
2. the cofinal full signed Gram bound above;
3. weighted absolute summability of the defect.

Each would force \(b_d=0\) for all \(d\ge2\).
The cofinal bound is itself equivalent to zero residual, since zero residual
makes every defect zero. It is a rigorous alternate target, not independent
evidence that saturation has been established.

The attempted shortcut from absolute convergence fails at a specific
exchange: the known result controls \(\sum_j|\alpha_ja_{j,d}|\) for each
**fixed** \(d\). It supplies no uniform control as \(d\) varies, and hence
does not justify summing the defect residue vectors or bounding their joint
Gram energy. No multiplicativity of \(b_d\) has been proved; primes alone
are not substituted for all conductors.

The next bounded research task is an arithmetic estimate for the displayed
Gram expression with the exact cofactor coefficients. Its mixed terms must
be retained. A bound that assumes the coefficients already equal
\(-\mu(d)\), density of the residue span, or zero residual would be circular.

## Verification

The development was checked in serialized Lean snippets. The key RH
consumers and the non-RH divergence theorem passed explicit axiom inspection
with only `propext`, `Classical.choice`, and `Quot.sound`.
The final project acceptance and publication are performed by the workspace
checkpoint; its commit and outcome are reported in the accompanying response.
