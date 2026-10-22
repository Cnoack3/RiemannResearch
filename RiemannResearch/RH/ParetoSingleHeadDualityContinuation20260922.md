
## 14. One fixed head, residual positivity, and the infinite dual normal — 22 September 2026

This continuation adds three modules containing **34 verified theorem declarations**.
Verification and publication status is recorded at the end of this section.
The full infinite signed covariance is retained. No proof of RH is claimed.

### One fixed head is enough

Let \(e_N(j)=\mathbf1_{1\le j\le N}\), and keep the manuscript's actual
closed legal span \(S\), canonical projection residual \(r\), and capacities
\(\kappa_{N,M}\). For **each individual fixed integer \(N\ge1\)**, the new
geometric equivalences are

\[
\boxed{
S=H_P
\iff e_N\in S
\iff \kappa_{N,M}\longrightarrow+\infty\quad(M\to\infty)
\iff \sum_{j=0}^{L-1}\frac{\eta_{N,N+j}^2}{\sigma_{N,N+j}}
       \longrightarrow+\infty\quad(L\to\infty).
}
\]

In particular **N=1 alone suffices**. The earlier hypothesis demanding
divergence at every positive head is unnecessary. The denominators and
numerators here are exactly those constructed in Section 13.

The actual finite optimizer satisfies the exact distance identity

\[
\left\|F^{\mathrm{opt}}_{N,M}-e_N\right\|_P^2
=\kappa_{N,M}^{-1}.
\]

Thus capacity divergence produces full-norm convergence to the head
indicator. Conversely, continuous head repair approximates that indicator
by finite legal exact-head vectors whenever it lies in S. The exact
Schur telescope then gives the gain-series equivalence.

`RH/CanonicalMobiusFixedHeadLimit.lean` contains
`canonicalWindow_optimizer_distance_sq`,
`indicator_mem_iff_windowCapacity_diverges`,
`density_iff_single_windowCapacity_diverges`, and
`density_iff_single_windowGain_diverges`.
Its `riemannHypothesis_of_single_windowGain_divergence` concludes actual
Mathlib `RiemannHypothesis` from the displayed divergence at one N.
**That divergence remains an open research hypothesis.** As before, the
unformalized converse from RH to legal density is not inserted into any theorem.

### Exact dilation identity and positive pairing at every head

Put \(B=N+1\). In the project's normalization,
\(D_B f(j)=B f(\lfloor j/B\rfloor)\), with \(f(0)=0\), and
\(\|D_Bf\|_P=\sqrt B\,\|f\|_P\). The legal closure is invariant under D_B.
The new finite-head identity is

\[
e_N=\mathbf1-B^{-1}D_B\mathbf1.
\]

Write \(\delta=\|r\|_P^2\) and
\(h_N=\langle r,e_N\rangle_P=\sum_{j\le N}w_jr(j)\).
Orthogonality and dilation invariance give the exact equality

\[
h_N=\delta-B^{-1}\langle r,D_Br\rangle_P.
\]

Cauchy–Schwarz yields the unconditional two-sided bound

\[
\boxed{
(1-B^{-1/2})\delta\le h_N\le(1+B^{-1/2})\delta.
}
\]

Consequently, if \(r\ne0\), then \(h_N>0\) at **every positive head**,
not merely for all sufficiently large N. If \(e_N\in S\), orthogonality
forces \(h_N=0\), hence \(r=0\), and the existing closure theorem gives
density. This proves the single-head membership equivalence above without
an unproved arithmetic premise.

Combining this with \(\kappa h_N^2\le T_N\), where
\(T_N=\sum_{j>N}w_jr(j)^2\), strengthens the earlier eventual bound to

\[
\boxed{
\kappa(N,k)\le
\frac{T_N}{\delta^2(1-1/\sqrt{N+1})^2}
\qquad(N\ge1,\ \delta>0).
}
\]

It holds for **every** nonempty finite indexed canonical family with
positive indices \(k_i\ge N\), including repetitions. Lean states the
same bound with numerator \((N+1)^2T_N\) and denominator
\(((N+1-\sqrt{N+1})\delta)^2\).

These declarations are in `RH/ParetoFiniteHeadDilation.lean`:
`finiteHeadIndicator_eq_dilation_difference`,
`finiteHead_residual_inner_identity`, `finiteHead_residual_inner_bounds`,
`finiteHeadIndicator_mem_iff_density`, `residualHeadPairing_pos`, and
`capacity_fixed_head_residual_bound`.

### The infinite dual problem has an actual attained solution when capacity is bounded

Fix N≥1 and write \(v_k=u_k\mathbf1_{j>N}\). Let \(Z_{N,M}\) be the actual
finite normal vector from Section 12. The new exact duality is

\[
\boxed{
\sup_M\kappa_{N,M}<\infty
\iff
\exists Z\in H_P:\ \langle v_k,Z\rangle_P=1\quad\text{for every }k\ge N.
}
\]

Here the Hilbert vector Z is in the shifted tail realization used by Lean.
It is not a coefficient sequence with an assumed inverse-Gram bound.
Every common normal witness W satisfies the finite completion

\[
\|W\|_P^2=\kappa_{N,M}+\|W-Z_{N,M}\|_P^2.
\]

Under bounded capacity the previously verified exact increment identity
makes \(Z_{N,M}\) a Cauchy sequence. It has a strong Hilbert limit \(Z_N^*\)
solving every infinite normal equation, and

\[
\boxed{
\kappa_{N,M}\longrightarrow\|Z_N^*\|_P^2
=\sup_M\kappa_{N,M},\qquad
\|Z_N^*-Z_{N,M}\|_P^2
=\|Z_N^*\|_P^2-\kappa_{N,M}.
}
\]

For every other witness W,

\[
\boxed{\|W\|_P^2=\|Z_N^*\|_P^2+\|W-Z_N^*\|_P^2.}
\]

Thus the infinite normal problem has an attained minimum energy and a
unique minimizing vector. Its finite coefficients need not be discussed
or controlled to establish this strong convergence.

`RH/CanonicalMobiusWindowDuality.lean` provides
`windowCapacity_bddAbove_iff_commonNormal`,
`exists_commonNormal_limit_of_capacity_bddAbove`,
`exists_minimum_commonNormal_of_capacity_bddAbove`,
`windowNormal_limit_energy_eq_iSup`,
`commonNormal_completion_at_limit`, and
`commonNormal_energy_eq_limit_iff`.

### The exact alternative if density fails

If \(\delta>0\), the actual residual supplies an explicit common normal:

\[
Z_N=-\frac{r\mathbf1_{j>N}}{h_N},
\qquad \langle v_k,Z_N\rangle_P=1\quad(k\ge N).
\]

This witness need not be the minimum-energy witness. The formalization
keeps that distinction. It supplies a finite capacity bound at every head.
Conversely, density forces capacity to diverge. Hence at every N≥1,

\[
\boxed{
S\ne H_P
\iff \sup_M\kappa_{N,M}<\infty
\iff \text{a common normal witness exists at head N}.
}
\]

There is no mixed behavior in which capacity diverges at one positive head
but remains bounded at another.

In particular, the existing implication density⇒RH gives

\[
\neg\mathrm{RH}\Longrightarrow
\sum_{j=0}^{L-1}\frac{\eta_{N,N+j}^2}{\sigma_{N,N+j}}
\longrightarrow
\|Z_N^*\|_P^2-
\|u_N\mathbf1_{j>N}\|_P^{-2}<\infty
\]

for **every fixed N≥1**. This is an exact alternative, not a contradiction:
the infinite witness has not been excluded.

### Remaining research boundary

It now suffices to prove the divergence of the **single series at N=1**,
or equivalently to exclude the common normal witness at that head.
Neither statement is proved here. The continuation sharpens the reduction
and describes the alternative precisely; it does not establish the missing
arithmetic signed-gain estimate, vanishing residual, or RH.

No classical PNT/Möbius limit is assumed by the new finite identities,
single-head equivalences, or duality theorems. The concurrently published base now supplies the unconditional theorem
`mobiusReciprocalSum_tendsto_zero` (in namespace
`RiemannResearch.RH.Pareto`) and `canonicalMobiusHilbert_sublinear`.
`RH/ParetoResidualTailDichotomy.lean` also supplies the unconditional actual
normalized-tail dichotomy. This discharges the earlier arithmetic provider
gap; these are concurrent results preserved by this continuation, not part
of its 34 new declarations.

### Verification and publication record

Final combined source check: `job_zlpsi9FY79x2fOCE4zLKO9LR2SH4pa0V`.
Result: **exit code 0, verified true, no warnings**.
Axiom audits of the finite-head density equivalence, all-head capacity bound,
attained infinite dual minimum, single-series density and RH criteria, and
not-RH gain limit report only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced.
The divergence hypothesis in the RH implication remains explicit.

The combined source check used the original base
`1dc33e10b7a364bfafe83194e28c87fab9cd1d24`.
The first checkpoint passed validation and created local commit
`c7f2d14c52027b59f6062abb92520f61dcc41d2a`, but publication encountered
a concurrent theorem-catalog conflict. That commit remains preserved.
The unchanged proof modules were transferred to the newer published base,
preserving its PNT formalization and placing the new catalog section below
the existing Schur entry.

Current workspace: `ws_rYXP8I0ssgLKpM720Tm69r7Vk3X-FdEL`.
Publication base: `e841611e50f744ce1c070f41e9b8258587bfae16`.
The publication checkpoint validates the three new modules and any local
reverse dependents. Its final job and published commit are recorded in the
returned handoff after completion. This is not a fresh full-project rebuild.
