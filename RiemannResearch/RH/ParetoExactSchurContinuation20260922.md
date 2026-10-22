## 13. Exact signed Schur recursion, positive definiteness, and fixed-head density — 22 September 2026

This continuation adds **47 theorem declarations across six Lean modules**.
It supplies an exact conductor-by-conductor capacity formula, proves its
denominator positive for every genuinely higher canonical index, and
constructs continuous finite legal head repairs. The asymptotic numerator
estimate remains open; RH is not proved.

### Complete-tail covariance is positive definite for distinct positive indices

`RH/CanonicalMobiusTailIndependence.lean` strengthens finite periodicity to
injectivity of the entire tail restriction on each finite legal space:

\[
F,G\in V_{M+1},\quad F(j)=G(j)\ \text{for all }j>N
\quad\Longrightarrow\quad F=G.
\]

Here the manuscript notation is \(V_{M+1}=\operatorname{span}(g_2,\ldots,g_{M+1})\),
which the project calls `finiteSpace M`.
Using triangularity and the already verified \(m_{M+1}\ne0\), it proves
\(u_{M+1}\notin\operatorname{span}(g_2,\ldots,g_{M+1})\).
Thus for any finite set of **distinct positive canonical indices**, any
cutoff \(N\ge0\), and any nonzero coefficient vector,

\[
\boxed{\sum_{k,\ell}c_kc_\ell\mathcal C^{(N)}_{k\ell}>0.}
\]

Principal declarations are `finiteSpace_eq_zero_of_tailShift_eq_zero`,
`canonicalMobiusHilbert_succ_tail_residual_energy_pos`, and
`signedMobiusAverage_covariance_pos_of_coeff_ne_zero`.
In particular, every canonical window \(u_N,\ldots,u_M\), with \(N\ge1\),
has a positive-definite full-tail covariance matrix. The earlier singular
formulation remains useful for indexed families allowing repetitions.
There is no uniform smallest-eigenvalue lower bound here.

### Actual screening and exact signed gain

At fixed cutoff N, let \(v_i=u_{k_i}\mathbf1_{j>N}\) denote the old complete
tails, and let \(v_m=u_m\mathbf1_{j>N}\) be a new one. Define

\[
C_{ij}=\langle v_i,v_j\rangle_P,\qquad
b_i=\langle v_i,v_m\rangle_P,\qquad d=\|v_m\|_P^2.
\]

`Analysis/FiniteGramOneStepCapacity.lean` constructs an actual solution
\(a\) of \(Ca=b\), including singular old systems. Let \(Cz=\mathbf1\),
\(Z=\sum_i z_i v_i\), and set

\[
\boxed{
\eta=1-\langle v_m,Z\rangle_P=1-\sum_i a_i,
\qquad
\sigma=\left\|v_m-\sum_i a_iv_i\right\|_P^2
=d-\sum_i a_i b_i.
}
\]

`RH/CanonicalMobiusOneStepCapacity.lean` proves

\[
\boxed{\kappa_{\rm new}-\kappa_{\rm old}=\frac{\eta^2}{\sigma}.}
\]

These are the actual infinite signed covariance entries, without truncation
or replacement by absolute values. The generic zero-denominator case is
handled explicitly: it forces \(\eta=0\) and zero capacity gain.
For a new index larger than every old index, Lean proves \(\sigma>0\)
without a supplied independence or nonsingularity hypothesis. Hence

\[
\kappa_{\rm new}>\kappa_{\rm old}\quad\Longleftrightarrow\quad\eta\ne0.
\]

The key declarations are `capacity_oneStep_increment`,
`oneStepDefect_eq_one_sub_sum`, `oneStepSchur_expansion`,
`oneStepSchur_succ_pos`, and `capacity_oneStep_strict_iff`.
Strict positivity of \(\sigma\) does not prove that \(\eta\ne0\), or
give a lower bound on the accumulated gain.

### Exact window recursion and its initial value

Write \(\kappa_{N,M}\) for the full-tail capacity of \(u_N,\ldots,u_M\).
For \(M\ge N\ge1\), let \(\eta_{N,M},\sigma_{N,M}\) be the preceding
quantities when adding \(u_{M+1}\). Then

\[
\boxed{
\kappa_{N,M+1}=\kappa_{N,M}+
\frac{\eta_{N,M}^2}{\sigma_{N,M}},\qquad\sigma_{N,M}>0.
}
\]

`RH/CanonicalMobiusWindowRecursion.lean` verifies the reindexing of the
enlarged family, its initial value, and the exact telescope:

\[
\boxed{
\kappa_{N,N+L}
=\frac1{\|u_N\mathbf1_{j>N}\|_P^2}
+\sum_{j=0}^{L-1}\frac{\eta_{N,N+j}^2}{\sigma_{N,N+j}}
\qquad(N\ge1,\ L\ge0).
}
\]

These are `windowCapacity_succ`, `windowCapacity_diagonal`,
`windowCapacity_telescope`, and `windowCapacity_eq_base_add_gains`.

### Continuous head repair and the complete conductor limit

`RH/CanonicalMobiusHeadRepair.lean` constructs a continuous map
\(R_{N,z}\) that repairs any vector's first N physical coordinates to those
of a prescribed target z. Recursively, with \(R_{0,z}(x)=x\),

\[
R_{n+1,z}(x)=R_{n,z}(x)+
\frac{z(n+1)-R_{n,z}(x)(n+1)}{n+1}
\bigl((n+2)g_{n+2}-(n+1)g_{n+1}\bigr).
\]

The added vector vanishes through coordinate n and equals n+1 at the next
coordinate. The construction does not divide by \(m_n\).
Lean proves exact head agreement, continuity, \(R_{N,z}(z)=z\), and that
repairing \(x\in\operatorname{span}(g_2,\ldots,g_{M+1})\) introduces no
conductor beyond \(\max(M,N)+1\).

Consequently **for each fixed N**, every \(z\in S\) has finite legal
approximants converging in full norm to z while matching its first N
coordinates exactly. This is `exists_legal_exact_head_approximants`;
`exists_legal_exact_head_near` gives its epsilon formulation. No repair-norm
bound uniform in growing N is claimed.

`RH/CanonicalMobiusCapacityDensity.lean` constructs the actual finite head
indicator \(e_N(j)=\mathbf1_{1\le j\le N}\), proves its zero tail and
\(\|e_N\|_P^2=N/(N+1)\), and combines the repair with the unrestricted
finite minimum from Section 12. It proves the exact geometric equivalences

\[
\boxed{
S=H_P
\quad\Longleftrightarrow\quad
\forall N\ge1:\ \kappa_{N,M}\longrightarrow+\infty\ (M\to\infty)
\quad\Longleftrightarrow\quad
\forall N\ge1\ \exists M\ge N:\ \kappa_{N,M}\ge1.
}
\]

The forward construction approximates \(e_N\), not the constant vector,
so the optimal tail energy tends to **zero** at each fixed head under
density. The converse selects actual optimized exact-head vectors with
full norm squared at most 2 and uses the verified bounded-head closure
theorem. The principal declarations are
`density_iff_canonicalWindow_capacity_ge_one` and
`density_iff_canonicalWindow_capacity_diverges`.

This is an equivalence with actual legal-span density. The project already
proves density implies Mathlib RH. The classical converse RH implies this
density is not silently inserted: it remains a separate formalization
provider in the project.

### The precise next sufficient estimate

`riemannHypothesis_of_window_gain_divergence` proves actual Mathlib RH from

\[
\boxed{
\forall N\ge1:\quad
\sum_{j=0}^{L-1}\frac{\eta_{N,N+j}^2}{\sigma_{N,N+j}}
\longrightarrow+\infty\qquad(L\to\infty).
}
\]

This is a **conditional research reduction**: the displayed divergence
has not been proved. A weaker sufficient target remains the fixed positive
cofinal window-capacity lower bound from Section 12. The recurrence now
expresses both targets through actual signed sources and strictly positive
screened energies. No arithmetic lower bound for these sources is supplied.

Still unproved: the needed cumulative-gain or cofinal-capacity estimate,
vanishing projection residual, and RH. The prior known-arithmetic provider
\(m_N\to0\) is also not formalized in this continuation; none of the new
finite identities or geometric equivalences assumes it.

### Verification and reproducibility

Workspace: `ws_YCBn4_yOwTvJ6_8f5sZf9beWp7vIYaNZ`.
Base commit: `9bb15d844ccae05e9c251e943e804a0ac8ca9835`.
Final combined source check: `job_bUDKDbIa3uIFsk916O3svMf48Xg-wI9a`.
Result: **exit code 0, verified true, no warnings**. Axiom audits of positive
definiteness, exact gain, positive Schur denominator, head repair, the density
equivalence, the telescope, and the direct cumulative-gain RH criterion report
only `propext`, `Classical.choice`, and `Quot.sound`.

No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced.
Explicit density or divergence premises remain part of their theorem
statements; axiom audits do not discharge them. Publication uses affected-module
and local reverse-dependent validation. The supplied handoff records the final
checkpoint and published commit after that job completes.
