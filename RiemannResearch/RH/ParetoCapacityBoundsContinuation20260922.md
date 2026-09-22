## 11. Quantitative capacity bounds and uniform residual obstruction — 22 September 2026

This continuation adds **16 verified theorem declarations** across three Lean
modules. It advances the capacity analysis without proving RH. All quantities
are those of the actual canonical Möbius family with complete infinite Pareto
tails; no unsigned or truncated covariance replaces the signed form.

### Unconditional lower bounds

Write κ(N,k) for the capacity of a finite nonempty family of positive
canonical indices k_i at cutoff N. For every member i, Lean now proves

\[
1\le \kappa(N,k)\,
  \|u_{k_i}\mathbf1_{j>N}\|_P^2
\le \kappa(N,k)\,\|u_{k_i}\|_P^2,
\qquad
\boxed{\kappa(N,k)>\frac1{4k_i}.}
\]

These use the actual normal equations and the already verified strict full
energy bound \(\|u_k\|_P^2<4k\). Neither PNT nor RH is a hypothesis.
The declarations in `RH/CanonicalMobiusCapacityBounds.lean` are:

- `capacity_mul_tail_energy_ge_one`;
- `capacity_mul_full_energy_ge_one`;
- `reciprocal_four_mul_lt_capacity`.

If a growing family **contains index N**, the single explicit arithmetic premise

\[
m_N=\sum_{d\le N}\mu(d)/d\longrightarrow0
\]

implies

\[
\boxed{N\kappa_N\longrightarrow+\infty.}
\]

This is `normalized_capacity_tendsto_atTop_of_reciprocal_cancellation`.
Its proof combines \(1\le\kappa_N\|u_N\|_P^2\) with the existing theorem
\(\|u_N\|_P^2/N\to0\). Membership of index N is essential to this particular
statement; merely assuming every index is at least N does not imply
\(\kappa_N>1/(4N)\).

The classical limit \(m_N\to0\) remains an explicit hypothesis. Bounded
discovery in the project and Mathlib did not locate an unconditional provider.
This is a formalization gap for a known arithmetic input, not an assertion
that the arithmetic limit is an open mathematical problem.

### Exact residual bound, uniform over all finite families

Let

\[
\delta=\|r\|_P^2,\quad
T_N=\sum_{j>N}w_j r(j)^2,\quad
h_N=\sum_{j\le N}w_j r(j).
\]

The new module defines `residualHeadPairing` in the equivalent weighted
Hilbert coordinates and proves \(h_N\to\delta\). For every legal vector F
equal to one through N, it proves the **signed** identity

\[
\langle r\mathbf1_{j>N},F\mathbf1_{j>N}\rangle_P=-h_N
\]

and its Cauchy–Schwarz consequence. Applying these to the attained optimizer
gives the finite-stage inequality

\[
\boxed{\kappa_N h_N^2\le T_N.}
\]

This is `capacity_mul_residual_head_sq_le`. The supporting declarations are
`residualHeadPairing_tendsto`, `exact_head_coordinate_eq`,
`residual_tail_pairing_eq_neg_head`, and
`residual_head_sq_le_tail_product`.

If \(\delta>0\), then eventually \(h_N>\delta/2\), so

\[
\boxed{\kappa_N\le\frac4{\delta^2}\,T_N.}
\]

`capacity_uniform_residual_bound` quantifies over **all finite nonempty
index types and all admissible families after the eventual cutoff**. Thus its
threshold is independent of family size, repetitions, or the largest conductor.
The hypotheses on the indices are \(k_i>0\) and \(k_i\ge N\).

Since \(T_N\to0\), `capacity_uniform_tendsto_zero_of_not_RH` proves

\[
\neg\mathrm{RH}\ \Longrightarrow\forall\varepsilon>0\ \exists N_0\ \forall N\ge N_0\
\forall\text{ admissible finite families},\quad
\kappa(N,k)<\varepsilon.
\]

This strengthens the earlier decay theorem for each specified sequence of
families to an explicitly uniform statement.

### Family enlargement and exact change of cutoff

`Analysis/FiniteGramAffineMinimum.lean` now proves
`normal_mass_mono_of_affine_transfer` and
`normal_mass_mono_of_family_map`. The family map may be noninjective:
coefficients are transferred by summing over its fibers. This retains singular
systems and repeated vectors.

Its application `capacity_mono_of_family_map` in
`RH/CanonicalMobiusCovarianceMinimum.lean` proves that enlarging a finite
canonical family at a fixed cutoff cannot decrease capacity.

The same application module adds `capacity_inv_le_tail_energy` and the exact
`capacity_inv_cutoff_identity`: for the **same family**, with all
\(k_i\ge K\ge N\),

\[
\boxed{
\kappa(N,k)^{-1}
=\kappa(K,k)^{-1}+\frac K{K+1}-\frac N{N+1}.
}
\]

Consequently the full optimal energy
\(N/(N+1)+\kappa(N,k)^{-1}\) is independent of which admissible head
cutoff is used for that fixed family. This does not give monotonicity when
both the family and the cutoff are changed without a corresponding comparison.

### What these results do and do not settle

For families containing N, the established implications permit both

\[
\kappa_N\to0,\qquad N\kappa_N\to+\infty.
\]

For example, these rates are compatible for the numerical sequence
\(N^{-1/2}\); this is only an illustration of the logical gap, not a claim
about the actual covariance capacities.

**The open research target remains:** construct a fixed \(\varepsilon>0\)
and admissible finite families with \(\kappa_N\ge\varepsilon\) at
arbitrarily large N. The previously verified capacity-to-RH theorem then applies.
No such family or bound is constructed here; RH and residual vanishing remain
unproved.

A possible next structural target, not formalized here, is to prove nonvanishing
of the finite reciprocal Möbius sums and then identify the affine span of
\(u_N,\ldots,u_M\) with all finite legal vectors having the prescribed head.
This requires additional arithmetic and spanning proofs; it supplies no
capacity lower bound by itself.

### Verification record

Final combined source check: `job_gIOZ7Sjcrieb9GvOkq2EXGvnavfoaXZn`.
Result: **exit code 0, verified true, no warnings**.

Axiom audits of uniform capacity decay, normalized-capacity divergence,
family monotonicity, and the cutoff identity report only
`propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project-local axiom, or unsafe declaration was added.
These audits do not discharge the explicit reciprocal-cancellation hypothesis.

Workspace: `ws_YCBn4_yOwTvJ6_8f5sZf9beWp7vIYaNZ`.
Base commit: `660e7a05b4a895e18ff9ff3e58deb8db8f09ab51`.
The final publication checkpoint validates the changed modules and their local
reverse dependents.
