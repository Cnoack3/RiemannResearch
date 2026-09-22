## 15. Exact first-head projection defect and heavy tails of every annihilator — 22 September 2026

This continuation adds **42 theorem declarations in four Lean modules**.
The statements below concern the actual complete Pareto Hilbert space and full
signed covariance. They do not prove RH or assume the missing capacity divergence.
No claim of novelty is made.

### Exact finite capacity as a projection error

Let \(e_1(j)=\mathbf1_{j=1}\), with \(\|e_1\|_P^2=1/2\). For \(M\ge1\), set

\[
t_M=\|e_1-P_{V_{M+1}}e_1\|_P^2,
\qquad t=\|e_1-P_Se_1\|_P^2.
\]

The manuscript uses \(V_{M+1}=\operatorname{span}(g_2,\ldots,g_{M+1})\);
Lean calls this `finiteSpace M`. The established identity is

\[
\boxed{t_M=\frac1{\kappa_{1,M}+2}.}
\]

This is the **unconstrained orthogonal-projection error** of the first-point
indicator. It differs from the previously established exact-head optimizer
error \(\kappa_{1,M}^{-1}\). Both identities hold simultaneously.

The proof identifies the minimum full energy under the single constraint
\(F(1)=1\). If \(q_M=\|P_{V_{M+1}}e_1\|_P^2>0\), the normalized projection
has minimal energy \(1/(4q_M)\). The already attained covariance minimum
has full energy \(1/2+1/\kappa_{1,M}\). Equating these gives the formula.
The general Hilbert-space theorem includes the optimizer, exact Pythagorean
completion, and uniqueness.

The complete conductor limit is also identified:

\[
t_M\longrightarrow t,\qquad t=0\iff S=H_P.
\]

When \(S\ne H_P\), \(t>0\) and

\[
\boxed{\kappa_{1,M}\longrightarrow t^{-1}-2
       =\|Z_1^*\|_P^2.}
\]

Here \(Z_1^*\) is the strong limit of the actual finite normals from Section 14.
No coefficient or inverse-matrix bound is assumed. The exact one-step defect
decrease is

\[
t_M-t_{M+1}
=\frac{\eta_{1,M}^2/\sigma_{1,M}}
       {(\kappa_{1,M}+2)(\kappa_{1,M+1}+2)}.
\]

Principal declarations in `RH/CanonicalMobiusSingleHeadCapacity.lean` are
`singleHeadError_eq_inv_capacity_add_two`, `singleHeadError_tendsto`,
`singleHeadCapacity_limit_of_not_density`, `singleHeadNormal_limit_energy`,
and `singleHeadError_succ_drop`.
The reusable minimum theorem is
`Analysis/SingleObservationProjection.observation_energy_isLeast`.

### Every nonzero arithmetic annihilator has heavy normalized tails

The former result for the canonical residual extends to the **entire**
orthogonal complement:

\[
\boxed{
0\ne z\in S^\perp
\quad\Longrightarrow\quad
N\sum_{j>N}\frac{|z(j)|^2}{j(j+1)}\longrightarrow+\infty.
}
\]

There is no nonzero-mean hypothesis in this theorem.
First, a nonzero pairing \(\langle z,\mathbf1\rangle\) gives the result from
the established unconditional \(\|u_N\|_P^2=o(N)\) and the exact inequality

\[
|\langle z,\mathbf1\rangle|^2
\le \|z\mathbf1_{j>N}\|_P^2\,\|\mathbf1-u_N\|_P^2.
\]

For an arbitrary nonzero \(z\), some integer threshold \(D_B\mathbf1\) has
nonzero pairing with it. These thresholds separate Hilbert vectors, because
\(e_N=\mathbf1-B^{-1}D_B\mathbf1\), \(B=N+1\), and successive head
indicators recover every coordinate. Dilation invariance gives
\(\langle z,D_Bu_N\rangle=0\), while

\[
D_B(\mathbf1-u_N)=0\quad\text{through coordinate }N,
\qquad
\frac{\|D_B(\mathbf1-u_N)\|_P^2}{N}
=B\frac{\|\mathbf1-u_N\|_P^2}{N}\longrightarrow0.
\]

The same complete-tail Cauchy–Schwarz argument finishes the proof.
Consequently any actual annihilator with a bounded cofinal subsequence of
normalized tail energies must be zero.

These are
`every_nonzero_annihilator_normalized_tail_tendsto_atTop` and
`annihilator_eq_zero_of_frequently_bounded_normalized_tail` in
`RH/ParetoAnnihilatorTail.lean`. The module proves the exact physical
weighted-tail interpretation as well. It uses the project's now-unconditional
PNT/Möbius sublinear-energy theorem, with no arithmetic provider premise.

### Quantitative comparison with the original RH residual

Put

\[
\rho=e_1-P_Se_1,\qquad t=\|\rho\|_P^2,
\qquad r=\mathbf1-P_S\mathbf1,\qquad\delta=\|r\|_P^2,
\qquad h=\langle\rho,\mathbf1\rangle_P.
\]

The checked identities and bounds are

\[
h=\langle r,e_1\rangle_P=\langle r,\rho\rangle_P,
\qquad\|r-\rho\|_P^2\le\delta/2,
\]

\[
\boxed{(2-\sqrt2)t\le h\le(2+\sqrt2)t,}
\qquad
\boxed{(6-4\sqrt2)t\le\delta\le(6+4\sqrt2)t.}
\]

The norm estimate comes from orthogonally compressing \(\tfrac12D_2r\):
the difference between that vector and \(r-\rho\) belongs to \(S\), while
\(r-\rho\in S^\perp\). The remaining inequalities follow from exact norm
expansion and Cauchy–Schwarz.

Combining them with the exact limiting capacity gives, in the nondense case,

\[
\boxed{
6-4\sqrt2\le\delta\bigl(\|Z_1^*\|_P^2+2\bigr)
\le6+4\sqrt2.
}
\]

Thus the first-head capacity determines the original projection defect up to
explicit absolute constants. This supplies a quantitative connection between
the single-head problem and the constant-target RH problem.

`RH/ParetoFirstHeadDefect.lean` proves these bounds, the positive mean of
\(\rho\) whenever \(\delta>0\), and its normalized-tail divergence.
Principal declarations include `firstHeadResidual_compressed_dilation_bound`,
`firstHeadResidual_pairing_energy_bounds`, `firstHeadResidual_limitEnergy_bounds`,
and `singleHeadNormal_global_defect_comparison`.

### Exact remaining boundary

The following sufficient condition for Mathlib RH is formally verified:
a bounded cofinal subsequence of
\(N\|\rho\mathbf1_{j>N}\|_P^2\), for this one explicitly defined first-point
projection defect. The declaration is
`riemannHypothesis_of_firstHeadResidual_frequently_bounded_tail`.
**The tail upper bound itself remains open.**

Equivalently at the geometric level, the open task remains \(t=0\), or
divergence of \(\kappa_{1,M}\), or exclusion of the common normal in Section 14.
The new heavy-tail theorem is a necessary condition on possible obstructions,
not a contradiction: finite Pareto norm permits this tail growth.
The separate formalization of the classical RH-to-density converse is not
silently inserted. No proof of RH is claimed.

### Verification and reproducibility

Workspace: `ws_rYXP8I0ssgLKpM720Tm69r7Vk3X-FdEL`.
Base commit: `c0efb2e558d38c98d6f648209355d2367ddbe309`.
Final combined source check: `job_eQYy3SA8oUxEsbP7m1RwVaACK2BbIcQf`.
Result: **exit code 0, verified true, no warnings**. Axiom audits of the
principal capacity identity, general annihilator theorem, explicit defect
comparison, and conditional RH consumer report only `propext`,
`Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced.
The domain-specific tail upper-bound hypothesis in the RH consumer remains
explicit; an axiom audit does not discharge that hypothesis.

The publication checkpoint validates the four new modules and local reverse
dependents. Its result is recorded in the returned handoff. This is not a
fresh full-project rebuild.
