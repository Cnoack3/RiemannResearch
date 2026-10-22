# Finite affine exhaustion and capacity increments

## 12. Finite affine exhaustion and exact capacity increments — 22 September 2026

This continuation closes the finite nonvanishing and spanning targets proposed
in Section 11. It adds **43 public theorem declarations**, plus three private
proof helpers, across six Lean modules. All statements below are unconditional
under their displayed finite-index conditions. No PNT or RH premise is used.
The asymptotic capacity bound remains unproved.

### Every finite reciprocal Möbius sum is nonzero

`RH/MobiusReciprocalNonvanishing.lean` proves
`mobiusReciprocalSum_ne_zero`:

\[
\boxed{m_N=\sum_{d\le N}\frac{\mu(d)}d\ne0\quad(N\ge1).}
\]

The proof is finite arithmetic. For N≥2, Bertrand supplies a prime
N/2<p≤N. It is the only denominator among 1,...,N divisible by p, and
μ(p)=−1. Let D be the product of the remaining denominators and let A be
the integer obtained by clearing them. If m_N=0, then pA=D, contrary to
p not dividing D. N=1 is immediate.

The reusable upper-half prime and denominator-clearing lemmas are in
`NumberTheory/IsolatedPrimeReciprocalSum.lean`. This proves finite
nonvanishing; it does not supply the separate classical limit m_N→0.

### The canonical vectors exhaust every finite legal exact-head class

Set g_1=0 and h_d=(d+1)g_{d+1}−dg_d. The module
`RH/CanonicalMobiusTriangular.lean` proves the exact identities

\[
h_d(j)=0\ (j<d),\qquad h_d(d)=d,\qquad
u_d-u_{d-1}=m_dh_d,\qquad
u_N=\sum_{d=1}^N m_dh_d,
\]
with u_0=0. Its `consecutiveResidueHilbert n` denotes h_{n+1}.

Using the checked nonvanishing theorem, it proves

\[
\operatorname{span}(u_1,\ldots,u_M)
=\operatorname{span}(g_2,\ldots,g_{M+1}).
\]

More strongly, for M≥N≥1,

\[
\boxed{
\operatorname{aff}\{u_N,\ldots,u_M\}
=\{F\in\operatorname{span}(g_2,\ldots,g_{M+1}):
F(1)=\cdots=F(N)=1\}.
}
\]

The declaration
`exists_canonicalMobius_affine_expansion_of_exact_head` supplies actual
coefficients c indexed by Fin(M−N+1), with

\[
\sum_i c_i=1,\qquad F=\sum_i c_i u_{N+i}.
\]

The reverse inclusion follows from the already verified exact heads and
finite-span membership. No conductor beyond M+1 is introduced, and every
signed term is retained.

Supporting declarations prove finite head injectivity, the triangular
decomposition, and the span of directions vanishing on the prescribed head.
`exact_head_eq_canonical_at_diagonal` proves that at budget M=N the
only legal vector with this head is u_N. Extra conductor budget is therefore
necessary to obtain a different exact-head vector.

### The covariance minimum is the unrestricted finite legal minimum

Define κ_{N,M} using the complete infinite tail covariance of
u_N,...,u_M. The module `RH/CanonicalMobiusWindowMinimum.lean` proves,
for M≥N≥1,

\[
\boxed{
\min_{\substack{F\in\operatorname{span}(g_2,\ldots,g_{M+1})\\
F(1)=\cdots=F(N)=1}}
\|F\mathbf1_{j>N}\|_P^2=\kappa_{N,M}^{-1},
}
\]

and

\[
\boxed{
\min_{\substack{F\in\operatorname{span}(g_2,\ldots,g_{M+1})\\
F(1)=\cdots=F(N)=1}}
\|F\|_P^2=\frac N{N+1}+\kappa_{N,M}^{-1}.
}
\]

These are actual attained `IsLeast` statements:
`canonicalWindow_tail_isLeast_all_legal` and
`canonicalWindow_full_isLeast_all_legal`.
They identify the previous signed-average optimizer with the optimum over
every finite legal candidate at the same head and conductor budget.
The finite family restriction therefore loses no candidates.

### Exact growth and saturation under conductor enlargement

The modules `Analysis/FiniteGramCapacityIncrement.lean` and
`RH/CanonicalMobiusCapacityIncrement.lean` introduce the actual
unnormalized normal tail vector Z. It satisfies

\[
\langle v_i,Z\rangle=1,\qquad \|Z\|^2=\kappa,
\]
where v_i is the complete tail of the corresponding canonical vector.

For any inclusion of an old family into a new family at the same cutoff,

\[
\boxed{\kappa_{\rm new}-\kappa_{\rm old}
=\|Z_{\rm new}-Z_{\rm old}\|^2.}
\]

No injectivity of the family map or invertibility of either Gram matrix is
assumed. Equality of capacities occurs exactly when Z_old satisfies every
new normal equation.

For any newly available vector v_j and any old signed coefficient vector a,
Lean also proves the quantitative estimate

\[
\boxed{
\bigl(1-\langle v_j,Z_{\rm old}\rangle\bigr)^2
\le
\left\|v_j-\sum_i a_i v_i\right\|^2
(\kappa_{\rm new}-\kappa_{\rm old}).
}
\]

The principal declarations are
`capacity_increment_eq_normal_distance_sq`,
`capacity_eq_iff_all_normal_equations`, and
`capacity_normal_defect_sq_le_screened_gain`.
Thus a lower bound for the signed normal-equation defect, relative to its
prediction error from the old span, would force a quantitative capacity gain.
Such an arithmetic lower bound is not supplied here.

### Exact remaining boundary toward RH

The finite nonvanishing, spanning, affine-exhaustion, and unrestricted-minimum
providers are now discharged. They do not control the sizes of 1/m_N or the
asymptotic signed covariance.

The remaining sufficient research estimate can now be stated without a
restriction to a special class of finite exact-head candidates:

\[
\exists\varepsilon>0\quad
\text{for arbitrarily large }N\quad
\exists M\ge N:\quad\kappa_{N,M}\ge\varepsilon.
\]

The existing capacity-to-RH theorem applies once such a bound is established.
A bounded cofinal family of full energies would suffice. Neither bound,
vanishing residual, nor RH is proved in this continuation.

### Verification and reproducibility

Final combined source check:
`job_p_JCpaJTUEEQoUZ-TWt0P25AN8yfThXj`.
Result: **exit code 0, verified true, no warnings**.
The isolated general-purpose arithmetic module also passed independently
in `job_9yHVoR-yGEBghnQZgyaoqnAcu0-tFT-R`.

Axiom audits of reciprocal-sum nonvanishing, affine coefficient extraction,
the unrestricted full-energy minimum, and the signed capacity-gain bound
report only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced.

Workspace: `ws_YCBn4_yOwTvJ6_8f5sZf9beWp7vIYaNZ`.
Base commit: `c22b39394a44c7f608b8afc729b19d09c4a70706`.
Publication uses changed-module and local reverse-dependent validation.
