# Actual compensated-source and quartic-tail continuation

The Riemann Hypothesis is not proved by this continuation. It supplies exact
finite geometry, constructive normalized error budgets, and unconditional
summability bounds. The arithmetic inputs that would force the limiting
projection defect to vanish remain Open.

## Complete physical compensated source

`RH/PhysicalCompensatedSource.lean` constructs the actual finite packet
family, proves its independence from the existing actual Gram injectivity,
and screens the fresh block against the entire old Gram projection. For
nested legal finite packet sets s ⊆ t, write e for that innovation family.
The old set contains an odd prime when the explicit old projection
coefficients are used to identify the actual source.

The tail-old space is the span of `(I-Q_N)` applied to every old packet.
Its actual finite-dimensional orthogonal projection constructs

\[
z_N=(I-P_{\mathrm{tail,old}})(I-Q_N)1,
\qquad T_N=1-z_N
=Q_N1+P_{\mathrm{tail,old}}(I-Q_N)1.
\]

The complete Pythagorean identity retains the old-tail fit square. It gives
`norm(z_N)^2 ≤ 1/(N+1)` without a supplied tail Gram inverse or norm bound.
For the innovation observation radius,

\[
\rho_N=\operatorname{capacity}_e(\langle e,z_N\rangle)
=\|z_N\|^2-\|z_N-P_ez_N\|^2
\le\frac1{N+1}.
\]

The full signed matrix source eta is identified with the innovation
observations of one. Exact old/fresh reindexing and the screened capacity
identity prove

\[
\operatorname{capacity}_e(\eta)=E_s-E_t,
\qquad \eta_N=\langle e,T_N\rangle
=\langle e,Q_N1\rangle
+\langle e,P_{\mathrm{tail,old}}(I-Q_N)1\rangle.
\]

Every tail-fit source term is retained. The full innovation Gram comparison
then yields

\[
\left|\sqrt{E_s-E_t}
-\sqrt{\operatorname{capacity}_e(\eta_N)}\right|
\le\sqrt{\rho_N}.
\]

For any nested legal chain s_n, positive common periods L_n, and requested
cutoff floors F_n, choose the actual natural horizon

\[
N_n=\max\{n,F_n,2^n[L_n(L_n+1)]^2\}.
\]

The existing actual finite error floor
`E_n ≥ 1/[L_n(L_n+1)]` and the internally constructed observed radius give
`rho_n/E_n^2 ≤ 2^(-n)`. Thus the normalized error is summable. Put

\[
q_n=\left[\sqrt{\operatorname{capacity}(\eta_{N_n})}
-\sqrt{\rho_n}\right]_+^2.
\]

`observedCertificate_divergence_iff_explicit_horizon` identifies cumulative
divergence of the literal sums of `(E_n-E_(n+1))/E_n^2` and `q_n/E_n^2`.
The source capacity, observed error, gain sign, source-radius inequality,
and normalized summability are constructed internally. The theorem's
remaining conditions are nesting, legal packets, an old odd prime at each
stage, and positive common periods. It asserts neither divergence statement.

## Actual complete quartic optimizer tails

`ParetoMobiusHeadInterpolation` proves the full physical tail identity,
including the exact first omitted site N+1, and the unconditional estimate

\[
\|(I-Q_N)f\|^2\le\frac{16M^3\|f\|^2}{N+1},\qquad f\in V_M.
\]

Here `finiteSpace (M-1)` is the complete dictionary V_M. The estimate uses
the established unconditional reciprocal Mobius bound, not an RH-level
cancellation hypothesis.

For any target v, write p_N=P_(V_N)v, d_N=norm(v-p_N)^2, and
delta=norm(v-P_(closed legal span)v)^2. For N_0=B≥2 and N_(j+1)=N_j^4,
the exact projection displacement sum is d_B-d_(N_J), retaining its final
residual square. The whole optimizer-tail series is summable and satisfies

\[
\sum_{j\ge0}\|(I-Q_{N_{j+1}})p_{N_{j+1}}\|^2
\le\left(\sqrt{d_B-\delta}
+\sqrt{16\|v\|^2\left(\frac1B+
\frac{B^8}{B^{12}-1}\right)}\right)^2.
\]

The stronger first-stage split allowance is bounded by
`16 norm(v)^2 B^2/(B^3-1)`, which in turn improves the earlier
`32 norm(v)^2/B`. For the exact compact target `twoThreeDual`, norm squared
is 134 and the coefficient 16 norm(v)^2 is exactly 2144. The whole future
tail total tends to zero as B tends to infinity without a zero-defect or
density hypothesis. In particular, positive delta remains possible.

## Exact signed-source energy and conditional arithmetic

The actual rank-two source is `eta = m U - (Q/2) V`; neither signed term
is removed. For a symmetric quadratic form Z, put A=U'ZU, B=U'ZV and C=V'ZV.
For C≠0 the complete energy is

\[
\eta'Z\eta=m^2A-mQB+Q^2C/4
=m^2(A-B^2/C)+C(Q/2-mB/C)^2.
\]

For C>0 this gives the sharp uniform-in-Q orthogonal lower bound; the
parallel square remains in the equality. The C=0 endpoint is handled
without division using positive-form Cauchy. The strict actual arithmetic
two-source determinant is not supplied by these identities.

`PhysicalResidualMean` proves the actual ordinary residual mean formula and
algebraicity of the genuine inverse-core coefficients. Nonzero mean and
strict finite mean-one penalty are **conditional research reductions**
whose explicitly named `BakerVonMangoldtSeparation` hypothesis is an Open
formal provider. It is a proposition parameter, not a project-local axiom.
Baker's published theorem supports the paper separation argument; a Lean
provider for that theorem is not added here. The finite independent-source
consumer likewise leaves its actual Baker and cyclotomic trace providers
explicit.

## Remaining provider ledger

| Obligation | Status |
|---|---|
| Actual finite Gram inverses, packet independence and old/fresh geometry | Established by existing providers and the concrete assembly above |
| Full compensated target error and exact observed radius | Constructed internally |
| Explicit normalized observed-error summability | Constructed internally |
| Unconditional complete quartic optimizer-tail summability | Established; permits positive limiting defect |
| Actual optimizer-tail/trial-energy product saving at the prescribed arithmetic scale | **Open** |
| Divergence of the literal actual normalized gain or compensated-certificate sum | **Open** |
| Formal Baker separation and actual finite trace/nonvanishing providers | **Open** for the conditional signed-source nonvanishing route |
| A quantitative moving-stage source lower bound that forces divergence | **Open** |

The scalar endpoint equivalence is now formalized in
`Analysis/CompensatedSourceCertificate.lean`: for a strictly positive antitone
error sequence, normalized-gain divergence is equivalent to E_n tending to
zero. The fixed-tail-block lower bound retains (E_n-E_J)/E_n^2; a positive
floor delta instead bounds every prefix by (E_0-E_J)/delta^2. Applying the
equivalence does not supply the arithmetic zero-limit or divergence input.

The newer radical-difference common-kernel result on GitHub main does not
identify a chosen conductor coordinate of the screened totient source. The
remaining trace provider, on the paper's fresh-prime congruence subsequence,
is the cyclotomic relative trace Tr(J_(pk,old))=0 and hence
Tr(V_(pk))=(p-1)^2 phi(k)>0 for k>1. Its actual coefficient-field/source
assembly remains an Open formal dependency.

A freely enlarged physical horizon closes the normalized-error allowance.
It does not close the product-saving estimate at an arithmetic stage whose
cutoff and conductor are prescribed together. Finite positivity, mean
nonvanishing, and sparse tail summability do not imply cumulative divergence
or RH.

## Verification

The continuation comprises 138 new public theorems; additional definitions
are not included in that count. The full scalar owner (31 theorems) and the
full actual finite-tail provider file pass native file checks with exit code
zero and no diagnostics. The concrete physical application check also passes
with exit code zero and no diagnostics.

The final coherent native-import check inlines the exact new concrete and
quartic application bodies and the four scalar endpoint bodies, and loads
the other new declarations from their compiled owners. It passes with exit
code zero in 15.446 seconds. A fresh transitive declaration walk, without
using imported axiom-result summaries, reports:

```
AUDIT PASSED: 138 public theorems;
transitive axioms [Quot.sound, Classical.choice, propext];
visited 54296 constants.
```

Verification code SHA-256:
`7ce6c0b15ffd8d888f867971a83408b279f67f9c4b0022d470275640d7ac2d6e`.
The proof checks use the pinned Lean 4.33.0-rc2 environment. Earlier isolated
algebraic and generic checks also pass; the interrupted initial cold build
is not counted as successful validation. Native dependency compilation found
and prompted repairs to a period-mean namespace reference and finite-tail
implementation details. The successful focused and coherent checks above
use their repaired bodies.

The final publication checkpoint validates changed modules and reverse
dependents against their actual project imports before committing and pushing.
A successful ephemeral check alone is not a claim of checkpoint acceptance.
Substantive hypotheses remain as listed in the provider ledger even when the
axiom audit is clean. Wolfram independently confirms the first-stage split
allowance identity and both geometric comparisons under B >= 2; these
computational cross-checks supplement the Lean proofs.

Sources: user-provided RH_Actual_Arithmetic_Advances_2026-10-07.pdf,
crt_complete_tail_certificate.txt, and crt_baker_mean_source_handoff.txt;
Baker, Mathematika 13 (1966), 204–216,
https://doi.org/10.1112/S0025579300003971; Dasgupta,
https://arxiv.org/abs/2303.02037, Theorem 1.2. The references support the
statements and proof strategy; no mathematical novelty claim is made.
