# CRT decomposition of the actual full-Q inverse Gram matrices

Date: 2026-11-13. Source module:
[RiemannResearch/RH/QCRTGramSaturation.lean](RH/QCRTGramSaturation.lean).

## Scope and target

Let \(g_k(n)=(n\bmod k)/k\), with the repository's Q Hilbert realization,
and let \(V=\overline{\operatorname{span}}\{g_k:k\ge2\}\).
The finite family is **all** conductors \(2,\ldots,N+1\), not only primes
or squarefree conductors. Write
\[
G_N=(\langle g_{i+2},g_{j+2}\rangle_Q)_{i,j<N},\qquad
b_N=(\langle1,g_{i+2}\rangle_Q)_{i<N},\qquad
c_N=G_N^{-1}b_N,\quad s_N=b_N^\top c_N.
\]
The inverse is the complete Q Gram inverse already justified by
QCovarianceInvertibility and QFullResidueProjection. The new module does
not replace it with the inverse of a truncated CRT matrix.

Let \(v=\Pi_V1\), \(r=1-v\). The unconditional limits are
\[
s_N\longrightarrow\|v\|_Q^2=1-\|r\|_Q^2,\qquad
\|v\|_Q^2-s_N\longrightarrow0.
\]
The stronger statement \(s_N\to1\) is equivalent to \(1\in V\).
It is not proved unconditionally here. The density of the augmented family
\(\{g_k,Bg_k\}\) does not identify the closure of the unaugmented family
\(\{g_k\}\).

## CRT and Parseval matrix decomposition

Use the complete Q-orthonormal divisor-wavelet basis
\(\Psi_m=\mathrm{divisorWavelet}(m)/\sqrt{J_2(m)}\), \(m\ge1\), established
in QDivisorHilbertBasis. Put
\[
C_{m,i}=\langle g_{i+2},\Psi_m\rangle_Q
=\frac{\mathrm{qResidueDivisorCoefficient}(i+2,m)}{\sqrt{J_2(m)}}.
\]
For a positive conductor L, split the rows into \(m\mid L\) and \(m\nmid L\).
With \(C_{L,N}\) the retained rows,
\[
G_N=H_{L,N}+T_{L,N},\qquad
H_{L,N}=C_{L,N}^{\top}C_{L,N},\qquad
(T_{L,N})_{ij}=\sum_{m\nmid L}C_{m,i}C_{m,j}.
\]
The Lean statement headGram_parseval uses a tsum supported on the finite
set \(m\mid L\). It is exactly the finite retained-row matrix above.
The complementary matrix remains present. It is positive semidefinite
because its quadratic form is the squared norm of the omitted component.

Writing \(P_L\) for the orthogonal projection onto the divisor CRT cell
space and \(f_N=\sum_i(c_N)_ig_{i+2}\), define the entirely matrix-valued
retained error
\[
h_{L,N}=1-2s_N+c_N^\top H_{L,N}c_N.
\]
The verified identities are
\[
h_{L,N}=\|1-P_Lf_N\|_Q^2,\qquad
c_N^\top T_{L,N}c_N=\|(I-P_L)f_N\|_Q^2,
\]
\[
1-s_N=h_{L,N}+c_N^\top T_{L,N}c_N
=\sum_{m\ge1}\left|\mathbf1_{\{m=1\}}-\sum_i C_{m,i}(c_N)_i\right|^2.
\]
The Q wavelet basis and the full infinite energies are used throughout;
a Haar Fourier basis is not silently treated as Q-orthonormal.

## New moving-cutoff theorem

Suppose \(L_N>0\), \(i\le j\Rightarrow L_i\mid L_j\), and every positive
integer divides some \(L_N\). These are structural cofinality hypotheses,
not an approximation-rate or density hypothesis on the legal residues.
Then
\[
\boxed{c_N^\top T_{L_N,N}c_N\longrightarrow0},
\qquad
\boxed{h_{L_N,N}\longrightarrow\|r\|_Q^2}.
\]
The factorial tower is supplied explicitly. Cofinality here includes
arbitrary prime powers.

Proof: divisor-wavelet density gives strong convergence \(P_{L_N}\to I\).
The actual inverse-Gram candidates satisfy \(f_N\to v\), and
\[
\|(I-P_{L_N})f_N\|_Q
\le\|f_N-v\|_Q+\|(I-P_{L_N})v\|_Q\to0.
\]
The head limit then follows from the exact complete-error decomposition.
No convergence rate, coefficient summability, or interchange of an
uncontrolled infinite tail is assumed.

## Declaration map

All declarations below belong to
RiemannResearch.RH.QCRTGramSaturation.

| Declaration | Statement/status |
| --- | --- |
| saturation_eq_norm_sq; error_identity | Exact inverse-Gram projection energy identities. |
| saturation_tendsto | Unconditional scalar limit to \(\|\Pi_V1\|_Q^2\). |
| projection_energy_gap_tendsto_zero | Unconditional vanishing gap \(\|\Pi_V1\|_Q^2-s_N\). |
| saturation_tendsto_one_iff | \(s_N\to1\) iff \(1\in V\). |
| gram_parseval; error_parseval; limiting_defect_parseval | Complete, Jordan-weighted Parseval formulas. |
| gram_crt_split; headGram_parseval; tail_quadratic | Exact CRT decomposition and nonnegative complementary energy. |
| cell_closure_iSup_eq_top; conditionalProjection_tendsto | Exhaustion of the ambient Q space by a cofinal CRT tower. |
| moving_conditional_tail_tendsto | Moving-cutoff tail convergence for any norm-convergent sequence. |
| candidate_crt_tail_tendsto_zero; candidate_factorial_crt_tail_tendsto_zero | Actual inverse-Gram optimizer tails vanish. |
| candidate_tail_parseval | Omitted-mode energy as the complete complementary Parseval sum. |
| candidate_head_quadratic; candidate_tail_quadratic | Matrix/vector forms of retained and omitted candidate energies. |
| matrix_error_crt_split; headEnergy_eq_norm_sq | Exact complete error and retained error formulas. |
| matrix_tail_tendsto_zero | Literal inverse-Gram quadratic-form tail tends to zero. |
| matrix_head_tendsto | Retained error tends to \(\|1-\Pi_V1\|_Q^2\). |
| matrix_head_tendsto_zero_iff | Retained error tends to zero iff \(1\in V\). |
| riemannHypothesis_of_matrix_head_tendsto_zero | Conditional RH consequence via the existing Q-to-Pareto transfer. |

## Remaining obligation and RH status

For any fixed structural tower as above, prove
\[
1-2b_N^\top G_N^{-1}b_N+
(G_N^{-1}b_N)^\top H_{L_N,N}(G_N^{-1}b_N)\longrightarrow0.
\]
This is an equivalent reformulation of \(s_N\to1\), not an estimate
established by CRT. The new tail theorem removes the omitted-mode tail
as an independent obligation for these actual minimizers. The retained
error can still contain the entire limiting residual.

The conditional consumer explicitly assumes this retained-error zero
limit and deduces RiemannHypothesis using
QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure,
owned by QOptimizerParityRH. No unconditional RH conclusion or
RH converse is asserted.

## Verification

The coherent proof candidate, including every theorem and the four guarded
axiom checks, passed Bazel with BuildBuddy:
job `job_GEp_f5Uwg7nJPX1V41XyT4Zsx3CsKYz-`, exit code 0, verified true,
84.442 seconds of verification.
[BuildBuddy invocation](https://app.buildbuddy.io/invocation/5ddcad31-96d6-49f3-9978-e44286ed97d1).

The persisted module adds its provenance header, direct owner imports,
and this focused catalog. Aggregate publication validation is separate
from the targeted proof check; the checkpoint result is the authority for
the eventual commit and push.

The source includes guarded axiom checks for the matrix decomposition,
the saturation equivalence, the moving-tail theorem, and the conditional
RH consumer. Each permits exactly the standard Lean axioms
propext, Classical.choice, and Quot.sound. The publication checkpoint
also audits source and validates the aggregate project with Bazel and
BuildBuddy before committing or pushing.

## Constant-mode continuation: the requested zero limit is still open

Source: the user's request to perform the retained-head obligation, 13 November 2026.
Write f_n=candidate n, s_n=saturation n, and P_L=conditionalProjection L.
The normal equations give <1,f_n>_Q=s_n. Every positive CRT cell contains 1,
so <1,P_L f_n>_Q=s_n as well. Orthogonal separation of the constant mode gives

    headEnergy L n = (1-s_n)^2 + ||P_L f_n - s_n 1||_Q^2.

This is head_constant_mode_exact. Together with the complete head/tail split,
head_constant_mode_bounds proves, for EVERY L>0 and n,

    (1-s_n)^2 <= headEnergy L n <= 1-s_n.

No nesting, exhaustion, asymptotic rate, or RH premise enters these identities.
Thus a finite certificate headEnergy L n <= epsilon controls the full squared
approximation error 1-s_n by sqrt(epsilon). Both the constant-mode remainder
and the omitted CRT energy are retained in their respective exact identities.

The new one_mem_of_cofinal_head_small and
riemannHypothesis_of_cofinal_head_small require only

    for every epsilon>0 and N, there are n>=N and L>0
    with headEnergy L n < epsilon.

The cutoff L may depend on the certificate. It need not belong to a nested or
divisor-exhaustive tower. The proof takes the limit of (1-s_n)^2 along arbitrarily
late small certificates and obtains ||defect||_Q^4=0.

This is a conditional research reduction, not a provider for small certificates.
The cofinal retained-head condition is exactly equivalent to the existing
inverse-Gram saturation condition and to membership of one in the closed full
legal residue span. Cutoff freedom and cofinal quantifiers provide no new
arithmetic estimate. The requested retained-head zero limit remains Open.

The attempted CRT-only proof stops at the constant component: decreasing omitted
energy cannot force 1-s_n to vanish. Ambient density of CRT cells and reciprocal
density of the residues do not supply that arithmetic assertion. The focused next
attempt is a rigorous complete-Gram certificate family with arbitrarily small
headEnergy; neither a finite numerical table nor a claim of invariant legal
closure supplies such a family.

Verification: the coherent named-theorem candidate is checked separately from
publication. The terminal publication checkpoint identifies the final source
revision and validates the whole project. No unfinished proofs or new axioms are
introduced.

## Retained-head criterion audit and exact converse

Source: the user's audit of commit 62f6997, 13 November 2026.
Let e_n=1-s_n=||1-f_n||_Q^2, let tau_(L,n)=c_n^T tailGram(L,n)c_n,
and let v=Pi_V 1. The cutoff-one formulas give

    cellSpace(1) = span{1},
    P_1 f = <f,1>_Q 1,
    P_1 f_n = s_n 1,
    headEnergy(1,n) = e_n^2,
    tau_(1,n) = s_n e_n.

Consequently the published cofinal-head hypothesis is equivalent to s_n -> 1
and to 1 in V. More strongly, for EVERY prescribed sequence L_n>0,

    headEnergy(L_n,n) -> 0  iff  s_n -> 1.

There is no nesting or exhaustion hypothesis in this equivalence. Excluding
L=1 therefore does not change the zero-limit obligation. The original
conditional RH theorem remains valid; no unconditional RH conclusion or
RH-to-density converse is asserted.

### Further unconditional identities

For every L>0, the complete energy accounting is

    headEnergy(L,n) = e_n^2 + ||P_L f_n-s_n 1||_Q^2,
    ||P_L f_n-s_n 1||_Q^2 + tau_(L,n) = s_n e_n.

For L|M and M>0, refinement gives

    headEnergy(M,n) = headEnergy(L,n) + ||P_M f_n-P_L f_n||_Q^2.

Every positive-cutoff head energy is strictly positive at a finite stage.
For n>0, orthogonality of the residual to g_2 gives the exact parity formula

    P_2(1-f_n) = 4e_n qDivisor(2),
    headEnergy(2,n) = 4e_n^2.

Thus 4e_n^2 <= headEnergy(L,n) <= e_n when 2|L and L>0, and
3/4 <= s_n < 1 for n>0. These statements do not decide the limiting gap.

Along the previously specified nested divisor-exhausting towers,

    ||P_(L_n) f_n-s_n 1||_Q^2 -> ||v||_Q^2 ||1-v||_Q^2.

Together with the unconditional tail limit zero and head limit ||1-v||_Q^2,
this identifies the possible nonzero limiting energy without discarding it.

### Declaration map for the audit

The first row belongs to QCRTFiniteCollocation; all other rows belong to
QCRTGramSaturation.

| Declarations | Statement/status |
| --- | --- |
| cellSpace_one; conditionalProjection_one | Exact constant-cell space and mean projection. |
| candidate_projection_one; headEnergy_one; tailEnergy_one | Exact one-cell optimizer formulas with the complementary energy retained. |
| centered_head_tail_exact | Complete nonconstant-head plus omitted-tail variance identity. |
| headEnergy_one_le | The one-cell cutoff attains the smallest positive-cutoff retained error. |
| cofinal_head_small_iff_saturation; cofinal_head_small_iff_one_mem | Exact equivalence with saturation and legal closure membership. |
| headEnergy_tendsto_zero_iff_positive | Same zero-limit obligation for every prescribed positive cutoff sequence. |
| headEnergy_refinement_exact; headEnergy_mono_of_dvd | Exact refinement square and its monotonicity consequence. |
| headEnergy_pos | Strict positivity at every finite stage and positive cutoff. |
| residual_projection_two; headEnergy_two | Exact two-cell residual and retained error. |
| even_cutoff_head_bounds; saturation_bounds | Sharper even-cutoff bounds and 3/4 <= s_n < 1 for n>0. |
| centered_head_tendsto | Unconditional limit to ‖v‖²_Q ‖1-v‖²_Q on exhaustive towers. |

### A separate nondegenerate arithmetic provider remains Open

Prime-power exhaustion is essential for the ambient tail theorem. An LCM tower
L_m=lcm(1,...,m) admits every prime-power depth and composite divisor; squarefree
primorial cutoffs do not. All coefficients and Gram entries must still use the
complete physical Q measure, and G=headGram+tailGram must remain the matrix
being inverted.

For the actual optimizers, the missing estimate is exactly

    1-b_n^T G_n^(-1)b_n -> 0.

An independently proved vanishing bound for the centered retained energy on
an exhaustive tower would also suffice, because the complete omitted tail
already tends to zero and the limiting saturation is at least 3/4.

The explicit canonical collocation lifts F_L are a different family:

    P_L F_L = 1-qDivisor(L),
    ||1-P_L F_L||_Q^2 = L^(-2),
    ||1-F_L||_Q^2 = L^(-2)+leakage(L),
    ||F_L||_Q^2 = 1-L^(-2)+leakage(L).

Their visible errors already vanish, but they need not satisfy the optimizer
normal equations. They cannot be substituted into the optimizer criterion.
The complete leakage is the full Jordan-weighted sum over all wavelets whose
conductors do not divide L, including excessive powers of primes already present.

QCRTBoundedCriterion.riemannHypothesis_of_bounded_lcm_leakage consumes a uniform
bound on this complete leakage along a cofinal LCM subsequence. The weaker
cofinal subpower norm-growth condition in QCRTZeroGrowth is another sufficient
provider. Neither arithmetic bound is proved by this audit.

A uniform inverse bound for every CRT target cannot supply the missing estimate:
QCRTInverseInstability.eventually_exists_unstable_trial rules out such a fixed
bound along every cutoff sequence tending to infinity. A successful argument
must control the actual canonical right-hand side and LCM arithmetic.

The conditional theorem has no circular proof body. Using saturation or equivalent
closure membership to establish its head-smallness hypothesis, then presenting
the conclusion as an independent proof of saturation, would be circular.

### Audit verification and publication scope

All 18 named review declarations passed an ephemeral Bazel/BuildBuddy check
against commit 62f6997, with guarded result axioms restricted to propext,
Classical.choice, and Quot.sound:

- Job: job_Jc0hdGeu114vDbikW7Id4EhOYF6nmjWH.
- Verification duration: 58.291 seconds, excluding transport and polling delays.
- [BuildBuddy invocation](https://app.buildbuddy.io/invocation/acc908db-04d6-4d97-bd50-f2eeec9ab4dc).
- Reviewed source SHA-256:
  eec9ee079a2c44231ce1a1266f3a3935bd6568bd0b8eadb760b2bf0c7674be10.

The persisted declarations remove the temporary _audit suffix, add provenance
and descriptions, and place general projection lemmas in their owning module.
The publication checkpoint separately validates the full resulting project
and any integration with newer main before committing and pushing.
