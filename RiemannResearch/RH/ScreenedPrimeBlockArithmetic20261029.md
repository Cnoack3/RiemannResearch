# Actual screened CRT blocks: basis, inverse-Gram sources, and arithmetic bounds

**Date:** 29 October 2026
**Starting checkpoint:** 1b2162038f5f78f47eb7d1e33586f65429821b31
**Source agenda:** RH_Capacity_Increment_Research_Agenda_2026-10-29(1).md
**Status:** the actual screened-basis interface and three inverse-Gram identities are now proved in Lean. New unconditional complete-Q energy bounds are proved for the actual screened conductor family. The subpolynomial growth provider remains **Open**. RH is not proved.

The starting checkpoint was compared with repository main and was identical when work began. This memorandum accompanies the new source, exported through RiemannResearch.lean. Publication is gated on the server checkpoint's required validation.

## 1. What has changed

| Result | Status and source |
|---|---|
| Independence of the combined old and newly added compensated family | Lean: QResidueHeadExtension.combined_independent |
| Exact enlargement of the old head-zero tangent | Lean: QResidueHeadExtension.tangent_extension |
| Screened independence and the entire innovation span | Lean: QResidueHeadExtension.screened_added_independent, screened_added_span |
| All hypotheses discharged for the actual dense schedule | Lean: QCRTInnovationBlock.block_independent, block_span |
| Physical next-site observation identified with the Gram source | Lean: QCRTInnovationBlock.block_observation |
| Actual gain, innovation capacity, and prediction shift as inverse-Gram forms | Lean: gain_inverseGram, capacity_inverseGram, prediction_inverseGram |
| Complete signed transition in those sources | Lean: dense_block_transition |
| Old-capacity square completion | Lean: dense_old_capacity_completion; explicitly assumes squarefree next site and nonzero old and innovation capacities |
| An old short prime anchor, with no unproved existence hypothesis | Lean: QCRTPrimeInnovation.exists_old_prime_anchor and shortAnchor_spec; uses Mathlib Bertrand |
| Exact invariance under replacing the primorial anchor by that short anchor | Lean: screened_anchor_change |
| Complete column and full-divisor trace upper bounds | Lean: screened_energy_bound, screened_energy_le_four, screened_trace_bound |
| Quantitative collapse of the ratio of screened to raw energy | Lean: actual_raw_energy_lower and actual_screening_ratio |
| No uniform positive lower angle for the raw primorial-anchor family | Paper consequence in Section 5, using the checked finite inequality and an elementary primorial-growth argument |
| Dyadic refined-budget estimate or subpolynomial complete optimizer energy | **Open** |

The new basis theorem is stronger than a prime-step-only statement: it works at every dense stage, including an empty added block.

## 2. Exact objects, with no change of optimizer

Use the complete real Hilbert space
\[
Q(m)=\frac1{\zeta(2)m^2},\qquad
g_d(m)=\frac{m\bmod d}{d}.
\]
Put
\[
n=i+2,\quad p=2i+3,\quad L=\mathfrak P(2i+2),\quad
L^+=\mathfrak P(2i+4).
\]
Keep the original actual minimum-norm exact-head vectors
\[
F_i=\operatorname{minimumAt}(2i,i+1),\qquad
Z_i=\operatorname{minimumAt}(2i+2,i+1).
\]
Write
\[
T^- = U_i\cap\{f:f(1)=\cdots=f(i+1)=0\},\qquad
T^+ = U_{i+1}\cap\{f:f(1)=\cdots=f(i+1)=0\},
\]
and
\[
W_i=T^+\cap(T^-)^\perp.
\]

The formal index set is exactly
\[
J_i=\{m>1:m\mid L^+\}\setminus\{m>1:m\mid L\}.
\]
For \(m\in J_i\), define
\[
z_m=g_m-\frac Lm g_L,\qquad x_m=(I-P_{T^-})z_m.
\]

At a prime enlargement, \(L^+=pL\), \(p\nmid L\), and elementary divisor arithmetic reindexes \(J_i\) as \(m=pd,\ d\mid L\). Thus this is the agenda's family, including \(d=1\). The Lean basis and Gram theorems use the exact conductor difference directly; they do not rely on an assumed prime-block reindexing.

### Proof of the basis assertion

Every newly admitted conductor exceeds the old head. Indeed, it is squarefree, and if it were at most \(i+1\), it would already divide the old primorial. This arithmetic fact is discharged in added_gt_head.

The existing compensated-basis theorem gives a linearly independent family for the entire new zero-head tangent. Splitting its conductor indices into old and newly admitted indices yields
\[
T^+=T^-\mathbin{\dot+}\operatorname{span}\{z_m:m\in J_i\}
\]
as an algebraic direct sum. Screening kills the old summand and is injective on the new summand. Moreover its image is precisely \(W_i\): if \(x=u+z\in T^+\) is orthogonal to \(T^-\), then
\[
x=(I-P_{T^-})x=(I-P_{T^-})z.
\]
Therefore the \(x_m\) are independent and span \(W_i\).

Lean proves both assertions, with every actual-family inclusion and head condition supplied. This is not merely positive definiteness assumed in a theorem type.

## 3. The actual three sources and the full signed transition

Let \(k_i\) be denseNormal, and let
\[
\ell_i=(I-P_{T^-})k_i,\quad h_i=\|\ell_i\|_Q^2,\quad
K_i=\|P_{T^-}k_i\|_Q^2,\quad \kappa_i=K_i+h_i.
\]
Let \(D_i=F_i-Z_i\), \(G_i=\|D_i\|_Q^2\),
\(a_i=1-F_i(n)\), and \(b_i=1-Z_i(n)\).
Set
\[
B_{me}=\langle x_m,x_e\rangle_Q,\qquad
c_m=x_m(n),\qquad f_m=\langle x_m,F_i\rangle_Q.
\]

The proofs identify the actual projections
\[
P_{W_i}k_i=\ell_i,\qquad P_{W_i}F_i=D_i.
\]
For the second identity, \(D_i\in W_i\), while \(F_i-D_i=Z_i\) is orthogonal to the entire new old-head tangent. The first is the corresponding nested-subspace projection identity.

Finite Gram projection theory now gives the checked equalities
\[
\boxed{
h_i=c^\top B^{-1}c,\qquad
G_i=f^\top B^{-1}f,\qquad
b_i-a_i=c^\top B^{-1}f.
}
\]
The physical observation \(c_m=x_m(n)\) is separately verified by block_observation.

If \(n\) is squarefree, the complete signed transition becomes
\[
\boxed{
E_{i+1}-E_i=
\frac{(a_i+c^\top B^{-1}f)^2}{K_i+c^\top B^{-1}c}
-f^\top B^{-1}f.
}
\]
This is dense_block_transition. No unobserved part of the gain is dropped. At nonsquarefree sites the previously checked transition remains \(-G_i\).

The agenda's alternative completion is also installed:
\[
E_{i+1}-E_i=
\frac{a_i^2}{K_i}
-\frac{(K_i b_i-\kappa_i a_i)^2}{K_i h_i\kappa_i}
-\|R_i^{\rm new}\|_Q^2.
\]
Its declaration explicitly assumes \(K_i\ne0\) and \(h_i\ne0\), as well as squarefreeness. The earlier zero-capacity-safe transition remains available and is not replaced by this conditional rearrangement.

## 4. Unconditional arithmetic control of the screened family

Bertrand supplies, for every \(i\ge0\), a prime \(r_i\) with
\[
i+1<r_i\le2i+2=p-1.
\]
This is an old legal conductor: \(r_i\mid L\). Also \(L>i+1\).

For any positive conductor \(m\), the exact anchor-change identity is
\[
\left(g_m-\frac Lm g_L\right)
-\left(g_m-\frac{r_i}{m}g_{r_i}\right)
=-\frac Lm\left(g_L-\frac{r_i}{L}g_{r_i}\right).
\]
The right side belongs to the actual old tangent \(T^-\). Consequently
\[
\boxed{
(I-P_{T^-})\left(g_m-\frac Lm g_L\right)
=(I-P_{T^-})\left(g_m-\frac{r_i}{m}g_{r_i}\right).
}
\]

The long anchor can therefore be removed *before estimating the norm*. The underlying screened vector and its Gram matrix are unchanged.

For \(m,r\ge2\), pointwise nonnegativity of residue atoms gives
\(\langle g_m,g_r\rangle_Q\ge0\). Retaining the exact norm expansion first,
\[
\left\|g_m-\frac rm g_r\right\|_Q^2
=\|g_m\|_Q^2+\frac{r^2}{m^2}\|g_r\|_Q^2
-\frac{2r}{m}\langle g_m,g_r\rangle_Q.
\]
The existing complete-Q estimate
\(\|g_d\|_Q^2\le2/(\zeta(2)d)\) then yields
\[
\left\|g_m-\frac rm g_r\right\|_Q^2
\le \frac2{\zeta(2)m}+\frac{2r}{\zeta(2)m^2}.
\]

Taking \(m=pd\), \(d\ge1\), and using orthogonal contraction proves
\[
\boxed{
\|x_d\|_Q^2
\le\frac2{\zeta(2)pd}+\frac{2r_i}{\zeta(2)p^2d^2}
\le\frac4{\zeta(2)pd}.
}
\]
Here \(x_d\) denotes the same screened vector with the prime-block indexing.
The finite estimate is proved even without assuming \(p\) prime; primality identifies these columns with the enlargement.

Summing the entire old divisor family, including \(d=1\), gives
\[
\boxed{
\sum_{d\mid L}\|x_d\|_Q^2
\le\frac4{\zeta(2)p}\sum_{d\mid L}\frac1d.
}
\]
The complete physical infinite tail is present in every norm. This is an upper bound for the full block trace at prime enlargements, not a physical-tail truncation.

**Localization caution.** The primorial-anchor raw direction vanishes up to \(\min(m,L)-1\); at prime stages with \(n\ge3\), this includes the prediction site. The short-anchor representative can have a nonzero value at \(n\), particularly when \(r_i=n\). Anchor invariance does not permit discarding this physical observation term. All checked source identities use the screened vector itself.

## 5. A quantitative obstruction to a uniform raw angle bound

For \(m,L\ge2\), the checked lower estimate is
\[
\boxed{
\left\|g_m-\frac Lm g_L\right\|_Q^2
\ge \frac{L-8m}{4\zeta(2)m^2}.
}
\]
To prove it, use
\(\|g_L\|_Q^2\ge1/(2\zeta(2)L)\),
the identity \((L/m)g_L=g_m-z_m\), and
\[
\|(L/m)g_L\|_Q^2
\le2\|g_m\|_Q^2+2\|z_m\|_Q^2.
\]
Combining the complete upper and lower residue estimates gives the result.

For the actual \(d=1\) column and \(L\ge16p\),
\[
\|z_1\|_Q^2\ge\frac L{8\zeta(2)p^2}>0,\qquad
\boxed{\|x_1\|_Q^2\le\frac{32p}{L}\|z_1\|_Q^2.}
\]
The latter is actual_screening_ratio.

Here is the additional **paper-level asymptotic consequence**. One has \(L/p\to\infty\), without using the prime number theorem. Fix a primorial \(C=\mathfrak P(M)\). For sufficiently large \(i\), the Bertrand prime \(r_i>i+1\) exceeds \(M\); thus \(C\) and \(r_i\) are coprime divisors of \(L\), so
\[
L\ge Cr_i\ge C(p+1)/2.
\]
Primorials \(C\) are unbounded by infinitude of primes. Hence \(L/p\to\infty\). This argument applies along the infinitely many odd-prime enlargement stages as well.

Thus no fixed \(\eta>0\) can satisfy
\[
\|(I-P_{T^-})z\|_Q^2\ge\eta\|z\|_Q^2
\]
for every raw new-prime direction at all sufficiently large enlargement stages. The checked \(d=1\) direction already obstructs it.

This does **not** rule out a useful estimate after changing coordinates, nor a bound for the specific signed sources. It rules out this particular uniform lower angle estimate relative to the raw primorial-anchor norm. It also explains why very large raw norms need not imply large screened energy.

## 6. What still blocks RH

The trace estimate is an upper spectral bound. It does not bound \(B^{-1}\) from above. Even the elementary matrices \(\operatorname{diag}(\varepsilon,1)\) have bounded trace and unbounded inverse as \(\varepsilon\downarrow0\). The actual sources may cancel or avoid small-eigenvalue directions, but that must be proved.

The unchanged sufficient hypothesis is
\[
\frac{\log(1+\widetilde S_N)}{\log(N+2)}\longrightarrow0.
\]
Its actual-family consumer remains
QCRTInnovationBudget.riemannHypothesis_of_subpolynomial_innovationBudget.
This session has not supplied that hypothesis.

A direct signed-energy route also remains possible: estimate the full expression in Section 3 over blocks, including nonsquarefree negative gains. The exact formula alone is not an estimate.

### Next research tasks

1. Use the proved basis and the short-anchor representatives to analyze the *joint* arithmetic sources \(f,c\), keeping the physical observation correction where required.
2. Normalize columns by \(\sqrt{pd}\) before asking for spectral estimates. With \(S=\operatorname{diag}(\sqrt{pd})\), set \(\widehat B=SBS\), \(\widehat f=Sf\), and \(\widehat c=Sc\). The three inverse-Gram quadratic/bilinear forms are unchanged. The checked column estimate bounds the normalized diagonal, but supplies no lower eigenvalue bound.
3. Seek source-dependent cancellation estimates for the actual signed block transition. Avoid demanding a uniform inverse bound for every source or a uniform angle for the raw large-anchor family.
4. Prove a dyadic estimate for the literal refined positive budget, or independently prove subpolynomial complete optimizer energy while retaining all signed gains. These remain **Open**.
5. Only after an arithmetic growth provider is checked should the existing RH consumer be specialized.

## 7. Verification and provenance

- Coherent candidate containing the actual basis, projections, and all three Gram identities: job_so1GHFQGK150TkfbDI-SPEo-hTUsUpSw, succeeded; server-reported duration 10.647 seconds.
- Saved-module imports, additional signed-transition candidate, and eight-declaration axiom audit: job_-iLrkzqsRypMOgx0nrOrnso5_tEb9Hmt, succeeded; server-reported duration 33.497 seconds, including dependency/module work.
- Audited axioms: only propext, Classical.choice, and Quot.sound.
- The additional signed-transition candidate was subsequently saved in QCRTInnovationBlock.lean. The final checkpoint validates the persisted source and aggregate project before publication.
- Workspace-opening request time and queue/polling delay were not separately measured. Reported server durations are not kernel-only timings.
- Wolfram independently simplified the scalar square completion and anchor coefficient identity to zero, and found no counterexample to the finite scalar inequalities used in the screening-ratio estimate. The Lean proofs are the verification evidence.
- No local project axiom, sorry, or admit was introduced. An axiom audit does not discharge hypotheses such as the remaining growth condition.

External reading was used for orientation, not as an unproved input to the new declarations:

- Werner Ehm, *On certain Gram matrices and their associated series* (2024), [arXiv:2405.06349](https://arxiv.org/abs/2405.06349). Provides related Nyman–Beurling Gram formulae and quadratic-form decompositions; no identity was transferred to discrete Q without proof.
- François Alouges, Sébastien Darses, Erwan Hillion, *Polynomial approximations in a generalized Nyman–Beurling criterion*, JTNB 34 (2022), 767–785, [doi:10.5802/jtnb.1227](https://numdam.org/articles/10.5802/jtnb.1227/). Related background on the distinction between approximation and coefficient control; not an arithmetic provider for this moving family.

The formalization is independently developed from the supplied agenda and existing project lemmas. No claim of mathematical novelty is made.
