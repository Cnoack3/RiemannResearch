# Squarefree capacity and energy certificates: Lean audit and research continuation

Date: 24 October 2026 (America/Los_Angeles).

Source: the user-provided `RH_Kappa_Capacity_and_Energy_Certificates_Chat_2026-10-24(1).md`, checked against RiemannResearch at base commit `27430c09b8b223c6e70a7c5da7b6471cdcadf69e`.

## Outcome

The attachment's central distinctions are correct. Its existing monotonicity, finite strict bounds, conditional RH implication, and crude-certificate obstruction were audited in Lean. The research proposals were pursued through exact signed arithmetic tails, refinable complete-energy certificates, actual finite squarefree packet legality, signed correlation criteria, and relative-gain saturation.

**Neither squarefree capacity saturation nor unconditional RH has been proved.** The new work removes a certificate-quality problem, closes finite legality interfaces, and proves reciprocal-mass divergence for consecutive heads. It does not provide the signed-correlation decay or inverse-Schur growth needed to finish RH.

All energy statements below use the complete Pareto norm, with
\[
P(n)=\frac1{n(n+1)},\qquad n\ge1.
\]
The Q-defined arithmetic functions are transferred to P with their coordinates preserved. Equality of P and Q norms is neither used nor asserted.

## 1. Audit of the supplied note

For the actual squarefree cutoff dictionary
\[
D_j=\{q:2\le q\le j+1,\ q\text{ squarefree}\},
\]
the existing `SquarefreePacketCapacity` module establishes
\[
0<\kappa_j<1\ (j\ge1),\quad
\kappa_j\uparrow\kappa_\infty\le1,\quad
\|1-p_j\|_P^2=1-\kappa_j.
\]
Increasing means nondecreasing: nonsquarefree cutoffs repeat. The checked implication is squarefree saturation implies Mathlib's `RiemannHypothesis`; no converse provider for squarefree saturation is supplied.

The existing amplitude certificates along the specified geometric selector have summable reciprocals. This says nothing comparable about reciprocals of actual energies. In particular, an upper bound larger than \(4^j\) is not a lower bound on the true error.

The normalized sampling identity remains
\[
\|1-F_{D,T}\|^2=\kappa_D^{-1}-1+
\|F_{D,T}-F_{D,\infty}\|^2.
\]
Its finite Gram and normalization hypotheses must hold. Exact source sampling eliminates the final term but leaves the capacity defect. The repository's target identification for these actual packets is already proved: `source_eq_cross` and `packet_inner_one` identify the source with \(\Lambda(q)\). It should not be listed as an unresolved target-direction assumption for this dictionary.

The actual horizontal-density/energy estimate needed by the sampled-signal rate remains an explicit analytic input. The full-conductor RH-converse theorem retains `RiemannHypothesis → BaezDuarte.NaturalApproximation`; it does not silently discharge the squarefree problem.

## 2. Proposal 1: complete signed-tail energy estimates

Write
\[
a_N=\sum_{d\le N}\frac{\mu(d)}d,\qquad
G_{N,q}=-\sum_{d\le N}\mu(d)g_d+q a_Ng_q,
\quad r_{N,q}=G_{N,q}-1.
\]
The new `PrimeBalancedSignedTail.lean` proves the exact floor identity, with the linear terms canceled:
\[
G_{N,q}(n)=\sum_{d\le N}\mu(d)\lfloor n/d\rfloor
-q a_N\lfloor n/q\rfloor.
\]
For \(n\ge N\), \(n>0\), \(q>0\), it proves the full residual identity
\[
r_{N,q}(n)=-\sum_{N<d\le n}\mu(d)\lfloor n/d\rfloor
-q a_N\lfloor n/q\rfloor.
\]
Using the repository's existing finite floor-tail reindexing theorem, the same residual is
\[
-\sum_{j=1}^{\lfloor n/(N+1)\rfloor}
\sum_{N<d\le\lfloor n/j\rfloor}\mu(d)
-q a_N\lfloor n/q\rfloor.
\]
These are actual arithmetic identities, not Hilbert-space countermodels. The anchor correction and all signed increments remain present.

For \(N<n<q\) and \(n<2(N+1)\), this specializes to the formerly informal first-window statement
\[
r_{N,q}(n)=M(N)-M(n).
\]
The theorem keeps both range conditions explicit; it does not invoke Bertrand's theorem. A first-window formula alone gives no upper bound for the entire energy.

### Refinement of the complete-energy certificates

Let \(q_N\) be the least prime above \(N\), \(U_N=N+q_N\), and
\[
E_N=\|G_{N,q_N}-1\|_P^2.
\]
For each finite numerical cutoff \(K\), define
\[
C_N(K)=\sum_{n=1}^K\frac{r_{N,q_N}(n)^2}{n(n+1)}
+\frac{U_N^2}{K+1}.
\]
For \(K\ge N\), the summands through \(N\) vanish. `ParetoAmplitudeCertificates.lean` proves the exact gap and step formulas
\[
C_N(K)-E_N=\frac{U_N^2}{K+1}
-\sum_{n>K}\frac{r_{N,q_N}(n)^2}{n(n+1)},
\]
\[
C_N(K+1)-C_N(K)=
\frac{r_{N,q_N}(K+1)^2-U_N^2}{(K+1)(K+2)}\le0.
\]
Consequently,
\[
E_N\le C_N(K)\le E_N+\frac{U_N^2}{K+1},
\qquad C_N(K)\downarrow E_N.
\]
The numerical condition \(U_N^2\le\varepsilon(K+1)\) certifies error at most \(\varepsilon\). The finite sums have rational arithmetic inputs. The statements expose a finite evaluation procedure, but no claim is made that evaluating very large selected heads is computationally cheap.

For the integer cutoff \(K=U_N^2\), put
\[
B_N=\max\{1,C_N(U_N^2)\}.
\]
Then the checked bounds are
\[
\boxed{\max(1,E_N)\le B_N\le2\max(1,E_N).}
\]
For **every** sequence of positive heads \(N_j\), the new arithmetic specialization proves
\[
\sum_jB_{N_j}^{-1}<\infty
\quad\Longleftrightarrow\quad
\sum_j\max(1,E_{N_j})^{-1}<\infty.
\]
Thus finite certified upper bounds can preserve regularized actual reciprocal mass. The earlier certificate obstruction concerned the unrefined tail bound evaluated at the physical head; it is not an unavoidable obstruction to certified computation.

**Still open:** divergence of the actual regularized reciprocal mass along the geometrically sparse selector. For consecutive heads, the dense-head argument in Section 3 discharges mass divergence unconditionally; its signed-correlation decay remains open.

### Actual finite packet legality

`PrimeHeadRefinedCertificates.lean` identifies the complete P energy with the norm of the transferred arithmetic trial. `SquarefreePrimeHeadStage.lean` uses the exact divisor packet identity and squarefree divisor closure to prove
\[
G_{N,q_N}\in V_{q_N-1}.
\]
It follows that every finite refinement certifies
\[
\boxed{\kappa_{q_N-1}\ge1-C_N(K).}
\]
This uses the nonregularized certificate: the regularization \(B_N\ge1\) is useful for averaging but would give only a trivial capacity lower bound.

## 3. Proposal 2: signed correlations and mass retention

Let \(u_i=F_i-1\) be complete Hilbert residuals, and let positive certificates satisfy \(\|u_i\|^2\le A_i\). Put
\[
S_M=\sum_{i<M}A_i^{-1},\qquad
\overline u_M=S_M^{-1}\sum_{i<M}A_i^{-1}u_i,
\]
\[
D_M=S_M^{-2}\sum_{i<M}A_i^{-2}\|u_i\|^2,
\qquad
X_M=\frac2{S_M^2}\sum_{i<j<M}
\frac{\langle u_i,u_j\rangle}{A_iA_j}.
\]
`NormalizedSignedEnergy.lean` proves the exact identity and bound
\[
\boxed{\|\overline u_M\|^2=D_M+X_M,\qquad0\le D_M\le S_M^{-1}.}
\]
For \(S_M\to\infty\), it proves
\[
\boxed{\overline u_M\to0\quad\Longleftrightarrow\quad X_M\to0.}
\]
It is enough to have an eventual signed upper budget \(X_M\le b_M\) with \(b_M\to0\). There is no requirement that the unnormalized cross sum remain bounded, and negative correlations are not replaced with absolute values.

For actual squarefree legal trials, `SquarefreeSignedCorrelationCriterion.lean` proves
\[
X_M\ge1-\kappa_\infty-S_M^{-1}\qquad(M>0).
\]
Together with reciprocal-mass divergence and the vanishing signed budget, it gives squarefree saturation and RH. The legality is the actual finite packet legality; all arithmetic mass and correlation hypotheses remain visible.

The distinction matters: reciprocal mass alone is insufficient. For the note's nonarithmetic exact-head model, \(r_N=(N+1)\mathbf1_{n>N}\), direct computation gives
\[
\langle r_N,r_M\rangle_P=\min(N,M)+1.
\]
With heads \(N_j=j\), the reciprocal mass is harmonic, but its averaged error is
\[
\frac{2M-H_M}{H_M^2}.
\]
The exact-head, zero-mean, energy, and covariance identities are formalized in `CountermodelExactHeads.lean`. The displayed harmonic-average simplification is ordinary finite-sum algebra. This remains a nonarithmetic example; legal-span membership is not asserted.

### A concrete improvement: use every head and harmonic weights

`DensePrimeHeadSignedCriterion.lean` applies Mathlib's Bertrand theorem to prove
\[
q_N\le2N,\qquad E_N\le\frac{(N+q_N)^2}{N+1}\le9N\quad(N\ge1).
\]
Thus the simple complete-energy certificates \(A_N=9N\) give
\[
S_M=\sum_{N=1}^M\frac1{9N}=\frac{H_M}{9}\longrightarrow\infty.
\]
This mass divergence is unconditional. There is no geometric subsequence and no data-dependent optimization. The resulting explicit legal trial is
\[
\boxed{F_M=\frac1{H_M}\sum_{N=1}^M\frac{G_{N,q_N}}N.}
\]
Its complete residual decomposition has
\[
\|F_M-1\|_P^2=D_M+X_M,\qquad
0\le D_M\le\frac9{H_M},
\]
\[
X_M=\frac2{H_M^2}\sum_{1\le N<L\le M}
\frac{\langle G_{N,q_N}-1,G_{L,q_L}-1\rangle_P}{NL}.
\]
Therefore this concrete construction converges in complete P norm **if and only if** \(X_M\to0\); the new actual-family RH consumer only requires a vanishing eventual upper budget for this signed term. No reciprocal-mass hypothesis remains in that consumer.

The available unsigned estimates do not prove the needed decay. The checked exact-head pairing inequality, together with \(U_N\le3N\) and \(E_L\le9L\), gives only \(|\langle r_N,r_L\rangle|\le9N\) for \(N<L\). Summing this comparison yields an upper bound \(18(M-H_M)/H_M^2\), which does not vanish. This comparison is ordinary algebra using the verified inequalities; no signed term has been proved negligible by it.

The refined certificates also satisfy \(B_N\le18N\), so their reciprocal mass diverges for consecutive heads as well. Their associated signed cross terms use different weights and must be estimated separately.

**Still open:** prove normalized signed-correlation decay for either dense-weight construction. The original sparse selector already controls correlations but has an unresolved true-mass problem; the dense selector has proved mass divergence but an unresolved correlation problem. Neither result can be substituted into the other construction without checking that the same heads and weights are used.

## 4. Proposal 3: inverse-Schur relative gains

`RelativeGainSaturation.lean` proves a finite quantitative result. If \(\kappa_n\) is nondecreasing, \(b_j\ge0\), and
\[
b_j(1-\kappa_j)\le\kappa_{j+1}-\kappa_j,
\]
then
\[
(1-\kappa_N)\left(1+\sum_{j<N}b_j\right)\le1-\kappa_0.
\]
For the actual squarefree capacities, `SquarefreeRelativeGainCriterion.lean` defines
\[
\beta_j=\frac{\kappa_{j+1}-\kappa_j}{1-\kappa_j}\in[0,1)
\]
and proves
\[
1-\kappa_N=(1-\kappa_0)\prod_{j<N}(1-\beta_j),
\qquad
\boxed{\kappa_N\to1\iff\neg\operatorname{Summable}(\beta).}
\]
The infinite-product analysis reuses the existing generic residual-gain theorem. The new specialization also gives
\[
(1-\kappa_\infty)\sum_{j<N}\beta_j
\le\kappa_\infty-\kappa_0.
\]
A positive limiting defect therefore bounds every partial relative-gain sum. The lower-bound consumer permits arbitrary monotone blocks of actual squarefree cutoff stages, not only adjacent conductors.

For a block Schur complement, the required arithmetic input is still
\[
\eta_j^TS_j^{-1}\eta_j\ge b_j(1-\kappa_{D_j}),
\qquad \sum_jb_j=\infty.
\]
No such unconditional arithmetic provider was obtained. Source sparsity and strict positivity of individual gains are insufficient.

The note's abstract countermodel admits a transparent finite calculation. Set \(A=1+b^2\) and
\[
t=d^{-2}+\sum_{q>2}(\Lambda(q)-d^{-1})^2.
\]
For the finite model dictionary, \(\kappa=t/(1+At)\). Every composite increases \(t\) by \(d^{-2}\), yielding a positive gain, while the limiting capacity remains \(1/A<1\). This ordinary calculation concerns a different Gram matrix and supplies no counterexample to the actual arithmetic saturation problem.

## 5. Proposal 4: provider and inference ledger

| Item | Status after this continuation |
|---|---|
| Actual packet target source equals \(\Lambda\) | Established already; checked source/API. |
| Q-to-P coordinate transfer | Established already; used explicitly. |
| Prime-balanced trial belongs to an exact finite squarefree packet stage | New formal assembly. |
| Exact floor tail and first Mertens window | New formal arithmetic identities. |
| Arbitrarily accurate complete-energy upper certificates | New formal result. |
| Preservation of regularized reciprocal mass by finite certificates | New formal result. |
| Normalized signed cross criterion | New formal exact criterion; arithmetic budget remains Open. |
| Squarefree relative-gain nonsummability criterion | New formal specialization; actual nonsummability remains Open. |
| Reciprocal mass for consecutive heads, A_N=9N or refined B_N | New unconditional divergence theorem. |
| Actual reciprocal-energy divergence after the geometric sparse selector | Open. |
| Actual inverse-Schur relative-gain lower bound with divergent mass | Open. |
| Actual horizontal-density/energy input for sampled-signal rates | Open in the audited sampling theorem. |
| RH implies full natural approximation | Explicit analytic provider in the existing converse. |
| RH implies squarefree packet saturation | No provider supplied. |
| Unconditional RH | Not proved. |

The proposed examples \(E_j\le C(j+1)\) must refer to the selected-head index \(j\), not to an unselected physical-head bound \(E_N\le CN\). None of the new results substitutes the latter for the former.

## 6. Literature context and next research targets

Báez-Duarte's strengthened Nyman–Beurling theorem supplies a classical approximation equivalence, not an unconditional proof of saturation: https://arxiv.org/abs/math/0202141.

His *Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis*, equation (1.14) and Proposition 4.6, proves nonconvergence in L² of the entire canonical balanced sequence: https://arxiv.org/pdf/math/0011254. Ordinary algebra identifies the canonical anchor \(q=N+1\) with the negative of its \(B_{N+1}\); the balanced functions are constant on reciprocal unit intervals. This contextual observation is not a new Lean theorem. It does not establish failure of the least-prime family, a selected subsequence, or signed averages.

The next substantive targets are now more precise:

1. Estimate the **whole signed residual** inside the complete energy, preserving the anchor correction. The first Mertens window alone is insufficient.
2. Use \(C_N(K)\) for finite certified experiments and \(B_N\) for averaging. For the sparse selector, seek bounds on its actual energies; for consecutive heads, mass divergence is already proved.
3. Prioritize the concrete harmonic-weight cross term above: its mass divergence is already discharged. Prove \(X_M\le b_M\to0\). Pairwise absolute decorrelation is stronger than required.
4. Alternatively, establish a genuine arithmetic inverse-Schur lower bound with divergent relative-gain mass. The newly checked equivalence only identifies the target.

## Verification record

The initial audit job `job_LKB8nqIFsBn3ieAneM-8_pspWIsRVH4C` succeeded (reported verification time 10.888 seconds), with principal existing axiom lists containing only `propext`, `Classical.choice`, and `Quot.sound`.

The first combined certificate/arithmetic snippet succeeded in `job_vehbSSEKGN1GkMrcEbeIimNdvyYAK8Ql` (7.026 seconds). Subsequent combined checks repaired elaboration details and formula parentheses; failed tactic attempts were not treated as mathematical refutations.

All nine initial saved modules passed server import/build and principal axiom audits in `job_X0v8KWtrTvy5ygeL09OBy69DSGT6t9ti` (20.753 seconds). The dense-head specialization and exact harmonic-average identity passed `job_KNiSGTGiU0bXehvqCO5pLExRIMAfq0tY` (6.824 seconds). Saved-file compilation and final integration are covered by the checkpoint.

Saved-module verification and publication are performed on the Lean server. Both final saved modules passed `job_Wt-iqbjhiqsp1XNkkFLk0nBAnHzWC6I1` (14.460 seconds), including the dense-harmonic RH consumer's exact hypothesis type and standard axiom audits. All 11 new modules are exported from the project root. The terminal checkpoint job, its scope, and the published commit are reported in the conversation's final response. No open analytic hypothesis is presented as an axiom-free provider merely because its conditional consumer passes Lean.

Workspace opening was not separately instrumented. Queue/polling wall time and reported verification duration are distinct; no hardware cause is inferred for tool latency.

The reusable-declaration and open-obligation ledger is [THEOREM_CATALOG_CAPACITY_20261024.md](../THEOREM_CATALOG_CAPACITY_20261024.md), a dated catalog addendum.
