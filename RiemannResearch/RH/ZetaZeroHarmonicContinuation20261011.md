# Zeta zero ordinate harmonic analysis: strengthened continuation
Date: 11 October 2026

## Recovery status — final integrated verification pending

The attached notes were read in full. Six focused Lean source modules with proof terms were preserved without sorry, admit, axiom, or unsafe declarations. Their archived source hashes were checked during recovery. The recovered candidates are being integrated with the other preserved developments; **final integrated server verification remains pending**. Absence of placeholders and successful file recovery are not kernel checks.

The Lean workspace opened successfully against repository commit c173f559e39c149116d0a56c5a6e230b069b668c. Repository-root AGENTS.md was read. One coherent sharp power-error candidate was submitted to the user's Lean server. It was accepted as a queued job:
job_Yts5GqrQN8pd_vOlrU6c3mRGXajDyhLX.
The original session last observed the job queued before transport timeouts. Recovery has now established its terminal state: the initial snippet failed with an addition-monotonicity proof error. That candidate has been repaired in the recovered source. During the original interrupted session no remote source mutation, checkpoint, or publication occurred; those statements describe that session, not a continuing queue blockage.

The verifier is accessible again. The recovered modules are prepared for integration in workspace `ws_hpqrnJbaPc0ZNyhBW2ywJ9K2VPm0t9rb`, based on `415a2c777f274bec07b7a19fadf089640c31f703`. A successful final checkpoint must validate the exact combined source before publication is reported. This document establishes the paper proofs below and identifies the intended Lean statements; it does **not** itself certify that checkpoint or the complete original notes.

## 1. Exact weighted-frequency variance, preserving the square

For a finite support \(I\), real weights \(r_i\), and real frequencies \(u_i\), define
\[
M_0=\sum_i r_i,\qquad M_1=\sum_i r_i u_i,\qquad M_2=\sum_i r_i u_i^2,
\qquad W=\sum_{i,j}r_i r_j(u_i-u_j)^2.
\]
The following equalities require no sign condition:
\[
\boxed{W=2M_0M_2-2M_1^2,}
\]
and for every real center \(c\),
\[
\boxed{W=2M_0\sum_i r_i(u_i-c)^2-2(M_1-cM_0)^2.}
\]
Expanding each square, distributing the finite sums, and collecting products proves both identities. Translation \(u_i\mapsto u_i+c\) leaves every difference unchanged and therefore leaves \(W\) unchanged.

Now suppose \(r_i\ge0\) and \(a\le u_i\le b\). Since
\[
(u_i-a)(b-u_i)\ge0,
\]
we obtain
\[
\left(u_i-\frac{a+b}{2}\right)^2\le\frac{(b-a)^2}{4}.
\]
Multiply by \(r_i\), sum, and substitute into the exact centered identity:
\[
\boxed{W\le\frac{(b-a)^2M_0^2}{2}
-2\left(M_1-\frac{a+b}{2}M_0\right)^2.}
\tag{A}
\]
This includes empty support and zero total mass; division by \(M_0\) is unnecessary. The coefficient \(1/2\) is sharp: equal mass at the two endpoints attains equality with vanishing center displacement.

For the notes' \(W_2(a)\), use \(r_i=|a_i|\), \(u_i=\log n_i\). If all nonzero indices lie in \(A\le n_i\le B\), where \(A>0\), (A) gives
\[
W_2(a)\le\frac{\log^2(B/A)}2\left(\sum_i|a_i|\right)^2
-2\left(\sum_i|a_i|\log n_i
-\frac{\log A+\log B}{2}\sum_i|a_i|\right)^2.
\]
Thus the leading sparse coefficient bound in Section 9.3 improves by a factor of two, and improves further when the weighted logarithmic mean is away from the interval midpoint. Common integer dilation of all support indices leaves the exact quantity unchanged.

**Analytic boundary.** Applying this to the actual covariance error still requires the entry estimate in equation (31), or the coefficient-specific estimate in (35). The draft finiteGramErrorPairing_norm_le_interval explicitly assumes an entrywise error estimate and a nonnegative quadratic coefficient. It does not prove a Landau formula or a Selberg density estimate.

The exact spread and centered identities are already present in the repository's FrequencySensitiveGramBounds.lean; they are reused rather than duplicated. The new interval refinement is drafted in FrequencySpreadInterval.lean, especially weightedFrequencySpread_le_interval_centered.

## 2. Sharp transfer of a Fourier error to every balanced power

For \(z,w\in\mathbb C\), \(e\ge0\), \(|z-w|\le e\), and any integer \(q\ge0\),
\[
\boxed{|z^q-w^q|\le(|w|+e)^q-|w|^q.}
\tag{B}
\]
Consequently,
\[
\boxed{\bigl||z|^q-|w|^q\bigr|\le(|w|+e)^q-|w|^q.}
\tag{C}
\]

**Proof.** Put \(b=|w|\) and \(D_q=(b+e)^q-b^q\). The case \(q=0\) is exact. Assuming (B) at \(q\), its nonnegative left side shows \(D_q\ge0\). Also \(|z|\le b+e\). Preserve the exact successor identity
\[
z^{q+1}-w^{q+1}=z(z^q-w^q)+(z-w)w^q.
\]
Its norm is at most
\[
(b+e)D_q+e b^q=(b+e)^{q+1}-b^{q+1}.
\]
This proves (B) by induction. Apply the reverse triangle inequality to \(z^q,w^q\) to prove (C).

For the notes' balanced Fourier coefficients, set \(z=Z_T(u)/T\), \(w=b_u\), and \(q=2r\). The sharper remainder is
\[
(|b_u|+e_T(u))^{2r}-|b_u|^{2r},
\]
rather than \(c_{2r}(|b_u|^{2r-1}e_T(u)+e_T(u)^{2r})\). All binomial terms are retained. In particular, for \(q=4\), the exact majorant is
\[
4b^3e+6b^2e^2+4be^3+e^4.
\]
For a mixed character with \(b_u=0\), it reduces exactly to \(e_T(u)^{2r}\). This is the harmonic reason balanced convolutions suppress mixed-character errors to higher order.

Drafts: BalancedPowerTransfer.lean and its actual-zero application in ActualZeroBalancedTuplePhase.lean. The actual-zero transfer statement explicitly assumes \(|Z_T(u)/T-b_u|\le e\).

## 3. Exact ordered balanced-tuple factorization

Let \(\iota\) be any finite occurrence type, including separate analytic multiplicity copies, and let \(z_i\in\mathbb C\). For \(r\ge0\), write \(t\in\iota^r\) for an ordered tuple and \(A_t=\prod_{k=1}^r z_{t_k}\). Then
\[
\sum_{t\in\iota^r}A_t=\left(\sum_i z_i\right)^r,
\]
and
\[
\boxed{\sum_{t,t'\in\iota^r} A_t\,\overline{A_{t'}}
=\left|\sum_i z_i\right|^{2r}.}
\tag{D}
\]
Finite distributivity proves the first identity. The second sum factors into the first sum times its conjugate. No repetitions or diagonals are deleted.

With \(z_i=e^{iu\gamma_i}\), (D) is the exact character coefficient for
\(\gamma_1+\cdots+\gamma_r-\gamma'_1-\cdots-\gamma'_r\).
Dividing by \(N^{2r}\) gives \(|Z_T(u)/N|^{2r}\) when \(N>0\). The draft's algebraic normalization also covers an empty occurrence type under Lean's division-by-zero convention; an empty sample has no probability interpretation.

The actual-zero application uses the existing repository Copies T and sum_eq_copies, so it retains the precise zeta multiplicities.

Drafts: BalancedTuplePhase.lean and ActualZeroBalancedTuplePhase.lean.

## 4. Sharp collision threshold and cofinal certificates

For a finite occurrence map \(f:\iota\to\mathbb R\), define
\[
C(f)=\sum_{i,j}\mathbf1_{f(i)=f(j)},\qquad
E(f)=\sum_{i\ne j}\mathbf1_{f(i)=f(j)},\qquad N=\#\iota.
\]
The exact identity is \(C=N+E\). If \(f\) is injective, \(E=0\). Otherwise a pair of distinct equal-value occurrences contributes both orientations, so \(E\ge2\). Therefore
\[
\boxed{C<N+2\quad\Longleftrightarrow\quad f\text{ is injective}.}
\tag{E}
\]
The strict threshold is sharp: a single double occurrence has excess exactly two.

More generally, if \(K_{ij}\ge0\) and \(K_{ij}=1\) whenever \(f(i)=f(j)\), then termwise comparison gives
\[
C(f)\le\sum_{i,j}K_{ij}.
\]
Hence \(\sum_{i,j}K_{ij}<N+2\) implies injectivity.

For the actual zeta multiplicity copies, the existing repository theorem
ActualZeroOrdinate.copyOrdinate_injective_iff identifies this injectivity exactly with
\[
\forall\rho\in\operatorname{cutoff}(T),\quad
\Re\rho=\tfrac12\ \text{and}\ m_\rho=1.
\]
The drafted bridge adds the exact collision-energy criterion and the general positive-kernel criterion at each finite height.

It also proves the cutoff logic: certificates at arbitrarily large heights suffice for every positive-height cutoff. Every fixed zero eventually lies inside one such cutoff. This is stronger than requiring a certificate at every individual height.

**Formal boundary.** The drafted global statement concludes criticality and simplicity of every actual positive zero. It does not yet add a separate theorem identifying that property with Mathlib's full RiemannHypothesis plus global simplicity. The usual passage also uses conjugation and the known absence of real zeros in the open critical strip. No such provider is silently assumed in the new Lean statements.

Drafts: FiniteCollisionCertificates.lean and ActualOrdinateCollisionCertificates.lean.

## 5. An exact finite gap-adapted sine filter

Let \(D\) be the finite set of positive absolute nonzero differences among the sampled ordinates. Define
\[
\kappa_D(v)=\prod_{d\in D}
\operatorname{sinc}^2\!\left(\frac{\pi v}{d}\right),
\quad
\operatorname{sinc}(x)=
\begin{cases}1,&x=0,\\ \sin x/x,&x\ne0.\end{cases}
\]
Every factor is nonnegative and \(\kappa_D(0)=1\). For a sampled nonzero gap \(v\), the factor with \(d=|v|\) evaluates at \(\pi\) or \(-\pi\), and is zero. Thus
\[
\boxed{\sum_{i,j}\kappa_D(\gamma_i-\gamma_j)=C_T}
\tag{F}
\]
exactly, at finite height and without a limiting operation.

This gives a necessary and sufficient adapted-kernel certificate:
\[
\sum_{i,j}\kappa_D(\gamma_i-\gamma_j)<N(T)+2
\]
if and only if every zero in the positive-height cutoff is critical and simple. Cofinal such certificates are equivalent to criticality and simplicity in every positive-height cutoff.

There is also a paper Fourier representation. The squared sinc factor is the Fourier transform of the probability density
\[
w_d(u)=\frac{d}{2\pi}
\left(1-\frac{d|u|}{2\pi}\right)_+.
\]
Convolving these finitely many densities gives a nonnegative probability weight supported on
\[
|u|\le B_D,\qquad B_D=2\pi\sum_{d\in D}\frac1d.
\]
Its Fourier transform is \(\kappa_D\); therefore its integral against \(|Z_T(u)|^2\) equals \(C_T\) exactly. For \(D=\varnothing\), use the unit point mass at zero as the empty convolution.

**Verification boundary.** The drafted Lean module states the finite kernel equality (F), the concrete gap-set construction, and the sharp certificate, with candidate proof terms. It does not formalize the Fourier integral or the convolution-weight construction.

**Research boundary.** The filter is adapted to the actual finite gap set. Its exactness alone does not bound \(C_T\), control its bandwidth as \(T\) grows, or exclude any off-line zero. No RH estimate is obtained simply by constructing this filter.

## 6. A stronger Haar Gaussian \(L^1\) rate

In the notation of Section 11 of the notes,
\[
\boxed{\left|\|G_{S_P}\|_1-\sqrt{2/\pi}\sqrt{V_P}\right|
\le \frac{A_P}{V_P}.}
\tag{G}
\]
This improves its constant \(3\) to \(1\).

Chen–Goldstein–Shao, *Normal Approximation by Stein's Method*, Chapter 4, Corollary 4.2 (book page 68), give the Wasserstein / integrated-distribution distance bound
\[
d_W\!\left(\sum_i\xi_i,Z\right)\le\sum_i\mathbb E|\xi_i|^3
\]
for independent centered variables with summed variance one.
Take \(\xi_p=g_p/\sqrt{V_P}\). The notes prove
\(\sum_p\mathbb E|g_p|^3\le A_P\), so the normalized bound is \(A_P/V_P^{3/2}\). The function \(|x|\) is 1-Lipschitz, and multiplying its expectation difference by \(\sqrt{V_P}\) proves (G).

This is a sourced paper strengthening. The probability theorem and its Haar application have **not** been formalized in the new Lean files. It concerns independent Haar phases, not simultaneous growing-prime samples of actual zeros.

Primary reference:
https://sites.stat.washington.edu/jaw/COURSES/520s/523/HO.523.20/CGS-Chapter4.pdf

## 7. Classical inputs, genuine research gaps, and formalization gaps

The audit confirmed the following published unconditional inputs:

- Ford–Meng–Zaharescu, Lemma 1, allows all \(x,T>1\); the narrower support condition in Lemma 2 belongs to the phase-comparison estimate. https://arxiv.org/pdf/1511.06814
- Ford–Zaharescu, Lemma 2, gives the uniform Selberg density estimate for \(1/2\le\sigma\le1\). https://ford126.web.illinois.edu/wwwpapers/fz.pdf

These are known mathematical theorems, whose complete Lean implementation was not undertaken here. They are not RH assumptions and are not new project axioms.

The original Sections 1–12 have not all been formalized. The new drafts cover finite balanced algebra, coefficient-error transfer, weighted frequency geometry, and finite/cofinal collision deductions. They do not certify the notes' infinite-prime measure obstruction, subgaussian Haar density, prime-tail estimates, Berry–Esseen theorem, complete growing-support asymptotics, or finite-band integration formula.

The remaining RH-facing obligations are genuine mathematics:
1. Supply sufficiently strong bounds for the **actual arithmetic residual coefficients**, preserving signed terms and the exact variance/square corrections.
2. Reach the necessary frequency scale with actual-zero estimates; raising the balanced order by itself does not reach microscopic pair correlation.
3. Prove a cofinal collision-energy upper bound excluding every repeated ordinate, rather than a density-one conclusion allowing sparse exceptions.
4. Control an adapted filter's bandwidth and its integral from arithmetic information; exact annihilation alone does not do this.

No claim here proves RH, assumes RH in order to prove RH, or asserts publication priority.

## 8. Preserved recovery inputs and remaining validation

The bundle contains:
- Six intended subject modules under RiemannResearch/Analysis/.
- continuation.patch, adding the modules and exporting them from RiemannResearch.lean against the inspected base.
- The exact original submitted snippet under verification/submitted_snippet.lean.
- verification/handoff.json, retaining the known workspace and job.
- The unchanged input notes and this continuation.

The recorded job's terminal compiler error has now been recovered, and the local candidate has been repaired. The archived handoff and submitted snippet remain historical evidence of the interrupted attempt. The next certification is the complete integrated server checkpoint, including diagnostics repair, declaration and axiom inspection, and the updated theorem catalog. The checkpoint must validate the exact integrated source before publication. Direct GitHub writes or hosted CI do not substitute for that server gate.



## Resumed continuation: criticality without a simplicity requirement

After the requested pause in the original session, the existing job was still queued at the last successful poll and later calls timed out. That historical interruption has now been resolved: its terminal diagnostics report the initial snippet's proof error. Recovery preserves the earlier work and the distinction between repaired candidates and a successfully checked integrated project.

The power proof uses explicit multiplication monotonicity rather than `gcongr`, and focused tactic imports were added. The original six-module candidate in `verification/all_modules_candidate.lean`, including axiom reports, was never submitted during the blocked session. Recovery repairs the source modules for the new combined integration. The historical combined candidate is retained as evidence; the final checkpoint must check the current integrated modules.

A useful strengthening now appears in `ActualOrdinateCollisionCertificates.lean`. Let \(S_T\) be the finite set of distinct actual nontrivial zeros with \(0<\Im\rho\le T\), and let \(D(T)=|S_T|\). Here each distinct zero is sampled once: this differs from the multiplicity-weighted ordinate sum and does not replace that sum in the other results. Define
\[
E_T^{\rm distinct}=\sum_{\rho,\sigma\in S_T}
K_{\Delta_T}(\Im\rho-\Im\sigma),
\qquad
\Delta_T=\{|\Im\rho-\Im\sigma|>0:\rho,\sigma\in S_T\},
\]
where \(K_\Delta(v)=\prod_{d\in\Delta}\operatorname{sinc}(\pi v/d)^2\) and \(\operatorname{sinc}(0)=1\).
Every nonzero sampled gap is annihilated, so this energy equals the number of ordered distinct-zero pairs sharing an ordinate, including the diagonal. That number is \(D(T)\) if the ordinate projection is injective, and otherwise is at least \(D(T)+2\).

Functional-equation reflection supplies the criticality implication. If \(\rho=\beta+i\gamma\) is off the line, then \(1-\beta+i\gamma\) is a different zero in the same cutoff with the same ordinate. Conversely, if all cutoff zeros are on the line, equality of ordinates implies equality of complex zeros. Thus
\[
\boxed{E_T^{\rm distinct}<D(T)+2
\quad\Longleftrightarrow\quad
\forall\rho\in S_T,\ \Re\rho=\tfrac12.}
\]
Analytic multiplicities may exceed one. Therefore this criterion does not unnecessarily demand the simplicity conjecture. It also agrees exactly with the repository's actual horizontal-energy condition:
\[
E_T^{\rm distinct}<D(T)+2\quad\Longleftrightarrow\quad
\operatorname{horizontalEnergy}(T)=0.
\]
If such certificates hold cofinally in height, every actual positive-ordinate zero is critical. The converse also holds. **Existence of the cofinal certificates remains open; neither an exact filter nor this equivalence establishes the required global bound.** The draft includes the precise finite and cofinal equivalences and the positive-zero specialization. A full formal RH conclusion has not been assembled here.

The independent-Haar Gaussian constant-one improvement remains a paper result. Bounded provider searches did not find a suitable Lean theorem for the required independent, non-identically distributed Wasserstein third-moment rate. The qualitative iid central limit theorem does not supply that rate, and no probability theorem is silently assumed.
