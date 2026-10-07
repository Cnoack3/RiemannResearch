# CRT and canonical-affine Lean formalization audit — 7 October 2026

The supplied Lean drafts have been repaired and integrated into the current RiemannResearch project. Nineteen new modules contain 208 theorem or lemma declarations, including private support lemmas. Every new module passed an isolated Lean diagnostic check with no errors. The final checkpoint validates the changed modules and their local reverse dependents before publication.

The work establishes finite and Hilbert-space constructions, sharper exact identities, and conditional RH consumers. It does not supply the remaining arithmetic cancellation or energy-growth estimate.

## 1. Coverage of the supplied material

| Supplied material | Final formalization |
|---|---|
| ProjectedDilationGain | Analysis/ProjectedDilationGain.lean; optimal line search and all correction squares retained |
| PrimeGainRecursion | Analysis/PrimeGainRecursion.lean; signed windows, both exact gain criteria, and positive quadratic reciprocal completion |
| NormCovariance | Analysis/NormCovariance.lean; finite covariance and strict block loss |
| ParetoUnscaledDilation | RH/ParetoUnscaledDilation.lean; complete mean/Gram scaling, composition, and signed product-conductor recurrence |
| FiniteProjectedDilationHierarchy, including the separately attached copy | Analysis/FiniteProjectedDilationHierarchy.lean; Analysis/FiniteProjectedDilationCertificates.lean |
| SquarefreeStepBridge | Analysis/SquarefreeStepBridge.lean; RH/SquarefreeParetoTransfer.lean connects it to the complete existing step isometry |
| AggregatedSignedGapDraft | Existing Analysis/CumulativeSignedGap.lean and RH/ParetoCumulativeSignedGap.lean; new cofinal bounded-prefix-floor consumers |
| ParetoAffineOptimizationCandidates | Existing canonical triangular exchange plus RH/CanonicalMobiusExchangeCertificate.lean and RH/ParetoAffineStationary.lean |
| FiniteHeadTailSpectralRealizationCandidate | Already formalized in Analysis/FiniteHeadTailSpectralRealization.lean and RH/ParetoActualHeadSpectrum.lean |
| LocalizedMellinHeadSignatureDraft | Already superseded by RH/LocalizedMellinHeadSignature.lean; new RH/LocalizedMellinSignatureDecay.lean |
| Paper nonvanishing and full affine span | Existing RH/MobiusReciprocalNonvanishing.lean and RH/CanonicalMobiusTriangular.lean; strengthened by RH/CanonicalAffineExhaustion.lean |
| Paper complete canonical inverse optimum | New RH/CanonicalResidualGramMinimum.lean constructs the actual inverse, positive normal mass, and unique weights |

Existing results were reused rather than copied under new names. The baseline checked through GitHub was commit 1840c7ba38d518160fbc35b87f522e5001b9a22e.

## 2. Native physical dilation and finite certificates

Analysis/OrthogonalDilationCompression.lean constructs, using actual orthogonal projections and continuous-linear adjoints,
\[
R=(I-P_U)D|_W,\qquad
K=pP_WD^*P_UD|_W,\qquad w=P_WD^*r.
\]
For an ordinary residual \(r\perp U\), physical scaling gives the pair identity, symmetry, positivity, and signed source identity. These are proved from the constructed operators, rather than assumed as additional providers.

RH/ThresholdProjectedDilationHierarchy.lean instantiates this construction with the actual Pareto Hilbert dilation. It proves equality with the established normalizedResidueHilbert atoms and their positive-conductor spans. The exact atom law is
\[
D_p g_d=g_{pd}-\frac1d g_p.
\]
Every finite combination dilates into the corresponding enlarged-conductor span, and finite spans supply the completeness needed for native projections.

For \(e_m=K^mw\) and \(r_{m+1}=r_m-pRe_m\),
\[
\|r\|^2-\|r_m\|^2
=p\sum_{k<2m}\langle w,K^kw\rangle.
\]
The subsequent legal optimizer contributes its complete additional norm square.

The new certificate module proves monotonicity and boundedness, and
\[
\sum_{m\ge0}\|K^mw\|^2\le\frac{\|r\|^2}{p},
\qquad K^mw\longrightarrow0\quad(p>0).
\]
This limit concerns increasing depth for one fixed compression/source. It is not a uniform estimate across arithmetic conductor stages and does not assert that the original residual tends to zero.

At any nonzero transported source, put \(a=\|e_m\|^2\) and \(b=\langle e_m,Ke_m\rangle\). The signed source identity proves \(a-b>0\). The last ray can then use
\[
t_*=\frac{pa}{a-b},
\]
with the exact additional bonus \(pb^2/(a-b)\). The complete optimizer remainder remains visible.

## 3. Exact quadratic reciprocal completion

For positive adjacent errors,
\[
\frac1{E'}-\frac1E
=\frac{E-E'}{E^2}
+\frac{(E-E')^2}{E^2E'}.
\]
PrimeGainRecursion proves the finite telescope retaining both terms. Under the stated gain lower bounds, its strengthened consumers retain the same positive quadratic remainder. Signed arithmetic certificates are allowed when actual error monotonicity is supplied independently.

The remaining arithmetic provider is an unbounded cumulative normalized actual gain, or the equivalent explicit signed-window budget. No individual-prime margin is manufactured by these algebraic identities.

## 4. Complete actual atom norm

RH/ParetoAtomPhysicalNorm.lean closes the finite-covariance-to-infinite-discrete-norm gap. Its convergent correction series gives
\[
\|g_p\|^2=
\frac4{3p}
-\frac{H_p+1/2}{p^2}
+\frac1{6p^3}
-\sum_{j\ge1}\Gamma_{p,j}.
\]
Here \(H_p=\sum_{r=1}^p1/r\), and \(\Gamma_{p,j}\) is the full finite covariance correction of the physical block. Summability is proved using literal Pareto block masses. The series is nonnegative, and is strictly positive for \(p>1\). Thus the corresponding envelope is strict for nontrivial legal atoms. The unconditional bound \(\|g_p\|^2<4/(3p)\) and its positive-pivot gain consumer are also proved.

Analysis/PairedCellDefect.lean proves a sharper continuum cell inequality:
\[
\Delta_{a,u,h}:=\int_0^h\frac{2us+s^2}{(a+s)^2}\,ds
\le h\int_0^h\frac{u+s}{(a+s)^2}\,ds
\quad(a>0,\ u,h\ge0).
\]
The proof retains the signed reflected pair and proves the required integrability. It improves the continuation's factor \(2h\) to \(h\).

The global paper consequence is
\[
T_p\le(1-\gamma)/p,\qquad
\|g_p\|^2\ge \frac Cp-\frac{H_p+1-\gamma}{p^2},
\quad C=\log(2\pi)-\gamma.
\]
These named global constants and their infinite continuum identification are still paper results. They are not asserted by the new Lean cell theorem or by the discrete norm module.

## 5. Constructed complete canonical optimum

Lean's finiteSpace M contains conductors \(2,\ldots,M+1\); its canonical window is \(N,\ldots,M\), with \(0<N\le M\). This is the paper window after shifting its conductor ceiling by one.

CanonicalResidualGramMinimum proves independence of the actual canonical family and of its residuals. A common factorial physical site proves that the constant target lies outside each finite legal space. Consequently the actual complete residual Gram inverse is constructed without an invertibility or stationarity hypothesis.

If \(R\) is that Gram matrix,
\[
z=R^{-1}\mathbf1,\quad
\kappa=\mathbf1^TR^{-1}\mathbf1>0,\quad
a_*=\frac z\kappa,
\]
then the unique normalized optimum satisfies
\[
E_{\min}=\kappa^{-1},\qquad
\|1-U(a)\|^2=\kappa^{-1}
+\|U(a)-U(a_*)\|^2.
\]
The optimum covers the entire legal exact-head interpolation space. Increasing the conductor ceiling increases normal mass; increasing the common head decreases it.

The RH consumer requires the explicit cofinal asymptotic
\[
\frac{\log(1+\kappa^{-1})}{\log(N+1)}\longrightarrow0.
\]
The finite construction and uniqueness are discharged; this arithmetic growth provider remains open.

The separate matrix expression involving the legal-atom Gram and \(CG^{-1}C^T\) is not newly asserted as a literal Lean matrix identity by these modules. The actual residual-Gram inverse optimum and its equality with the full interpolation minimum are proved.

## 6. Squarefree and Mellin transfers

The corrected finite atom is constant on each integer cell. SquarefreeParetoTransfer connects the literal corrected trial to the complete existing ParetoStepIsometry, and identifies its infinite error with the actual Hilbert norm. Squarefree centered approximation then implies the existing centered approximation condition and Mathlib's RH.

The converse still needs the published RH-conditional damped Möbius approximation theorem. A citation to that analytic theorem is not a Lean proof of it. The exact finite support filtering and discrete/continuous energy transfer are now formalized.

The four-improvement Mellin criterion was already stronger in the repository than its attached draft. The new SignatureDecay module additionally proves, at each hypothetical off-line zero and under the stated subpolynomial complete-energy bound, the little-o estimate
\[
|\alpha_i(s)|^2 n_i^{\,2\Re(s)-1-\varepsilon}\longrightarrow0
\quad(\varepsilon>0).
\]
No concrete arithmetic signature or spectral-moment provider is supplied.

## 7. Verification and continuation

All nineteen new modules passed isolated error diagnostics. Selected exact declarations were also checked for axioms: the actual Gram completion and its RH consumer, the physical finite-span dilation law, source convergence, the complete atom-norm identity, and squarefree approximation's RH implication. Their reports contain only propext, Classical.choice, and Quot.sound. These reports do not discharge hypotheses appearing in the theorem types.

Continue with an actual arithmetic provider, preferably the signed normalized-gain window or the explicit canonical normal-mass growth estimate. Preserve all complete Gram interactions, endpoint terms, and optimizer squares. A uniform residue mean cannot replace the actual CRT conditional law.

Additional analytic formalization targets remain:
1. The RH-conditional damped squarefree approximation theorem.
2. Infinite continuum cell regrouping and the gamma/Stirling evaluation of \(C\), followed by the finer global bounds and asymptotic.
3. The actual spectral-moment and signature providers from the four-improvement program.

Primary references for the analytic inputs, not substitutes for their formal proofs:
- Luis Báez-Duarte, A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis, 2: https://arxiv.org/abs/math/0205003
- NIST DLMF, gamma asymptotics and harmonic/digamma values: https://dlmf.nist.gov/5.11 and https://dlmf.nist.gov/5.4
