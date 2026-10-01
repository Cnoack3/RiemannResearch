# Assuming RH is false: a signed arithmetic intersection

Research date: October 1, 2026 UTC. Repository base: `52d13f4fd91907fd499273bda0e5dac2c8b75077` in `Cnoack3/RiemannResearch`.

## Result and verification boundary

No contradiction, proof of RH, or established mathematical breakthrough was found. The investigation does sharpen the necessary conditions for failure. In particular, ordinary unconditional prime estimates strengthen the actual screened-gap condition from

$$\sum_j \frac{2^jG_j^2}{(j+3)^2}<\infty$$

to

$$\boxed{\sum_j2^jG_j^2<\infty.}$$

They also force the actual normalized prime survivors to satisfy

$$\boxed{\sum_{p\ \mathrm{prime}}(\log p)|s_p|^2<\infty,\qquad
s_p\sqrt{\log p}\longrightarrow0.}$$

The discrete Mellin witness gives the additional height-sensitive obstruction

$$\boxed{D\ge\frac{2\beta-1}{6}|\rho|^{2\beta-3}}$$

for every off-line zero $\rho=\beta+i\gamma$, $1/2<\beta<1$. The familiar continuum lower bound remains available, and either can be the stronger bound. The height-sensitive bound improves that bound when $|\rho|^{2\beta-1}>6$.

New Lean declarations establish the exact finite-window certificate equality, uniform harmonic survivor bounds, finite exceptional-prime counts, and polynomial lower bounds on the actual signed raw Gram sum and inverse source energy. The stronger prime-tail assembly and height-sensitive discrete bound are proved below in ordinary mathematics; they are not asserted to be kernel-verified analytic imports. No external theorem is introduced as a project-local axiom. No claim of mathematical priority is made.

## 1. Keep the two projection problems distinct

Let

$$H=\left\{f:\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)}<\infty\right\},\qquad
g_d(n)=\frac{n\bmod d}{d},\qquad V=\overline{\operatorname{span}}\{g_d:d\ge2\}.$$

For the constant target, put

$$r=1-P_V1,\qquad D=\|r\|^2=1-q_\infty.$$

For the physical first-point target, write $r_{\rm pt}$ for its closed residual and $\Delta=\|r_{\rm pt}\|^2$. Under $\neg RH$, both are positive, and the canonical tail certificate $z$ satisfies

$$C_N\longrightarrow C_\infty=\|z\|^2=\Delta^{-1}-2<\infty,
\qquad z_N=\operatorname{tailMinimum}(N)\longrightarrow z.$$

These two residual energies are different. Likewise, `ProjectionSchur.schurEta/schurSigma` and `TailCapacity.schurEta/schurSigma` are different families. The former telescope captured constant energy; the latter telescope tail capacity. Equating them would fabricate a contradiction.

For every genuine residue-tail certificate $w$, the repository proves

$$\|w\|^2=C_N+\|w-z_N\|^2,$$

and, under failure,

$$\|w\|^2=\|z\|^2+\|w-z\|^2.$$

Thus the same canonical certificate must satisfy all its tail, sign, interpolation and moment constraints. It is not permissible to choose a different favorable witness for each condition.

## 2. Inventory of the relevant criterion families

The inventory groups equivalent formulations rather than counting renamed versions as independent obstructions. Discovery used bounded declaration searches, source ranges, existing obstruction notes and the current GitHub branch. It is a research inventory, not a claim that every declaration in the large repository was newly rebuilt or every historical proposed criterion accepted.

| Criterion family and representative modules | Necessary consequence of $\neg RH$ | Assumption audit |
|---|---|---|
| Constant projection, captured energy, fixed coefficients, Gram correction: `ParetoNormClosure`, `MobiusCoefficientStabilization`, `ResidueGramMobiusCorrection` | $D>0$; captured energy tends to $1-D<1$; some fixed coefficient targets fail, with cofinally wrong coefficients | Many formulations describe the same residual. Several formal RH converse directions still take a density or Baez-Duarte provider explicitly. The directions used for contraposition are unconditional. |
| Constant-projection Schur saturation: `ResidueSchurLimits`, `ResidualGainObstruction` | Total captured gain $1-D$; relative gains summable; exact logarithmic budget $\log(e_0/D)$ | These are constant-projection gains, not capacity gains. |
| Residual tails: `ResidualTailPNT`, `ExactHeadResidualTail` | $t_N\to0$ but $Nt_N\to\infty$; quantitative lower bound $t_N\gtrsim D^2\log N/(N\log\log N)$ | The classical PNT premise is discharged in this repository result. A cofinally bounded normalized tail remains an open arithmetic provider. |
| Exact heads and L1 approximation: `ParetoExactHeadResidual`, `RHFalseEnergyConsequences` | Every legal exact-head error has a same-zero polynomial energy floor; legal L1-convergent approximants cannot have the required subpower energy savings | Full norms and physical tails remain. |
| Natural Mobius correction: `NaturalMobiusResidualEscape`, `RawMobiusFiniteWindowCriterion` | Actual inverse source energy diverges, with the sharper same-zero lower bound in Section 4 | Small fixed components before inversion do not control a growing inverse matrix. |
| Signed raw Gram sums: `RawMobiusSignedGramEnergy` | Signed off-diagonal energy has a positive polynomial lower bound | Both orientations and signs of all pairs remain. A subpower signed upper bound is not established. |
| Tail averages and centered primitives: `ParetoTailAverageCriterion`, `NaturalMobiusCenteredPrimitiveTests` | For every $L$, the centered tail-average square sum diverges, although the consecutive-difference square sum is $D-D^2$; every stated logarithmic primitive saving fails | Square-summable differences do not imply convergence or square-summable deviations from a constant. |
| Regularized shifted minima: `NoorRegularizedApproximation` | Unscaled minima may tend to zero, while divided minima retain a lower limit at least $D$ | The missing unscaled/divided rate cannot be removed. |
| Weighted approximations and moving Hardy edges: `ParetoWeightedApproximationRH`, `ExactHeadMovingHardyRH` | A zero creates a positive weighted-energy floor for each weight below its threshold; uniform bounds as edges approach $1/2$ fail | Existing convergence toward the line $1$ does not give the necessary moving boundary near $1/2$. |
| First-site capacity, trials and certificates: `ParetoTailCapacityDuality`, `IntegerDPPVacancyCertificates`, `IntegerDPPCertificateCutoffBridge` | Finite capacity, positive first-site vacancy and a genuine canonical certificate | Finite trial optimizers and cutoff equivalences are not constructions of arbitrarily small errors. |
| All-site holes, hazards, damped determinants: `IntegerDPPAllSiteObstruction`, `IntegerDPPPowerWeightedHoles`, `IntegerDPPDampedConvergence` | One common zero supplies positive holes at every site; suitable weighted hole series diverge; hazards are summable; damped limit is strictly above its benchmark | Offsite and physical-tail contributions remain. |
| Capacity prime budgets: `ParetoFirstSitePrimeBudget`, `ParetoFirstSitePrimeAlignment` | $A_N/U_N\to-1$; $V_N-U_N=o(\sqrt{U_N})$, $U_N+X_N=o(\sqrt{U_N})$; prime and nonprime survivors have finite total energy | The positive source diverges, but its actual signed cancellation is retained. |
| Angular blocks, complete trees and CRT tests: `ParetoFirstSitePrimeBlocks`, `ParetoFirstSitePrimeMultiscale`, `ParetoFirstSiteAdjacentContrasts` | Actual block scatter, complete internal split trees, historical drift and all chosen normalized contrast series are summable | Fixed-vector and finite-column transfer applies only to fixed objects. Growing full-dictionary screening remains. |
| One-sided arithmetic and physical masses: `MobiusResidualOneSidedMass`, `ResidualPhysicalSignMass`, `MobiusResidualSignOscillation` | Both signs occur cofinally; both charge masses and both signed physical first moments diverge | No absolute convergence or one-sided positivity can be silently imposed. |
| Two optimal coefficients: `OptimalTwoCoefficientCriterion` | $4-3c_{\infty,2}-c_{\infty,3}\ge(23/24)D>0$ | The exact norm-square remainder is retained. |
| Damped moving heads: `DampedMobiusSparseHeadDichotomy` | At every sufficiently small positive damping, every moving cutoff has divergent actual signed off-diagonal energy | The consequence concerns actual centered damped rows, not independent random signs. |
| Strip zeros and Chebyshev Mellin continuation: `RiemannHypothesisRightHalfStrip`, `ChebyshevMellinRH` | A common right-half-strip zero and a pole of the continued Chebyshev error transform | Analyticity of the continuation is distinct from convergence of a proposed integral. |
| Burnol products and Li norms | Positive zero-product defect; failure of at least one RH-equivalent norm identity | `hBurnol` is explicit in formal projection consequences. An RH-equivalent positive norm identity cannot be imported as unconditional. |

The existing `RHFalseJointObstruction.lean` already combines the canonical certificate, common-zero site floors, head barriers, wrong coefficients, norm escape, sign excursions and determinant defect. This continuation preserves that theorem and adds the newer signed-screening constraints.

## 3. Exact capacity accounting under failure

Use the capacity Schur variables. At budget row $n$, the prospective conductor is $p=n+3$. Put

$$a_n=\operatorname{factorialPrimeDelta}(n)>0,\quad
b_n=\operatorname{factorialPrimeError}(n),\quad
w_n=\frac{\mathbf1_{p\ {m prime}}}{\sigma_{n+1}}.$$

Then $\eta_{n+1}=a_n+b_n$ at prime rows. Define the complete cumulative source, error and cross energies $U_N,V_N,X_N$, and the nonprime gain budget $J_N$. Exactly,

$$C_{N+1}=C_1+U_N+V_N+2X_N+J_N.$$

The signed mixed term is indispensable. The alignment identity rewrites this as

$$C_{N+1}=C_1+R_N+S_N+J_N,$$

where $R_N=(U_N+X_N)^2/U_N$ and $S_N=V_N-X_N^2/U_N$ are nonnegative. Under failure, $R_N\to0$, $S_N$ has a finite limit, and $J_N$ has a finite limit. In particular,

$$V_N-U_N=o(\sqrt{U_N}),\qquad U_N+X_N=o(\sqrt{U_N}),\qquad A_N/U_N\to-1.$$

For any finite future window, the new checked identity is

$$\|z-z_{N+1}\|^2=
\sum_{i<k}\mathrm{primeGain}_{N+i}
+\sum_{i<k}\mathrm{nonprimeGain}_{N+i}
+\|z-z_{N+k+1}\|^2.$$

All nonprime rows and the final remaining error are visible. Let

$$T_N=\|z-z_{N+1}\|^2=C_\infty-C_{N+1}\longrightarrow0.$$

Every actual future prime survivor window is bounded by this single $T_N$, independently of the length or of how the window is selected.

## 4. The same zero forces signed raw and inverse growth

Select $\rho=\beta+i\gamma$, $1/2<\beta<1$, with $\zeta(\rho)=0$, and write $\alpha=2\beta-1>0$. The new Lean assembly gives, eventually,

$$\boxed{O_N\ge\frac{\alpha}{96|\rho|^2}(N+1)^\alpha-2H_N-\frac13,}$$

where $O_N$ is the full signed raw Mobius off-diagonal Gram sum. It is not the sum of absolute values, and both pair orientations remain.

For the actual inverse source quadratic form, the same zero gives, for $n\ge2$,

$$\boxed{I_n\ge\frac{\alpha}{96|\rho|^2}(n+2)^\alpha-e_0-\frac13.}$$

Here $I_n=(b_n+G_n\mu_n)^TG_n^{-1}(b_n+G_n\mu_n)$ with the repository's matrix indexing. The proof uses the exact equality between the natural and physical raw residuals, and the exact norm split $\|A_n\|^2=e_n+I_n$.

For every legal $f$ agreeing with $1$ through physical coordinate $N$, the same zero also gives

$$\|1-f\|^2\ge\frac{\alpha}{|\rho|^2}(N+1)^\alpha.$$

These are constraints on the same actual zero, not unrelated existential witnesses. They coexist with finite screened capacity because raw and adaptively screened quantities differ.

## 5. Rigidity of the actual prime survivors

For prime $p=n+3$, define

$$s_p=\frac{\eta_{p-2}}{\delta_{p-3}}
=1+\frac{\operatorname{error}_{p-3}}{\delta_{p-3}}.$$

The checked harmonic floor gives

$$\frac{s_p^2}{4H_{p-1}}\le\mathrm{primeGain}_{p-3}.$$

Consequently, under failure,

$$\sum_p\frac{s_p^2}{H_{p-1}}<\infty.$$

For the finite exceptional set $B(N,k,\varepsilon)$ of actual prime rows in $[N,N+k)$ with $|s_p|\ge\varepsilon$, Lean proves

$$\boxed{\frac{\varepsilon^2\,|B(N,k,\varepsilon)|}
{4H_{N+k+1}}\le T_N.}$$

This works for every length, including adaptively chosen lengths. It yields the ordinary consequence that fixed-$\varepsilon$ exceptions up to $X$ number $o(\log X)$.

### Stronger source estimate: the exceptions are actually finite

The exact factorial coprime reciprocal-square mass is

$$M_p=\prod_{q\ge p,\ q\ {m prime}}(1-q^{-2})^{-1},\qquad
\delta_{p-3}=\frac{M_p}{p^2(M_p-1)},\qquad
0<\sigma_{p-2}\le\frac{H_{p-1}}{p^2}.$$

This uses the actual reciprocal-square mass from `ParetoEulerProduct` and `ParetoCoprimePrimeObservation`. It does not replace the Pareto norm or delete a tail.

Partial summation and classical PNT give

$$\sum_{q\ge p}q^{-2}\sim\frac1{p\log p},\qquad
M_p-1\sim\frac1{p\log p},\qquad
\delta_{p-3}\sim\frac{\log p}{p}.$$

For clarity, partial summation gives

$$\sum_{q\ge p}q^{-2}=-\frac{\pi(p^-)}{p^2}
+2\int_p^\infty\frac{\pi(t)}{t^3}\,dt,$$

and the two leading terms combine to $1/(p\log p)$. The logarithm of the Euler product differs from this sum by $O(\sum_{q\ge p}q^{-4})$, which is smaller. Therefore

$$\frac{\delta_{p-3}^2}{\sigma_{p-2}}\ge(1-o(1))\log p.$$

An explicit upper prime-count estimate alone suffices for a weaker constant. Dusart's unconditional $\pi(t)\le t/(\log t-1.1)$ above $60184$ implies $\pi(t)\le2t/\log t$ for $t\ge60200$. Thus

$$\sum_{q\ge p}q^{-2}\le\frac4{p\log p},\quad
\log M_p\le\frac8{p\log p},\quad
M_p-1\le\frac{16}{p\log p}$$

for $p\ge60200$. Since $H_{p-1}\le2\log p$ there,

$$\boxed{\delta_{p-3}\ge\frac{\log p}{16p},\qquad
\frac{\delta_{p-3}^2}{\sigma_{p-2}}\ge\frac{\log p}{512}.}$$

Comparison with the summable actual prime gain proves

$$\boxed{\sum_p(\log p)s_p^2<\infty.}$$

Thus $s_p\sqrt{\log p}\to0$ along every prime, and each fixed-$\varepsilon$ exceptional prime set is finite. This analytic assembly is an ordinary proof, not a newly formalized Dusart or Euler-tail provider. The asymptotic source calculation was already recorded in `AdjacentSchurResearch20260930.md`; the sharpened failure consequences are the new assembly here.

For prime blocks $[X,2X)$, let $T(X)$ denote the corresponding remaining canonical capacity error. PNT and the stronger source floor give

$$\operatorname{mean}_{X\le p<2X}s_p^2\ll\frac{T(X)}X=o(X^{-1}).$$

Pointwise small survivors alone are not a contradiction: a divergent gain series can have every term tending to zero. The decisive distinction is aggregate summability.

## 6. Stronger necessary condition on the actual pooled gap

Take $N=2^j$. On the two consecutive budget windows $[2N,3N)$ and $[3N,4N)$, define the actual pooled error slopes $X_L/U_L$ and $X_R/U_R$, and let

$$G_j=X_R/U_R-X_L/U_L.$$

Prime conductors differ from budget indices by the exact shift $p=n+3$. The constant aligned component cancels in this difference. The complete split equality is

$$S_{\rm parent}=S_L+S_R+
\frac{U_LU_R}{U_L+U_R}G_j^2.$$

Using the source asymptotic above and $\vartheta(x)\sim x$ gives

$$U_L,U_R\ge(1-o(1))N,\qquad
\frac{U_LU_R}{U_L+U_R}\ge(1-o(1))\frac N2.$$

For example, eventually both sources exceed $N/4$, so $S_{\rm parent}\ge NG_j^2/8$. The parent windows are disjoint dyadic windows; their complete scatters are bounded by the summable actual angular energy under failure. Therefore

$$\boxed{\neg RH\ \Longrightarrow\ \sum_j2^jG_j^2<\infty,
\qquad G_j=o(2^{-j/2}).}$$

This is stronger by two powers of the logarithmic scale than the earlier source-floor consequence. It controls the same actual screened $G_j$. Prime density supplies its weight, not a lower bound on its sign or size.

A sufficient arithmetic contradiction is now

$$\sum_j2^jG_j^2=\infty.$$

One stronger concrete provider would be fixed $\varepsilon>0$ and a set $E$ with divergent $\sum_{j\in E}(j+1)^{-1}$ such that

$$|G_j|\ge\frac{\varepsilon}{\sqrt{2^j(j+1)}}\quad(j\in E).$$

No such provider is proved or inserted as an axiom. The finite split identity is formalized; this stronger eventual rate assembly is ordinary mathematics.

## 7. A sharper discrete obstruction from the same zero

Write $R=|\rho|$, $\alpha=2\beta-1\in(0,1)$, and

$$a_\rho(n)=\frac{n^{-\rho}-(n+1)^{-\rho}}\rho
=\int_n^{n+1}x^{-\rho-1}\,dx,\qquad
K_\rho=\sum_{n\ge1}n(n+1)|a_\rho(n)|^2.$$

Abel summation, initially in $\Re s>1$ and then analytic continuation to $\Re s>0$, yields

$$L_\rho(g_d)=\sum_na_\rho(n)g_d(n)
=\frac{(d^{-1}-d^{-\rho})\zeta(\rho)}\rho=0,
\qquad L_\rho(1)=\rho^{-1}.$$

The witness is continuous on $H$. Consequently, for the actual constant residual,

$$\boxed{D\ge\frac1{R^2K_\rho}.}$$

This uses the discrete functional norm rather than replacing it by a larger continuous norm. To bound it, observe

$$|a_\rho(n)|\le\min\{n^{-\beta-1},2n^{-\beta}/R\}.$$

For any $T>0$, the full head obeys

$$\sum_{n\le T}n(n+1)|a_\rho(n)|^2
\le\frac{8T^{2-\alpha}}{R^2}.$$

For every remaining interval, weighted Cauchy-Schwarz gives

$$n(n+1)|a_\rho(n)|^2\le\int_n^{n+1}x^{-2\beta}\,dx.$$

Keeping the whole tail therefore gives

$$\sum_{n>T}n(n+1)|a_\rho(n)|^2\le T^{-\alpha}/\alpha.$$

Take $T=R/2$ to obtain

$$K_\rho\le\frac{2^\alpha(1+2\alpha)}\alpha R^{-\alpha}
\le\frac6\alpha R^{-\alpha},$$

and hence

$$\boxed{D\ge\frac\alpha{2^\alpha(1+2\alpha)}R^{\alpha-2}
\ge\frac\alpha6R^{\alpha-2}.}$$

This proof is ordinary mathematics and was independently reviewed. Wolfram checked the finite algebra; it is supplementary evidence, not a proof of the infinite-series statements. The existing repository already contains the annihilator in `LateralScreeningContinuation20260924.md`; this height-sensitive norm estimate is an additional quantitative assembly.

The same discrete functional also bounds the actual first-point error:

$$\Delta\ge\frac{|1-2^{-\rho}|^2}{R^2K_\rho},\qquad
C_\infty+2\le\frac{R^2K_\rho}{|1-2^{-\rho}|^2}.$$

### Multiple zeros: retain their Gram correlations

For a finite family of off-line zeros, include multiplicity rows

$$a_{\rho,k}(n)=\int_n^{n+1}(-\log x)^kx^{-\rho-1}\,dx,
\qquad b_{\rho,k}=(-1)^kk!/\rho^{k+1}.$$

Let $K$ be their full discrete Gram matrix. The exact finite dual optimization gives

$$D\ge b^*K^\dagger b.$$

The actual residual supplies feasibility; use the inverse when the rows are independent. For the conjugate pair put $B_\rho=\sum_nn(n+1)a_\rho(n)^2$. Then

$$D\ge\frac{2\bigl(K_\rho/R^2-
\Re(B_\rho/\bar\rho^2)\bigr)}{K_\rho^2-|B_\rho|^2}.$$

This retains the cross term. Separate one-zero floors cannot simply be added. The finite-family optimization is a prose-level Hilbert-space derivation, not a new Lean theorem in this checkpoint.

## 8. What external results add, and what they do not

Burnol's continuous projection formula and the Balazard-Saias-Yor identity give

$$\Omega_\zeta=\frac1{2\pi}\int_{-\infty}^{\infty}
\frac{\log|\zeta(1/2+it)|}{1/4+t^2}\,dt
=\sum_{\Re\rho>1/2}\log\left|\frac\rho{1-\rho}\right|>0$$

under failure, counting multiplicities. If $W$ is the continuous Nyman-Beurling space, then

$$D=1-e^{-2\Omega_\zeta}+\|P_W1-P_V1\|^2.$$

The arithmetic projection remainder is essential. Kunik's discussion of the integer-step subspace explicitly separates it from the continuous projection formula. The repository's formal Burnol consequences preserve an explicit `hBurnol` hypothesis.

Guth-Maynard's 2026 version gives the unconditional density estimate

$$N(\sigma,T)\le T^{30(1-\sigma)/13+o(1)}.$$

It permits a sparse off-line set. Its large-value theorem requires bounded Dirichlet coefficients and supplies an upper estimate; it does not automatically give a lower bound for adaptively screened signed CRT contrasts.

Platt-Trudgian rigorously exclude off-line zeros through at least height $3\cdot10^{12}$. Bellotti excludes

$$\beta\ge1-\frac1{54.004(\log|\gamma|)^{2/3}(\log\log|\gamma|)^{1/3}}$$

for $|\gamma|\ge3$. Neither excludes a high zero arbitrarily close to $1/2$.

Maier-Rassias analyze smoothed Mobius trial energy under exactly one off-line quadruplet and an additional reciprocal-derivative moment bound. Their conditional polynomial growth is compatible with this repository's failure anatomy. It is not a contradiction or an unconditional provider.

Suzuki's positive Li-norm identities are themselves RH-equivalent. Their unconditionally defined square norms cannot be equated to Li coefficients when assuming failure.

A separate callable Deep Research tool was unavailable. The investigation used primary papers through web search, GitHub, read-only parallel audits and Wolfram symbolic evaluation. Wolfram's context endpoint errored; its evaluator succeeded.

## 9. Why the stringent conditions still do not contradict one another

The Mellin annihilator has coordinates $n(n+1)\overline{a_\rho(n)}\sim n^{1-\bar\rho}$. Its tail energy behaves like $N^{1-2\beta}$, so its normalized tail grows like $N^{2-2\beta}$. Thus a nonzero square-integrable obstruction can have a vanishing tail and an unbounded normalized tail. This illustrates compatibility; it does not identify that witness with the actual canonical residual.

Likewise, at the level of scalar source/survivor identities one may take prime source energy comparable to $\log p$, survivors $s_p=2^{-p}$, errors $s_p-1$, and zero nonprime gains. These satisfy divergent source, finite surviving energy, alignment saturation and all finite tree identities. They are not the repository's arithmetic rows and are not a counterexample to RH. They show why positive source estimates plus square identities alone cannot force the desired contradiction.

A very high hypothetical zero with $\beta$ close to $1/2$ has an arbitrarily small positive spectral defect and obeys the cited density and zero-free bounds. Numerical verification over a finite height range cannot exclude that remaining scenario.

## 10. Precise remaining contradiction targets

Any one of these established sufficient providers would refute the simultaneous failure conditions:

1. Prove nonsummability of the actual log-weighted prime survivor energy, with a quantitative transfer to the true Schur rows.
2. Prove $\sum_j2^jG_j^2=\infty$ for the actual screened pooled gaps; the weaker threshold in Section 6 is sufficient.
3. Obtain a nonsummable actual moving CRT contrast certificate after retaining or controlling the complete inverse-Gram screening remainder.
4. Prove a cofinal subpower upper bound on the actual signed raw off-diagonal sum, contradicting the same-zero polynomial lower bound.
5. Prove cofinal boundedness of the actual inverse source energy or of $Nt_N$, contradicting their failure growth.
6. Derive an arithmetic upper bound on $D$ smaller than the simultaneous discrete zero-Gram floor for every possible off-line zero set.

The strongest next arithmetic task is a lower estimate for actual signed survivor or contrast energy, possibly obtained from a useful explicit model with a proved weighted square-summable screening error. Fixed-column removal and upper large-sieve inequalities alone do not supply it. This is the remaining substantive gap, rather than an unstated RH-strength provider.

## 11. Verification record

The coherent candidate containing the new prime-window and raw/inverse-growth proofs completed Lean with exit code 0, `verified: true`, job `job_sFBEZ1nAf8AhlkKJHGb3sJXTJkhDCG36`, code SHA-256 `ad1b7c76133e9c37b03703e753d68c686b7026ceae3600ffdee857fd2e61980c`.

Axioms were printed for the exact complete-window identity, canonical exceptional-row bound, uniform windows, same-zero raw/head obstruction and inverse-source power lower bound. Every inspected declaration reported only `propext`, `Classical.choice`, and `Quot.sound`. Failed intermediate candidates were repaired; none is presented as verification evidence.

Installed-module and reverse-dependent validation is handled by the single final publication checkpoint. Its terminal receipt is reported separately; an accepted queued job is not publication evidence. The new common-joint theorem has sole mathematical premise $\neg\mathrm{RiemannHypothesis}$.

The additional common-joint theorem completed Lean with exit 0, verified true, job `job_7FkdpQUWJ5Uch9WLm9OaYdhunB3dM-WI`, code SHA-256 `634836e419e9d5f8c40889e05c5c4fd24763f3eaa9982909dca4c6d115f27663`. Its axiom inspection also reported only the three standard foundations above.

## Primary references

- Jean-Francois Burnol, *A note on Nyman's equivalent formulation of the Riemann Hypothesis*, Theorem 1.2 and Lemma 2.4: <https://arxiv.org/pdf/math/9910055>.
- Matthias Kunik, *Charakterisierung der Riemannschen Hypothese mit Hilfe eines Hilbertschen Folgenraumes*, integer-step discussion pp. 3-4: <https://math.ovgu.de/math_media/Medien/Institute/IAN/Kunik/Publikationen/rh.pdf>.
- H. M. Bui, S. J. Lester and M. B. Milinovich, *On Balazard, Saias, and Yor's equivalence to the Riemann Hypothesis*, equation (1.1), Theorem 1.2: <https://arxiv.org/pdf/1306.0856>.
- Pierre Dusart, *Estimates of Some Functions Over Primes without R.H.*, Theorem 6.9: <https://arxiv.org/pdf/1002.0442>.
- Larry Guth and James Maynard, *New large value estimates for Dirichlet polynomials*, April 7, 2026 version, Theorems 1.1-1.2: <https://arxiv.org/html/2405.20552v2>.
- Dave Platt and Tim Trudgian, *The Riemann hypothesis is true up to $3\cdot10^{12}$*: <https://arxiv.org/pdf/2004.09765>.
- Chiara Bellotti, *Explicit bounds for the Riemann zeta function and a new zero free region*, Theorem 1.2: <https://arxiv.org/pdf/2306.10680>.
- Helmut Maier and Michael Th. Rassias, *A criterion related to the Riemann Hypothesis*, Theorem 1.1: <https://arxiv.org/pdf/1705.09918>.
- Masatoshi Suzuki, *Li coefficients as norms of functions in a model space*, Theorem 1.1: <https://arxiv.org/pdf/2301.05779>.
