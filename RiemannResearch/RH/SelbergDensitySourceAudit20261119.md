# Which Selberg density estimates supply the horizontal-moment bounds?

Audit of the November 19, 2026 horizontal-moment commit against the literature and the current Lean sources. Write $L=\log T$, $d=\sigma-1/2$, and $X=Ld$. The repository asks for **one logarithm and one constant for all cutoffs** at a fixed slope. Its positive-height count is

$$
 N_+(\sigma,T)=\sum_{\substack{0<\gamma\le T\\ \beta\ge\sigma}}m(\beta+i\gamma),
 \qquad N_+(\sigma,T)\le C_a T^{1-ad}L
 \quad(T\ge H_a,\ 1/2\le\sigma\le1).
$$

Here $m$ is the analytic order of the zero. Different zeros at the same ordinate and repeated copies of a zero both contribute. [Starting commit](https://github.com/Cnoack3/RiemannResearch/commit/18c54a3a08e38bda0e26a193f57d601df45b6441) · [Lean definitions](../Analysis/ActualZeroSelbergDensity.lean)

## Which exponent can be used?

| Source and evidence | Estimate and scope | Lean status |
| --- | --- | --- |
| Selberg, Jutila, Conrey–Baluyot | With one logarithm on the whole half-strip, Selberg gives $a=1/4$, Jutila every fixed $0<a<1$, and Baluyot every fixed $0<a<8/7$. The last interval has supremum $8/7$ and no largest member. | The count and second-moment source interfaces are explicit local inputs. The repository proves their consequences. [Baluyot, Theorems 1.2.1–2 and §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Lamzouri, §2, equation (2.1), November 2026](https://arxiv.org/html/2611.14486v1#S2) |
| Total counting and Gabriel–Littlewood | One logarithm at $a=0$ on the full strip. For $q=3(1-\sigma)/(2-\sigma)$, the stronger curved bound is $N_+\ll\min(TL,T^qL^{2+q})$, uniformly for $T\ge2$. Its tangent at $1/2$ gives $a=4/3$ with $L^3$ globally. | Unconditional local providers are `uniformSelbergDensity_zero`, `exists_ingham_littlewood_density_all_heights` and `ingham_tangent_density_log_loss`. Chourasiya–Simonič's explicit Corollary 1 has constants on the listed bands, a starting height and additive $B_2 L^2+B_3L$. The local theorem supplies an order bound with its own constant. [Lean proof](../Analysis/ActualInghamLittlewoodDensity.lean) · [Corollary 1 and Table 1](https://arxiv.org/html/2507.15184v2#S1) |
| Baluyot plus Gabriel–Littlewood | $a=8/7$ with $L^{1+\varepsilon}$ for each fixed $\varepsilon>0$. For $8/7<b<4/3$, a surplus log power $e>(21/2)(b-8/7)$ suffices at slope $b$. | The interpolation is checked. The strict Baluyot range is its external input. Constants can depend on the selected loss. [Endpoint derivation](../Analysis/ActualSelbergDensityInterpolation.lean) |
| rStation paper 184/v1, November 19, 2026, Theorem 1(1) | With its dyadic specialization as an external input, **$a=4/3$ is attained with one logarithm** on the full strip. It also supplies $a=8/7$ by weakening the slope. | The platform records an automated acceptance. The local proof checks the deduction from `DyadicInghamOneLog`. The paper's analytic fourth-moment and inverse-polynomial estimates have no local proof in this audit. [Theorem 1 and review](https://rstation.ai/problems/riemann_hypothesis/papers/184) · [Review process](https://dualverse.ai/) · [Lean deduction](../Analysis/ActualSelbergTransitionWindow.lean) |

The strongest independently corroborated full-strip, one-logarithm result identified here is Baluyot's open interval. Among the newer source statements audited, paper 184 yields the largest one-logarithm slope, $4/3$, if its analytic estimate is accepted. The strongest full-strip one-logarithm provider located in this Lean project without an external premise is $a=0$. These are statements about available evidence. Optimality of any finite slope for the actual zeta zeros is open.

## Cutoffs and sources for fixed strips

Baluyot proves Conrey's 1989 announcement in his Rochester dissertation. His $N(\sigma,T)$ counts $\beta>\sigma,\ 0<\gamma\le T$. The exponent $1+\theta(1-2\sigma)=1-2\theta d$ requires $0<\theta<4/7$. Both $C_\theta$ and the starting height may depend on $\theta$. For $\sigma>1/2$, taking a limit of strict thresholds from below retains copies on $\beta=\sigma$ by continuity of the majorant. The inclusive endpoint $\sigma=1/2$ follows separately from total counting. At $\sigma=1$ the nontrivial strip count is empty. The upper height is inclusive throughout. [Source definition and Theorem 1.2.1](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Strict and inclusive transfer](../Analysis/ActualSelbergDensityConventions.lean)

| 2026 result | Scope and loss | Consequence for this audit |
| --- | --- | --- |
| Guth–Maynard, Annals, Theorem 1.2 | For $\beta\ge\sigma,\ \lvert\gamma\rvert\le T$, the height exponent is $15(1-\sigma)/(3+5\sigma)+o(1)$. At $\sigma=3/4$ it is $5/9+o(1)$. Combined with Ingham, the global coefficient of $1-\sigma$ is $30/13$, with a power allowance. | `guthMaynardDensity_of_absoluteCount` restricts the source count to positive heights, retaining analytic orders. The interface fixes $\sigma\in[1/2,1]$ and $\varepsilon>0$ before choosing the constant and eventual threshold. [Theorem 1.2](https://arxiv.org/html/2405.20552v2#S1) · [Lean interface](../Analysis/ActualGuthMaynardFixedStrip.lean) |
| Tao–Trudgian–Yang, Mathematics of Computation, §6 | Their $A(\sigma)$ bounds control $T^{A(\sigma)(1-\sigma)+\varepsilon}$ at a fixed abscissa. For example, Theorem 51 in the preprint gives $A(\sigma)\le2/(9\sigma-6)$ for $17/22\le\sigma\le38/49$ and $A(\sigma)\le9/[8(2\sigma-1)]$ for $38/49\le\sigma\le4/5$. | These enter pointwise minima on their stated strips. A fixed $T^\varepsilon$ dominates every fixed power of $\log T$ as $T$ grows, so these estimates give no additional global one-log slope at microscopic cutoffs. [Journal publication](https://doi.org/10.1090/mcom/4138) · [Theorem 51 and Table 2](https://arxiv.org/abs/2501.16779) |
| Lewko, Palomar 000010 v1 | The global coefficient $39/17$ is uniform in $\sigma$ with $T^\varepsilon$. The sharper piecewise curve has its right-hand branch $3/(2\sigma)$ strictly above $3/4$. Its uniform version requires $\sigma\le3/4$ or $\sigma\ge3/4+\delta$ for fixed $\delta>0$. | Externally kernel-checked on Lean 4.35.0-rc2, with local conditional transfers on 4.33.0-rc2. A native port can supply the two fields of `LewkoDensityHypothesis` using the pinned solution and the shared inclusive absolute-height count. [Registered verification](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1) · [Pinned proof](https://github.com/mrklwk/zeta-density-39-over-17-lean/blob/ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0/lean/Solution.lean) |
| Ye, October 2026 preprint, Theorem 1.2 | The short-interval estimate has height power $15h(1-\sigma)/(3+5\sigma)+\varepsilon$ for interval length $T^h,\ 2/3\le h\le1,\ 7/10\le\sigma\le4/5$. | It sharpens localized counts in that range. Its strip starts at $7/10$. [Preprint](https://arxiv.org/abs/2610.15989) |

A proportion of simple or critical-line zeros bounds a different statistic. A moving Selberg cutoff requires control of each right tail as a function of $d$. For example, Lamzouri's November small-gap work uses the fixed subcritical density input explicitly. [Lamzouri, §2](https://arxiv.org/html/2611.14486v1#S2)

## Source imports and analytic obligations

1. **Use the published count directly.** Import `ActualSelbergDensityConventions` and supply the local class `ZeroDensityLiterature.ConreyBaluyot2017`. Its field `rightCount` is Baluyot's strict, one-logarithm estimate. `conreyBaluyot` constructs the existing `ConreyBaluyotDensityHypothesis`. Its companion `oneLogSlope` supplies `UniformSelbergDensity a` to horizontal-moment consumers. Both are available below the Montgomery assembly. Selberg's quarter and slope one are immediate specializations. The underlying count theorem remains an external input.
2. **Alternatively supply the normalized moment.** For each fixed $\theta<4/7$ with $\theta>0$, choose the paper's positive truncation parameter before $T,\sigma$. Put $y=T^\theta$. On $1/2+1/\log y\le\sigma\le1/2+\eta$, the source is $\big|T^{-1}\int_T^{2T}|\zeta M|^2\,dt-1\big|\le C y^{1-2\sigma}$, with $M$ from (1.2.6), including $\lfloor y^{1+\varepsilon}\rfloor$. Lean multiplies by $T$, takes the upper side, and runs the existing dyadic assembly with its proved `inghamDensityBound`. A native proof must bound this actual mollified moment uniformly. The Gaussian route has a separate arithmetic target, `UniformGaussianMellinPartsBound`, a uniform upper bound on the **signed sum** of the residues and shifted vertical contribution over the required center range. The count theorem alone gives no such estimate. [Baluyot, Theorem 1.2.2 and §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Normalized moment conversion](../Analysis/ActualConreyBaluyotDensity.lean) · [Signed Gaussian arithmetic target](../Analysis/ConreyBaluyotRayMellinSeparation.lean)
3. **For the new $4/3$ source, isolate its dyadic claim.** In paper 184 choose $\eta_0=1,\ T=U=H=S$. Equation (1) bounds the count on $[S,2S]$ by $C S^q\log S$, uniformly in $1/2\le\sigma<1$. Its equation (2) also saves the factor $[1+(1-2d)\log S]^{1-q}$ in the denominator. For fixed interior $\sigma$ this reduces the total logarithmic factor to order $(\log S)^q$. The one-logarithm transfer only needs equation (1). Dropping the lower height endpoint gives the repository's $(S,2S]$. The local proof uses $q\le1-\frac43 d$ and sums dyadic windows including the finite initial segment. To remove the premise, a formalization can target just this specialization. The substantive inputs are the localized bounded mollified fourth moment and the energy estimate for the sharply truncated inverse that appears in its detector. [Paper 184, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/184) · [Dyadic assembly](../Analysis/ActualSelbergDyadicAssembly.lean)
4. **Keep the RH criteria downstream.** Arbitrarily large uniform slopes and cofinal smallness of the unnormalized one-sided mass are each equivalent to RH. Baluyot's interval and the proposed fixed slope $4/3$ give neither cofinal condition. An independent proof must supply one of them. [Slope equivalence](../Analysis/ActualSelbergSlopeRH.lean) · [Mass equivalence](../Analysis/ActualCofinalOneSidedMassRH.lean)

The moment route can be used directly in Lean.

```lean
import RiemannResearch.Analysis.ActualConreyBaluyotDensity

open RiemannResearch.Analysis
open ActualZeroOrdinate ZeroDensityLiterature

example (hm : ∀ θ : ℝ, 0 < θ → θ < 4 / 7 → ∃ ε : ℝ, 0 < ε ∧
    ConreyBaluyot.BaluyotDyadicMomentAsymptotic θ ε)
    {a : ℝ} (ha : 0 < a) (ha' : a < 8 / 7) : UniformSelbergDensity a := by
  letI : ConreyBaluyot2017 := ConreyBaluyot2017.of_normalizedMoments hm
  exact oneLogSlope ha ha'
```

## What the repository proves at $4/3$

The unconditional comparison with the curved Ingham majorant has an exact transition. Clearing the positive denominator $2-\sigma$ gives

$$
 T^q L^{2+q}\le T^{1-(4/3)d}L
 \quad\Longleftrightarrow\quad
 (5-4\sigma)\log L\le \tfrac43 d^2 L.
$$

There is a common constant for every cutoff satisfying this inequality. In particular $d^2L\ge(9/4)\log L$ suffices at large heights. Equality is included. This is an equivalence for the two majorants. The available total-count bound also handles every bounded $dL$. [Exact comparison and unconditional count theorem](../Analysis/ActualSelbergTransitionWindow.lean)

For the occurrence law at height $T$, put $m_T=\mathbb E_T[L|\beta-1/2|]$ and $v_T=\mathbb E_T[(L|\beta-1/2|)^2]$. Along heights tending to infinity with $m_T>0$ eventually and $m_T\to0$, one-log slopes below $A>0$ give

$$
 \frac{v_T}{m_T\log(1/m_T)}\le c\quad\text{eventually for each }c>1/A.
$$

Baluyot gives the threshold $7/8$ without any uniformity in the slope. Supplying the one-log dyadic Ingham hypothesis gives $3/4$ under the same assumptions on the mean. Without that hypothesis, the existing $3/4$ result from the three-log bound requires $\log L/\log(1/m_T)\to0$. The convergence of the microscopic mean, and the stronger cofinal smallness of $T m_T$ in the RH criterion, remain independent obligations. [Parametric moment theorem](../Analysis/ActualSizeBiasedDisplacement.lean) · [Conditional specialization](../Analysis/ZeroDensityLiterature.lean) · [Earlier mean-rate assumption](../Analysis/ActualHorizontalMomentRates.lean)
