# What remains to prove unconditional positive-gap PCC

**One signed limit remains open.** At each fixed positive rational width, the loss in pair mass from starting a gap interval at an actual zero instead of averaging its starting offset must agree, up to $o(1)$, with a finite prime-power energy. Lean proves that this statement is necessary and sufficient for ordinary positive-gap PCC. The limit is the hypothesis to supply to the reverse implication. The underlying single-character Landau estimate and translation limit are in [verified commit 6fe8e2ca](https://github.com/Cnoack3/RiemannResearch/commit/6fe8e2ca2b2dbc4d7ba0a6f95b55145bf9aa5cf6).

## A conditional route through continuous spectra

An intensity-one continuous convolution-DPP subsequential limit of the complete unfolded zeros must be the sine process. Fujii’s short-window number-variance estimate gives the required lower-slope bound for that same limit. For ordinary PCC, a convolution representation of the second factorial measure of every physical subsequential limit suffices. Establishing this representation remains open. [Sharp spectral rigidity and projection audit](CONTINUOUS_DPP_SPECTRAL_RIGIDITY.md)

## The exact proof obligation

Put $L=\log T$ and $D_T=TL/(2\pi)$, for $T>1$. Index the nontrivial zeros with $0<\gamma_i\le T$ by occurrence, repeating each complex zero according to its analytic multiplicity. Define

$$
P_T(q)=\frac{1}{D_T}\sum_{i,j}
\mathbf 1_{\{\,0<L(\gamma_j-\gamma_i)/(2\pi)\le q\,\}}.
$$

The lower endpoint is open and the upper endpoint is closed. Equal ordinates contribute zero, including distinct complex zeros at the same height. The conjectured cumulative mass is $G(q)=\int_0^q[1-\operatorname{sinc}^2(\pi u)]\,du$, where $\operatorname{sinc}(x)=\sin(x)/x$ and $\operatorname{sinc}(0)=1$. The Lean proposition requires $P_T\to G$ uniformly on every compact interval $[a,b]$ with $0<a\le b$. Positive rational widths suffice by monotonicity and continuity. This is the counting convention of Goldston, Lee, Schettler and Suriajaya, equations (1.3)–(1.5). [Paper](https://arxiv.org/html/2503.15449v1) · [Definitions](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomeryPositiveGapDensity.lean) · [Rational-width equivalence](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomerySampledCountError.lean)

Use the translated count $H_T(q)$ and the prime energy $B_T(q)$ given by

$$
\begin{aligned}
H_T(q)&=\frac{1}{L^2}\int_0^{L^2}\bigl[P_T(s+q)-P_T(s)\bigr]\,ds,\\
\Phi_T(u)&=\frac1L\sum_{1\le n\le\lfloor T\rfloor}
       \frac{\Lambda(n)}{n}\exp\!\left(2\pi i u\,\frac{\log n}{L}\right),\\
B_T(q)&=\int_0^q|\Phi_T(u)|^2\,du.
\end{aligned}
$$

The required estimate, with all quantifiers, is

$$
\boxed{\quad
\forall q\in\mathbb Q_{>0}\;\forall\varepsilon>0\;\exists T_0(q,\varepsilon)>1\;
\forall T\ge T_0(q,\varepsilon),\quad
|H_T(q)-P_T(q)-B_T(q)|<\varepsilon .
\quad}
$$

In particular, $T$ ranges over all sufficiently large real heights. The threshold may depend on the width and tolerance. The following two limits are unconditional for every fixed real $q>0$.

$$
H_T(q)\longrightarrow q,\qquad
B_T(q)\longrightarrow q-G(q)=\int_0^q\operatorname{sinc}^2(\pi u)\,du .
$$

Subtracting these two known limits shows exactly why the boxed estimate gives $P_T(q)\to G(q)$. The estimate requires the signed comparison with $P_T(q)$ sampled at the zeros. [Translation average and closing theorem](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomeryTranslatedGapDensity.lean) · [Prime energy and integrated sinc identity](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomeryPrimeProbeEnergy.lean)

## How to close the Lean proof

The hypothesis `h` in the following implication is the entire open goal. The implication itself uses the checked theorem `positiveGapPCC_iff_translationDeficit_primeEnergy`.

```lean
import RiemannResearch.Analysis.MontgomeryTranslatedGapDensity

open Filter RiemannResearch.Analysis
open scoped Topology
open MontgomeryPositiveGap MontgomeryPrimeTrace

example (h : ∀ q : ℚ, 0 < q →
    Tendsto (fun T : ℝ =>
      rightSmoothedOrdinateCount T q (Real.log T ^ 2) - positiveGapMass T q -
        primeProbeEnergy T q) atTop (𝓝 0)) :
    PositiveGapPCC :=
  positiveGapPCC_iff_translationDeficit_primeEnergy.mpr h
```

## What the Landau and dense prime-orbit results supply

A finite prime-orbit character has frequency $u=\sum_{p\in P}a_p\log p$ with integer coefficients $a_p$. Summing that character over zero occurrences and taking the squared modulus gives $|\sum_i e^{iu\gamma_i}|^2=\sum_{i,j}\cos(u(\gamma_i-\gamma_j))$. Write $\rho_i=\beta_i+i\gamma_i$. The reconstructed amplitude retains each horizontal moment with its phase.

$$
A_{T,J}(u)=\sum_i e^{u(\rho_i-1/2)}
-\sum_{j=1}^J\frac{u^{2j}}{(2j)!}\sum_i(\beta_i-\tfrac12)^{2j}e^{iu\gamma_i}.
$$

Let $N(T)$ be the number of zero occurrences. For $|u|\le(4/3)L$, Lean proves

$$
\left|\frac{\sum_{i,j}\cos(u(\gamma_i-\gamma_j))-|A_{T,J}(u)|^2}{N(T)}\right|
\le \frac{C}{T}
$$

uniformly for sufficiently large $T$ when $k,J\in\mathbb N$, $k\log L\ge2L$, and $2(J+1)\ge(k+4)(1+\tfrac43\sqrt L)\log L$. Here $4/3$ is the tangent slope in the Ingham zero-density bound. This controls the reconstruction error, including at the endpoint. [Count-normalized pair theorem](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/RationalLandauInghamTangent.lean)

For a finite test with real coefficients $c_b$ and frequencies $u_b$ in the same band, let $Q_T(u)=\sum_{i,j}\cos(u(\gamma_i-\gamma_j))$. Under the same conditions on $k,J$, the new theorem `eventually_weighted_primeOrbit_gap_count_precision` gives

$$
\left|\sum_b c_b\frac{Q_T(u_b)-|A_{T,J}(u_b)|^2}{N(T)}\right|
\le \frac{C}{T}\sum_b|c_b|.
$$

Thus $\sum_b|c_b|=o(T)$ suffices to make the horizontal reconstruction error $o(1)$ for a test that changes with height. The constant is independent of the number of characters, their choice and the signs of the coefficients. Multiplying the displayed error by $N(T)/D_T\to1$ gives the same $o(1)$ at PCC normalization. [Finite weighted transfer](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/RationalLandauInghamTangent.lean)

Two estimates are still needed for a Fourier proof using such tests.

1. **Arithmetic range.** The uniform rational Landau main-term estimate for $u=\log(n/m)>0$, $1\le m<n$, uses $\log n+3u/2\le\theta L$ with fixed $\theta<1$. Since $\log n\ge u$, this yields $u/L\le2\theta/5$. The wider $4/3$ range controls removal of the horizontal weights. Evaluating the corrected amplitudes still requires control of the signed moments and the arithmetic sum in the frequencies used by the proposed test. [Rational band](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/RationalLandauMovingBand.lean)
2. **Passage to gap intervals.** The character theorem counts all ordered pairs with equal ordinates included and uses $N(T)$. The target counts strictly positive unfolded gaps in $(0,q]$ and uses $D_T$. Lean already proves $N(T)/D_T\to1$. One must approximate the strict-interval count on the **actual pair measure** with normalized error $o(1)$ (or with limsup error at most each prescribed tolerance), accounting for ties and both orientations. The coefficient bound above controls reconstruction for the chosen test. It gives no estimate for this interval-approximation error. The repository’s Montgomery form factor also inserts the weight $4/(4+(\gamma_i-\gamma_j)^2)$. [Form factor](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomeryFormFactor.lean) · [Count normalization](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/ActualZeroCountNormalization.lean)

The tie correction can be written exactly. With $x_{ij}=L(\gamma_j-\gamma_i)/(2\pi)$ and $m_T(t)$ the number of occurrences at ordinate $t$, swapping $i$ and $j$ gives, for $q>0$,

$$
2D_T P_T(q)=\sum_{i,j}\mathbf 1_{\{|x_{ij}|\le q\}}
             -\sum_{t\,\text{a distinct ordinate}}m_T(t)^2 .
$$

This formula gives the collision term to subtract from an even Fourier test that includes zero. The term counts every ordered pair of occurrences sharing a height. [Collision identity](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/ActualZeroCollisionMultiplicity.lean)

## An equivalent target for the Selberg approach

Let $S_*(t)=N(0,t]-\mathrm{smoothCount}(t)$, with the repository’s exact gamma main term. Define

$$
A_T(q)=\frac1{D_T}\sum_i
\left[S_*\!\left(\min\{T,\gamma_i+2\pi q/L\}\right)-S_*(\gamma_i)\right].
$$

It suffices, equivalently, to prove $A_T(q)+B_T(q)\to0$ for every fixed positive rational $q$. The required sign is negative for the sampled increment, which must satisfy $A_T(q)\to-\int_0^q\operatorname{sinc}^2(\pi u)\,du$. Either this limit or the boxed estimate closes the same conjecture. [Signed-trace equivalence](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomeryPrimeProbeEnergy.lean) · [Clipped sampled increment](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomerySampledArgumentError.lean)

The signs can also be checked at finite height. Write $M_T(q)$ for the same clipped, sampled increment with $\mathrm{smoothCount}$ in place of $S_*$. The exact identity $A_T(q)=P_T(q)-M_T(q)$ gives
$$
[H_T(q)-P_T(q)-B_T(q)]+[A_T(q)+B_T(q)]=H_T(q)-M_T(q).
$$
The right side tends to zero unconditionally since $H_T(q)\to q$ and $M_T(q)/q\to1$. This explains why the two open residuals have opposite signs. [Finite identity and uniform smooth-count estimate](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MontgomerySignedCesaroTrace.lean)

For the covariance approach, the repository gives an exact signed decomposition and a complete-window prime-diagonal comparison for primes up to $\lfloor\log\log T\rfloor$. The full-cutoff rate and the covariance asymptotic throughout $y=T^{o(1)}$ still require estimates on the actual sampling, endpoint and mean-value errors. Those estimates would have to yield the signed limit above. [Published covariance status](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/MICROSCOPIC_GAP_PROOFS_20261126.md)

Simonič, Trudgian and Turnage-Butterbaugh’s Lemma 8 bounds the Lebesgue measure of the $t\in[T,2T]$ where $|S(t+2h)-S(t)|\ge\lambda$ at their specified $h$. The rank approach uses that tail estimate through a dyadic transfer to short-window counts. Even after a square-tail bound is supplied, convergence of the **retained** positive-gap mass to $G(q)$ remains an input. [Lemma 8](https://arxiv.org/pdf/2010.10675#page=21) · [Repository transfer status](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/MICROSCOPIC_GAP_PROOFS_20261126.md) · [Moving-rank theorem](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/MicroscopicSquareTailCriteria.lean)
