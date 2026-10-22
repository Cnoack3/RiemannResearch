# Signed cancellation continuation, 2026-09-27

Continuation of commit `8dd31c46f3b047948b627f83700f87080003093e`.
The new results distinguish unconditional moving-parameter convergence from
conditional progress at a fixed subhalf damping. No fixed positive damping
below one half is newly proved to have finite canonical energy.

## Notation and the retained signs

Write `F_{ε,M} = arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M`.
This is the complete Hilbert cutoff, including its infinite physical tail.
Its squared norm includes every signed Gram cross term. The raw prefix
`F_{0,M}` may equivalently use the coefficient function `μ` (the zero-index
weight does not enter). The canonical scalar coordinates at positive damping
are

\[
 f_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor
 -n/\zeta(1+\varepsilon).
\]

No norm below means the sum of the norms of individual Möbius atoms.

## 1. An unconditional shrinking band below one half

For every fixed real `A`, the cutoff vectors converge uniformly to the
half-damped Hilbert limit throughout the band

\[
 \varepsilon\le\tfrac12,\qquad
 (\tfrac12-\varepsilon)\log(M+1)\le A.
\]

Precisely, for every `η>0` there is `J` such that every `M≥J` and every
`ε` in this band satisfy `‖F_{ε,M}−f_{1/2}‖≤η`. For `M>0` and `A≥0`
the band is `[1/2−A/log(M+1),1/2]`. The full finite Gram energies converge
to the canonical half energy. One constant depending on `A` also bounds
all these cutoff norms, their full signed off-diagonals, and every physical
head off-diagonal, uniformly in both cutoffs.

Main declarations in `RH/DampedMobiusMovingSubhalfBand.lean`:

- `dampedMobius_moving_subhalf_tendsto`;
- `dampedMobius_logarithmic_subhalf_band_tendsto`;
- `dampedMobius_logarithmic_subhalf_band_uniform`;
- `dampedMobius_logarithmic_subhalf_band_energy_tendsto`;
- `dampedMobius_logarithmic_subhalf_band_signed_bounds`.

The general theorem in `Analysis/IncreasingAbelConvergence.lean` allows
increasing nonnegative triangular weights with a common terminal bound and
each fixed weight tending to one. Exact finite Abel summation bounds the
signed tail by twice the terminal weight. For this application the terminal
weight is `(M+1)^(1/2−ε)≤exp(A)`.

This is unconditional, using the checked half-endpoint convergence. The
damping limit remains **one half**, so this does not establish membership at
a fixed subhalf damping or the zero-damping limit required for RH.

## 2. Remove the independent scalar density-tail hypothesis

Let `P(t)=Σ_{d≤t}w(d)`, `w(0)=0`, and suppose the naturally ordered density
sum `Σ_{d≥1}w(d)/d` converges to `C`. Exact reciprocal Abel summation gives

\[
 D(x)-D(y)=P(x)/x-P(y)/y+\int_y^x P(t)t^{-2}\,dt.
\]

If `|P(t)|≤B t^a L(t)`, `a<1`, and `L` is nonnegative and decreasing,
the verified finite-bound transfer yields

\[
 |C-D(y)|\le \left(2+\frac1{1-a}\right)B y^{a-1}L(y).
\]

The constant is deliberately a finite-bound constant; the exponent and
secondary profile are preserved. The power and logarithmic natural-prefix
wrappers also verify the floor lifting. For logarithms the deterministic
shift satisfies `c>0`, `b≤a c`, so `t^a/(c+log t)^b` is increasing.

For `0<ε≤1/2`, the new Möbius convergence theorems require only:

| Input | Sufficient condition |
|---|---|
| `|P_ε(t)|≤B t^a` | `0≤a<ε` |
| `|P_ε(t)|≤B t^ε/(c+log t)^b` | `b>1`, `c≥6`, `b≤ε c` |

The density tail is now a conclusion. Its convergence is already
unconditional for Möbius at every positive damping. Main declarations:
`reciprocal_density_tail_bound_of_prefix_power`,
`reciprocal_density_tail_bound_of_prefix_log`,
`dampedMobius_cutoffs_converge_of_prefix_power`, and
`dampedMobius_cutoffs_converge_of_critical_prefix_log`.

The signed scalar prefix remains an **Open** arithmetic premise. This
removes a redundant dependency; it does not prove the missing cancellation.
The scalar quarter-damping limitation discussed in the previous audit
continues to apply.

## 3. Critical logarithmic growth of the complete signed Hilbert prefix

The old strict power premise `‖F_{0,M}‖≤C M^θ`, `θ<ε`, can be replaced by
the eventual critical estimate

\[
 \|F_{0,M}\|\le \frac{C M^\varepsilon}{(\log(2M))^q},\qquad q>1.
\]

`dampedMobius_cutoffs_converge_of_raw_critical_log` proves full natural-order
Hilbert convergence at the same positive damping `ε`;
`dampedMobius_energy_of_raw_critical_log` identifies the canonical finite
energy. An arbitrary real coefficient `C` is permitted in the theorem;
the eventual norm inequality itself forces its relevant nonnegativity.

The generic theorem `signedVector_power_damped_tendsto_of_dini` uses

\[
 \sum_{M\ge1}M^{-1-\varepsilon}\|S_M\|<\infty,
 \qquad M^{-\varepsilon}\|S_M\|\longrightarrow0.
\]

The logarithmic hypothesis supplies both. The threshold `q>1` belongs to
the positive Abel-variation majorant; it is not claimed necessary for
actual arithmetic convergence. Unlike the scalar-prefix route, the norm
retains cancellation in the full arithmetic Hilbert vector.

## 4. Averaged cancellation suffices for finite energy

For finite energy alone the extra boundary-limit hypothesis can be removed:

\[
 \boxed{\quad\sum_{M\ge1}\frac{\|F_{0,M}\|}{M^{1+\varepsilon}}<\infty
 \quad\Longrightarrow\quad
 \sum_{n\ge1}\frac{|f_\varepsilon(n)|^2}{n(n+1)}<\infty.\quad}
\]

This is `dampedMobius_energy_of_raw_signed_dini`. Harmonic-series divergence
forces `M^(−ε)‖F_{0,M}‖≤1` at arbitrarily large cutoffs. The exact Abel
identity then gives a bounded subsequence of damped cutoff norms. Every
finite physical-head energy passes to its scalar coordinate limit under
the same bound, giving summability of the actual canonical energy.

No monotonicity, pointwise power envelope, or boundary limit is assumed.
Full natural-order norm convergence is not asserted from Dini summability
alone.

A further sufficient condition, proved by weighted Young's inequality, is

\[
 \sum_{M\ge1}\frac{(\log(2M))^q\|F_{0,M}\|^2}{M^{1+2\varepsilon}}
 <\infty,\qquad q>1.
\]

This is `dampedMobius_energy_of_log_weighted_raw_signed_sq`. It is an
average over cutoffs, allowing individual exceptional values. The critical
pointwise logarithmic bound with saving `b>1` implies such a square average
by choosing `1<q<2b−1`; this last comparison is explanatory algebra, not
a separately named Lean corollary.

`riemannHypothesis_of_raw_signed_dini_sequence` explicitly concludes RH
when the Dini sums are finite at positive dampings tending to zero. There
is no common bound across damping stages. These arithmetic Dini hypotheses
remain **Open**.

## 5. Exact zero-free consequence of signed cutoff growth

The new fixed-growth theorem proves, for `α,θ≥0`,

\[
 \|F_{\alpha,M}\|\le C M^\theta\ (M\ge1)
 \quad\Longrightarrow\quad
 \zeta(\rho)\ne0\quad
 (\tfrac12+\alpha+\theta<\Re\rho<1).
\]

`zeta_ne_zero_of_dampedMobius_signed_growth` first obtains canonical finite
energy at every `ε>α+θ`. Varying the extra damping and using isolated zeros
removes the possible common shifted zero left by a **single** fixed-damping
finite-energy hypothesis.

The module also proves bounded-cutoff and convergent-cutoff specializations,
and `right_half_zero_forces_dampedMobius_cutoff_growth`: an eligible zero
forces failure of every `C M^θ` bound. Current normalized subhalf growth has
`α+θ=1/2` and gives no interior zero-free strip. A fixed gain `δ>0` in that
exponent would imply the fixed zero-free region `Re(s)>1−δ` inside the
critical strip. Thus even that smaller-looking power gain is substantive
number theory, not a consequence of the existing little-o normalization.

## 6. Literature and symbolic-computation audit

- Burnol, [arXiv:math/0202166](https://arxiv.org/pdf/math/0202166), Theorems
  1.3 and 1.4 explicitly assume RH. Section 4 supplies the finite-energy
  zero-shift strategy used by the existing repository. These conditional
  estimates were not imported as unconditional arithmetic facts.
- Maier–Rassias, [arXiv:1705.09921](https://arxiv.org/pdf/1705.09921),
  Theorem 1.1, proves genuine Möbius power cancellation in unbalanced
  cotangent rows `h≈Bk`, with `B≥k^(2δ)`. Its range does not control the
  balanced growing Gram block needed here. No full signed norm estimate
  was inferred from it.
- Conrey–Myerson, [arXiv:math/0002254](https://arxiv.org/pdf/math/0002254),
  Theorem 1 and Remark 1, gives uniform convergence of a smoothed sawtooth
  expression while identifying the missing integrable domination needed
  for an RH conclusion. Scalar uniform convergence alone is insufficient.
- Báez-Duarte, [New versions of the Nyman–Beurling criterion](https://doi.org/10.1155/S0161171202013248),
  Proposition 4.9, proves failure of natural raw L² convergence. The
  discussion after Proposition 4.12 treats unbounded raw norms as following
  from a stronger conjectural Mertens oscillation. These are distinct
  claims. Bounded raw cutoffs implying RH is recorded only as a conditional
  structural theorem, not proposed as an established or likely estimate.

Wolfram independently checked the power-tail integral, the exponent
feasibility reduction, the model logarithmic tail integral, and the band
amplification `exp((A/log M)log M)=exp A`. Symbolic computation was used for
algebraic guidance only; the mathematical declarations are checked by Lean.

## 7. Remaining arithmetic target

No audited verified provider supplies the Dini condition, the critical
signed logarithmic estimate, or the required scalar prefix estimate at
any fixed `0<ε<1/2`. The shrinking-band result reaches below the endpoint
only at finite cutoffs and approaches `1/2`, not zero.

The weakest of the new signed-Abel sufficient inputs for fixed
canonical energy is the Dini condition in Section 4. For full
natural-order convergence, add its vanishing Abel boundary, or establish
the critical signed bound with logarithmic saving `q>1`. Proving Dini
finiteness along positive dampings tending to zero would prove RH; the
new theorem states that assumption explicitly and does not discharge it.

**Quantitative status updated:** `DampedMobiusHalfHilbertRate.lean` now
proves `dampedMobius_half_cutoffs_log_rate`, with error at most
`C*(6+log(M+1))^(-1/4)` at every cutoff. The finite head has the stronger
squared-error bound `D*(6+log M)^(-3)`. The quantitative increasing Abel
transfer gives convergence whenever
`(1/2-epsilon)*log(M+1)-(1/4)*log(6+log(M+1)) -> -infinity`, including
every coefficient `c<1/4` log-logarithmic band and arbitrary divergent
slack at the critical coefficient. Critical-band signed bounds are also
proved. Fixed subhalf membership remains Open. See
`QuantitativeEndpointContinuation20260927.md` for the proof and audit.

## Verification

All final modules are accepted through the project checkpoint. Isolated
checks of the principal results report only `propext`, `Classical.choice`,
and `Quot.sound`; all substantive arithmetic premises remain in theorem
types. The theorem catalog separates unconditional results, established
analytic transfers, and open arithmetic providers.
