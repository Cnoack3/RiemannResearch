# Arithmetic series convergence: a concrete next proof plan

September 10, 2026. The complete kernel jump-energy identity and explicit
summability of its jump-square series have now passed the coordinated Lean
verification and axiom audit. The all-scale weighted jump estimate and the
resulting low-damping arithmetic series summability **remain unverified**.
This note distinguishes that next arithmetic provider from the already
available operator contraction and exact finite residual.

Write `T_m` for the existing scaled integer dilation, `Q` for the actual
dyadic quotient projection, `A=T_2^*/2`, and `K=I-T_2 T_2^*/2`. Let
`w(k)=1/(k(k+1))` for positive integers, and let `F_m=T_m R_3`, so

\[
F_m(n)=m(\lfloor n/m\rfloor\bmod 3).
\]

## Exact identities supporting the estimate

The existing complete resolvent theorem supplies

\[
\|Qf\|^2=\frac12\left\|K\sum_{j\ge0}A^j f\right\|^2.
\]

The new `DyadicKernelJumpEnergy.lean` verifies, with explicit
summability of the nonnegative series,

\[
\|Kf\|^2=\frac{f(1)^2}{2}
 +\sum_{\ell\ge1}\frac{(f(2\ell+1)-f(2\ell))^2}{2(2\ell+1)^2}.
\]

Every signed increment remains inside its complete square. Inequalities
enter only in the subsequent convergence estimate.

## Targeted missing provider

For every positive integer `m` and nonnegative integer `j`, prove

\[
\boxed{\|K A^j T_mR_3\|\le6.}
\]

The j=0 case is now verified with the stronger bound 2, via
`dyadicKernelDefect_residue_three_norm_sq_le_four` in
`DyadicResidueKernelEnergy.lean`. Even dilations have zero first-block energy.

This is the sole missing arithmetic block estimate in the proposed
convergence route. Existing Hilbert contraction estimates handle the
remaining tail. A Lean signature is

```lean
theorem dyadicKernelDefect_halfAdjoint_triadicResidue_norm_le
    (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ‖dyadicKernelDefect
      (RiemannResearch.Analysis.AbelCoboundary.orbit dyadicHalfAdjoint
        (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j)‖ ≤ 6
```

The sharper geometric estimate `‖K A^j T_mR_3‖≤2m·2^{-j}` is optional;
it is not needed for the depth bound or arithmetic series summability.

## Ordinary proof of the uniform block estimate

Put `d=2^j`. Adjoint composition and the existing physical adjoint coordinate
formula should give, for `k≥1`,

\[
g(k):=(A^jF_m)(k)
=\frac1{w(k)}\sum_{n=dk}^{d(k+1)-1}w(n)F_m(n).
\]

The coefficients in this sum have total mass `1/d`, by the existing exact
weight-block identity. Since `0≤F_m≤2m`, it follows that `0≤g≤2m/d` and
therefore `‖Kg‖≤‖g‖≤2m/d`. This would provide the optional sharper
geometric estimate. It is convenient inside the ordinary argument but
need not be formalized as a separate all-scale theorem.

It remains to show a uniform bound when `d≤m`. For each `ℓ≥1`, define the
finite set of jumps inside the combined pair of blocks by

\[
J_\ell=\{r\ge1:2d\ell<rm<2d(\ell+1)\}.
\]

The sequence `F_m` changes only at `rm`. Its signed increment there is
`m` when `3∤r` and `-2m` when `3∣r`. Hence its oscillation on the combined
interval is at most `2m|J_ℓ|`. Each normalized weighted block average is
`1/d` times a convex average, giving

\[
|g(2\ell+1)-g(2\ell)|\le\frac{2m}{d}|J_\ell|.
\]

The interval length is `2d≤2m`, with strict endpoints, so `|J_ℓ|≤2`.
Consequently its entire kernel-energy contribution satisfies

\[
\frac{(g(2\ell+1)-g(2\ell))^2}{2(2\ell+1)^2}
\le 4\frac{m^2}{d^2}\sum_{r\in J_\ell}\frac1{(2\ell+1)^2}
\le16\sum_{r\in J_\ell}\frac1{r^2}.
\]

The last inequality uses `rm<2d(ℓ+1)≤2d(2ℓ+1)`. The `J_ℓ` are pairwise
disjoint. Summing thus gives at most `16Σ_{r≥1}r^{-2}≤32`, using the
elementary telescoping majorant `r^{-2}≤2/[r(r+1)]`.

For the first coordinate, the physical block is `[d,2d)`. Under `d≤m`, it
lies below `2m`, so `F_m` takes only the values `0,m` on it. If `m≥2d`,
the coordinate vanishes; otherwise `g(1)≤m/d<2`. Thus the first-coordinate
energy is at most `2`. The exact kernel formula gives `‖Kg‖²≤34≤36`.
When `d>m`, existing Hilbert contraction also suffices:
`‖Kg‖≤‖A^jF_m‖≤sqrt(m/d)‖R_3‖≤‖R_3‖≤2≤6`.
The elementary residue bound `0≤R_3≤2` supplies the last comparison.

The claims needing formalization are precisely: the power-adjoint block
formula, the weighted two-block oscillation estimate, the finite jump-set
count and disjointness, and the summable comparison. They are ordinary
positive-weight and discrete-jump arguments; no Möbius cancellation is
used in these proposed norm estimates.

## Preferred consequence: retain the exact finite residual

For any `N` with `m≤2^N`, the already-proved finite packet identity is

\[
QF_m=QK\sum_{j<N}A^jF_m+QA^NF_m.
\]

Its actual Lean endpoint is `dyadicCriticalPacket_error_eq` in
`RH/DyadicCriticalApproximation.lean`. The identification of its packet
with the displayed finite sum uses `dyadicHalfAdjoint_orbit_eq` in that
same module. The terminal bound follows from the existing
`dyadicHalfAdjoint_orbit_norm_sq_le` and `hilbertDilation_norm_sq`:

\[
\|QA^NF_m\|^2\le\|A^NF_m\|^2
\le2^{-N}\|T_mR_3\|^2
=m2^{-N}\|R_3\|^2\le\|R_3\|^2.
\]

On the finite initial packet, the proposed uniform block estimate gives
`‖Σ_{j<N}KA^jF_m‖≤6N`. This vector lies in the adjoint kernel, so the
existing `dyadicQuotientProjection_kernel_norm_sq` supplies its exact
projection factor `1/sqrt(2)`. Consequently the proposed block estimate
would give the depth bound

\[
\boxed{\|QT_mR_3\|\le\frac{6N}{\sqrt2}+\|R_3\|
\quad(m\le2^N).}
\]

This finite residual route avoids a new infinite-tail theorem and retains
the exact terminal vector until its norm is estimated.

An alternative using the complete resolvent also needs no sharper
geometric provider. The already-proved `dyadicHalfAdjoint_orbit_norm_le`
in `RH/DyadicCriticalResolvent.lean` gives the factor `(3/4)^k` after
shifting the orbit to `A^NF_m`, whose norm is at most `‖R_3‖` by the
preceding squared bound. Kernel contraction then bounds the resolvent
tail by `4‖R_3‖`. Combined with the initial `6N`, this yields

\[
\|QT_mR_3\|\le\frac{6N+4\|R_3\|}{\sqrt2}.
\]

The finite residual route above has a better constant and fewer steps.
Neither consequence has yet been established unconditionally because
the uniform all-scale block estimate is still missing.

## From depth growth to the actual product series

Choosing a dyadic depth gives logarithmic growth. Applied at `m=n3^j`,
this majorizes the norm of the actual arithmetic term by a constant times

\[
n^{-1-\varepsilon}3^{-\varepsilon j}(1+\log n+j).
\]

This product majorant is summable for every `ε>0`. It would discharge the
actual Hilbert-valued product-index series convergence in the handoff.

For Lean, dyadic shell grouping avoids logarithms entirely. In the shell
`2^N≤n<2^(N+1)`, one has `n3^j≤2^(N+1+2j)`. There are at most `2^N`
indices in the shell. Using `|μ(n)|≤1`, the sum of term norms within that
shell is therefore at most

\[
2^{-\varepsilon N}3^{-\varepsilon j}
 \left(\frac{6(N+1+2j)}{\sqrt2}+\|R_3\|\right).
\]

Its double sum over `N,j≥0` is a combination of geometric zeroth and
first moments, convergent for every positive damping. This grouping is
applied only to the nonnegative norm majorant and discards no signed
term from the arithmetic family.

**This conclusion remains conditional on verifying the missing provider
and the summable-majorant argument.** It does not supply the uniform
normalization remainder, Mellin limits, complementary-energy recovery,
full legal approximation, or RH.
