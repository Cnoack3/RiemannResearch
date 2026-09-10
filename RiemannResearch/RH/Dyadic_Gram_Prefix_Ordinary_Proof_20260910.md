# Exact dyadic Gram kernel and an elementary logarithmic prefix estimate

Source: the user-supplied `DyadicRegularizedVerificationContinuation20260910 (1).md`.
Date: September 10, 2026.

**Verification status:** The argument below is an ordinary mathematical proof candidate derived during this continuation. Its tent representation, logarithmic majorant, and prefix estimate have not been checked in Lean. The orthogonal boundary identities and the minimum-denominator spacing lemma used below have been source-checked in this pass; the exact tent representation, logarithmic block sum, and their assembled consequence remain unverified in Lean. This note does not establish the Möbius-series convergence, normalization remainder, Mellin limits, full two-seed completion, or RH.

## 1. Exact finite orthogonal expansion

Write `V_m=Q T_m 1` and `B_l=Q d_l`, for positive integer indices. The physical recurrence and orthogonality give

\[
V_1=V_2=1,\quad V_{2l}=V_l,\quad
V_{2l+1}=\tfrac12(V_l+V_{l+1})+B_l,
\]
\[
\langle B_l,1\rangle=0,\qquad
\langle B_l,B_k\rangle=\tfrac14\mathbf1_{l=k}.
\]

For `r≥0` and `2^r≤l<2^(r+1)`, define the dyadic tent on `[1,2]`

\[
\phi_l(t)=\max\{0,1-|2^{r+1}t-(2l+1)|\}.
\]

Its support is the interval `[l/2^r,(l+1)/2^r]`, its height is one, and its midpoint is `(2l+1)/2^(r+1)`.

**Finite expansion.** If `2^K≤m≤2^(K+1)` and `t=m/2^K`, then

\[
V_m=1+\sum_{r=0}^{K-1}\ \sum_{l=2^r}^{2^{r+1}-1}\phi_l(t)B_l. \tag{1}
\]

Proof: induct on `K`. The initial grid has endpoints `V_1=V_2=1`. At an even grid point the recurrence identifies the vector with the previous grid and every new-level tent vanishes. At an odd grid point, the vector is the average of its two neighboring vectors on the previous grid plus the new boundary `B_l`. Every earlier tent is affine on the interval between those neighbors: its breakpoints belong to the previous grid. Thus its midpoint value is the average of its endpoint values. The unique new-level tent at the midpoint has coefficient one; all other new-level tents vanish. This proves (1), including both endpoints.

For a dyadic rational `t`, all tents at levels at or above any denominator depth vanish. Hence (1) may be written as a finite-support sum over all positive `l`, independently of the chosen denominator depth.

For two normalized integer mantissas `t_m,t_n`, orthogonality gives the **exact** identity

\[
\langle V_m,V_n\rangle
=1+\frac14\sum_{r\ge0}\sum_{l=2^r}^{2^{r+1}-1}
\phi_l(t_m)\phi_l(t_n). \tag{2}
\]

The sum is finite. For arbitrary finite signed coefficients `c_i`, this also gives

\[
\left\|\sum_i c_iV_{m_i}-1\right\|^2
=\left(\sum_i c_i-1\right)^2
+\frac14\sum_{l\ge1}\left(\sum_i c_i\phi_l(t_{m_i})\right)^2. \tag{3}
\]

Thus all signed mixed terms are retained, inside exact squares. No coefficient positivity is assumed.

## 2. A logarithmic majorant for distinct mantissas

At each level `r`, at most one tent is nonzero at a given point; every tent lies between zero and one. If a product of two tents at that level is positive, their two arguments belong to the interior of the same interval of length `2^(-r)`. Consequently, if `d=|t_m-t_n|>0`, that level can contribute only when `d<2^(-r)`.

Since `0<d≤1`, the number of contributing levels is at most

\[
1+\frac{\log(1/d)}{\log2}.
\]

Therefore

\[
0\le\langle V_m,V_n\rangle-1
\le\frac14+\frac{\log(1/d)}{4\log2}. \tag{4}
\]

For the triadic indices `m=3^(j+1)`, put `α=log3/log2`. Their normalized mantissas are `t_j=2^{\{(j+1)α\}}`. For distinct `j,k`, put `h=|k-j|` and `δ_h=dist(hα,ℤ)`. Irrationality of `α` follows from the impossibility of `3^q=2^p` for positive `p,q`. On `[0,1]`, the derivative of `2^x` is at least `log2`, so

\[
|t_j-t_k|\ge(\log2)\,
|\{(j+1)α\}-\{(k+1)α\}|
\ge(\log2)\delta_h. \tag{5}
\]

Combining (4) and (5), define for `h≥1`

\[
a_h=\frac54+
\frac{\log(1/\log2)+\log(1/\delta_h)}{4\log2},
\qquad a_0=0. \tag{6}
\]

Then the raw Gram bound required by the assembly is

\[
|\langle V_{3^{j+1}},V_{3^{k+1}}\rangle|\le a_{k-j}
\quad(j<k). \tag{7}
\]

The absolute value causes no loss here: (2) proves the raw Gram is at least one.

## 3. Elementary prefix lemma; no continued fractions are needed

**Lemma.** Let `α` be irrational and `δ_h=dist(hα,ℤ)`. Suppose a constant `C≥0` satisfies

\[
\log(1/\delta_h)\le Ch\quad(h\ge1). \tag{8}
\]

Then for every positive integer `N`,

\[
\sum_{h=1}^N\log(1/\delta_h)
\le 2(C+1+\log4)N. \tag{9}
\]

**Proof.** Choose `q∈{1,…,N}` attaining the minimum of `δ_h` over this finite set. For each positive integer `h`, choose a nearest integer `p_h` to `hα`.

For `1≤h<q`, the integer `q p_h-h p_q` is nonzero. Indeed, if it vanished then

\[
hα-p_h=\frac hq(qα-p_q),
\]

and hence `δ_h=(h/q)δ_q<δ_q`, contradicting minimality. Therefore

\[
1\le|q p_h-h p_q|
\le q\delta_h+h\delta_q
\le(q+h)\delta_h<2q\delta_h.
\]

It follows that

\[
\delta_h>\frac1{2q}\quad(1\le h<q). \tag{10}
\]

Partition the integers `{1,…,N}` into consecutive blocks of length at most `q`. Within a block, the circular distance between two distinct orbit points is `δ_h` for some `1≤h<q`, and so exceeds `1/(2q)`.

In a block of size `s≤q`, sort the distances to zero as `d_1≤⋯≤d_s`. For `i≥2`, the `i` corresponding points lie in the centered circular arc of length `2d_i`; their spacing gives

\[
2d_i>\frac{i-1}{2q},\qquad
d_i>\frac{i-1}{4q}. \tag{11}
\]

All block indices are at most `N`, so minimality also gives `d_1≥δ_q`, and (8) bounds its logarithm by `Cq`. Thus the contribution of one block is at most

\[
Cq+\sum_{i=1}^{q}\log(4q/i)
\le(C+1+\log4)q. \tag{12}
\]

Here `log(q!)≥q log q-q` follows by integrating the increasing function `log x` on `[1,q]`. There are `ceil(N/q)` blocks and `q ceil(N/q)≤N+q≤2N`. Summing (12) proves (9). For `q=1`, there are no spacing terms and the same estimate is immediate. ∎

## 4. Exponential separation for `log3/log2`

Take `α=log3/log2`, `q≥1`, and a nearest integer `p` to `qα`. Then `|qα-p|≤1/2` and `p≥1`. The positive integers `3^q` and `2^p` are distinct, so their distance is at least one. The mean value estimate for the exponential yields

\[
1\le|3^q-2^p|
\le\max(3^q,2^p)|q\log3-p\log2|
\le 2\,3^q(\log2)\delta_q
\le2\,3^q\delta_q.
\]

Therefore `δ_q≥1/(2·3^q)` and

\[
\log(1/\delta_q)\le\log2+q\log3\le q\log6. \tag{13}
\]

Applying (9) with `C=log6` gives

\[
\sum_{h=1}^N\log(1/\delta_h)
\le2(1+\log24)N. \tag{14}
\]

Equations (6) and (14) furnish the explicit linear majorant

\[
\sum_{h=1}^N a_h\le AN,\qquad
A=\frac54+\frac{\log(1/\log2)+2(1+\log24)}{4\log2}. \tag{15}
\]

Taking `a_0=0` also gives the corresponding `Finset.range N` prefix bound, if that is the project's convention.

## 5. What this would discharge

After Lean verification of (1), the elementary rotation lemma, and their connection to the actual projected steps, (7) and (15) would supply the off-diagonal majorant and linear prefix provider of `DyadicRegularizedGramAssembly.lean` without further analytic assumptions. The existing logarithmic diagonal provider already handles the diagonal.

This would establish a uniform norm bound for the actual damped step average. It would still leave the product-index Möbius series, arithmetic identification, normalization remainder, and the scalar limiting providers open. In particular, it would not establish unconditional (N2) or RH.
