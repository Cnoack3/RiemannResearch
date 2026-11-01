# Squarefree Mobius heads: complete Cesaro energy and signed repair

Date: November 1, 2026.
Baseline: `6b53ff6d66ca30dee9b96eb8f07ebf48c5975e94`.

## Conclusion and scope

The explicit family admits substantially better complete-energy bounds than the
coefficient-supremum estimate in the initial agenda. Two squarefree repair
conductors suffice to cancel its limiting Cesaro mean exactly. This produces an
explicit cubic far-tail certificate, while retaining every composite squarefree
prefix conductor and every signed cross term in the exact objective.

The zero lower-logarithmic-growth condition remains **Open**. In particular,
neither the new cubic tail estimate nor the unconditional paper bound `E=o(H)`
is a proof of RH. A finite weighted quadratic estimate on a growing transition
window is isolated below as the next arithmetic target.

New Lean verification covers the centered identities, coefficient-dependent
complete-tail inequalities, signed averaging, two-repair constraints, exact
heads, actual coefficients, and literal squarefree membership. The global
square-root-envelope estimate, asymptotic `o(H)` comparison, polynomial budget
bound, finite-window reduction, and completeness of repair parametrization
below are paper proofs, not additional newly checked declarations.

## 1. Exact weighted energy, including its signed terms

For positive integers set

\[
a_H=\sum_{d\le H}\frac{\mu(d)}d,\qquad
M_H=\sum_{d\le H}\mu(d),\qquad
q_t=\frac2{(t+1)(t+2)},\qquad
\mathcal E(F)=\sum_{t\ge1}q_t(CF(t))^2.
\]

Here `C` averages the coordinates **1 through t**, as in the existing project.
For `r=t mod d` define the signed endpoint defect

\[
\delta_d(t)=\frac{r(d-2-r)}{2d}.
\]

The exact formula and uniform defect estimate are

\[
Cg_d(t)=\frac{d-1}{2d}-\frac{\delta_d(t)}t,
\qquad |\delta_d(t)|\le\frac d8.                 \tag{1}
\]

The defect may be negative. In particular the factor is `d-2-r`, not `d-1-r`;
the latter would correspond to an incorrect shift of the positive-index sum.
Formula (1) follows from the existing quotient/remainder formula. Its bound
follows from `0<=r<=d-1`, `r(d-1-r)>=0`, and completing a square.

For the original single repair define

\[
L_{H,D}=\frac{Da_H-M_H}2,\quad
R_{H,D}(t)=\sum_{d\le H}\mu(d)\delta_d(t)-Da_H\delta_D(t),
\quad B_{H,D}=\frac18\left(\sum_{d\le H}|\mu(d)|d+|a_H|D^2\right).
\]

Then, exactly,

\[
CF_{H,D}(t)=L_{H,D}+R_{H,D}(t)/t,
\]
\[
\boxed{\mathcal E(F_{H,D})=
\frac H{H+2}+\sum_{t>H}q_t\left(L_{H,D}+\frac{R_{H,D}(t)}t\right)^2.}       \tag{2}
\]

Expanding the square gives `L^2+2LR/t+R^2/t^2`; the middle summand is signed.
The square `R^2` contains all products between distinct squarefree conductors,
including composites, and all repair-prefix products. No diagonal replacement
or independent-coordinate approximation is used.

Since `|R|<=B`, for every cutoff `T>=0` the **entire** omitted tail satisfies

\[
\boxed{\sum_{t>T}q_t(CF_{H,D}(t))^2
\le\frac2{T+2}\left(|L_{H,D}|+\frac{B_{H,D}}{T+1}\right)^2.}              \tag{3}
\]

The finite prefix plus (3) is a complete upper certificate, and the prefix
alone is a lower certificate. Constants depend on the actual coefficients.

## 2. A better global bound and the cost of a large repair

This subsection is a paper argument using the actual weighted norm.
Write `r_d=d g_d`. On `t<d`, `Cr_d(t)=(t+1)/2`; on all positive endpoints,
`|Cr_d(t)|<=d/2` by the existing residue-mean bound. Consequently

\[
\mathcal E(r_d)
\le \frac{d-1}2+\frac{d^2}{2(d+1)}\le d,
\qquad \mathcal E(g_d)\le 1/d.                     \tag{4}
\]

The head sum in (4) uses
`q_t((t+1)/2)^2=(t+1)/(2(t+2))<=1/2`; the remaining mass is `2/(d+1)`.
Let `P_H=-sum_{d<=H} mu(d)g_d`. First retain the exact signed equality

\[
\mathcal E(F_{H,D})=\mathcal E(P_H)
+2a_H\langle CP_H,Cr_D\rangle_q+a_H^2\mathcal E(r_D).
\]

The triangle inequality and `sum_{d<=H}d^{-1/2}<=2 sqrt(H)` then give

\[
\boxed{\mathcal E(F_{H,D})
\le (2\sqrt H+|a_H|\sqrt D)^2
\le 8H+2Da_H^2.}                                    \tag{5}
\]

This improves both the quadratic dependence on the head and the quadratic
dependence on a distant repair conductor in the elementary bound. It remains
a linear-scale estimate when `D` is comparable to `H`.

Moving the repair arbitrarily far away has a real cost. Since `a_H!=0`, if
`D>=4H/|a_H|`, then for `ceil(D/2)<=t<D`, the unwrapped repair and the bound
`|CP_H(t)|<H/2` give `|CF_{H,D}(t)|>=|a_H|D/8`. For `D>=4`, that interval
has q-mass at least `1/(2D)`. Therefore

\[
\mathcal E(F_{H,D})\ge a_H^2D/128.                  \tag{6}
\]

For fixed `H`, the complete energy is thus of order `D a_H^2` as `D` tends
to infinity. A huge primorial is a valid existence witness, but offers no
automatic energy advantage. The scale in (6) depends on `a_H`; it is not a
uniform lower bound for every `D>H`.

## 3. Signed repairs and exact cancellation of the limiting mean

For any finite real weights with `sum_i w_i=1` and squarefree `D_i>H`, let
`Fbar=sum_i w_i F_{H,D_i}`. It has exact head one and is a literal finite
squarefree combination. The exact Cesaro formula is

\[
C\bar F(t)=\frac{a_H\sum_i w_iD_i-M_H}{2}
+\frac{\sum_{d\le H}\mu(d)\delta_d(t)
-a_H\sum_i w_iD_i\delta_{D_i}(t)}t.                 \tag{7}
\]

The prefix occurs once in (7), even when the averaging weights are large.
The appropriate budget is

\[
B(\bar F)=\frac18\left(\sum_{d\le H}|\mu(d)|d
+|a_H|\sum_i|w_i|D_i^2\right).
\]

If `a_H sum_i w_i D_i=M_H`, (3) becomes the newly checked cubic estimate

\[
\boxed{\sum_{t>T}q_t(C\bar F(t))^2
\le\frac{2B(\bar F)^2}{(T+2)(T+1)^2}.}             \tag{8}
\]

This is decay in the tail cutoff, not yet a small bound as the head moves.

Two distinct repairs `H<D<E` already suffice. Put

\[
w_D=\frac{Ea_H-M_H}{(E-D)a_H},\qquad
w_E=\frac{M_H-Da_H}{(E-D)a_H}.
\]

The existing theorem `mobiusReciprocalSum_ne_zero` permits these definitions
for every `H>=1`. The new checked constraints are `w_D+w_E=1` and
`a_H(w_DD+w_EE)=M_H`. The resulting `meanNeutralMobiusHead` has actual form

\[
F_H^0=-\sum_{d\le H}\mu(d)g_d+\alpha_Hg_D+\beta_Hg_E,
\quad
\alpha_H=\frac{D(Ea_H-M_H)}{E-D},\quad
\beta_H=\frac{E(M_H-Da_H)}{E-D}.                    \tag{9}
\]

Thus `alpha/D+beta/E=a_H`, `alpha+beta=M_H`. A small `a_H` can make the
weights large, but cancels out of the actual coefficients in (9). Bounding
the prefix by `sum |w_i|` would introduce an avoidable loss.

Nonnegative repair weights cannot cancel the mean when `M_H/a_H<=H`, because
their weighted mean conductor is strictly greater than `H`. Signed weights
remove that obstruction. Canceling the limiting mean alone need not minimize
the full energy: the transition region still matters.

## 4. Unconditional sublinear energy at comparable repair scales

This subsection is a paper deduction from existing checked results; its
asymptotic assembly has not been newly formalized here.

Let `Ecan(H)=E(canonicalMobiusHead H)`, using repair `H+1` even when it is not
squarefree. The existing weighted Cesaro contraction and
`canonicalMobiusHilbert_sublinear` imply `Ecan(H)=o(H)`. Existing reciprocal
Mobius cancellation and its finite Abel identity also give
`a_H->0` and `M_H/H->0`.

For `H<D<=2H`, the difference from the canonical witness is
`a_H(r_D-r_{H+1})`, is zero through `H`, and has Cesaro absolute value at most
`|a_H|(D+H+1)/2`. The actual tail mass is `2/(H+2)`. The squared-norm
inequality `E(U+V)<=2E(U)+2E(V)`, obtained from the exact signed quadratic
identity, yields

\[
\mathcal E(F_{H,D})\le2Ecan(H)+
\frac{a_H^2(D+H+1)^2}{H+2}=o(H).                   \tag{10}
\]

For the mean-neutral pair, also choose `2D<=E<=4D`. The exact difference is

\[
F_H^0=F_{H,D}+b_H(r_E-r_D),\qquad
b_H=\frac{M_H-Da_H}{E-D}.
\]

The same argument, and `(E+D)/(E-D)<=3`, give the explicit comparison

\[
\boxed{\mathcal E(F_H^0)\le4Ecan(H)+104H a_H^2+18M_H^2/H=o(H).}            \tag{11}
\]

To check the constants, combine
`2 a_H^2(D+H+1)^2/(H+2)<=32H a_H^2` with
`9(M_H-Da_H)^2/(H+2)<=18M_H^2/H+72H a_H^2`.
Primes supplied by Bertrand's postulate provide `H<D<=2H` and
`2D<E<=4D`; they are valid squarefree repairs. Composite squarefree prefix
conductors are still all retained.

These estimates give a rigorous improvement over an elementary polynomial
supremum bound. They do **not** give `E<=H^{1-delta}` for any fixed positive
delta, or zero lower logarithmic exponent: for example `H/log H=o(H)` has
logarithmic growth exponent one.

## 5. A finite-window target for the remaining RH condition

For the scale choices in Section 4, `|a_H|<=1`, `|M_H|<=H`, and (9) give
`|alpha_H|<=9H`, `|beta_H|<=6H`. Hence the actual budget satisfies

\[
B_H=\frac18\left(\sum_{d\le H}|\mu(d)|d
+|\alpha_H|D+|\beta_H|E\right)\le\frac{67}{8}H^2\le9H^2.               \tag{12}
\]

Let `T_H=ceil(H^{4/3})`. Applying the checked bound (8) and the paper budget
(12) bounds the whole tail after `T_H` by 162, uniformly in `H>=1`.
With

\[
R_H(t)=\sum_{d\le H}\mu(d)\delta_d(t)
-\alpha_H\delta_D(t)-\beta_H\delta_E(t),
\quad
W_H=\sum_{H<t\le T_H}\frac{2R_H(t)^2}{t^2(t+1)(t+2)},
\]

the exact split and upper bound are

\[
\frac H{H+2}+W_H\le\mathcal E(F_H^0)
\le\frac H{H+2}+W_H+162.                          \tag{13}
\]

Consequently it is enough to prove zero lower logarithmic growth of `W_H`
along a cofinal sequence. This reduction retains every coordinate: the
infinite tail is explicitly bounded, not discarded.

**Next specific arithmetic estimate, Open:** for each `epsilon>0`, obtain on
a cofinal family the block estimates

\[
\sum_{T<t\le2T} R_H(t)^2
\ll_\epsilon H^{3+\epsilon}T,
\qquad T=2^kH,\quad H\le T<T_H.                   \tag{14}
\]

Use a truncated final block, or bound it by the complete block. Multiplying
by `2/T^4` and summing the geometric series gives `W_H<<_epsilon H^epsilon`.
The critical estimate is cancellation in the **complete signed quadratic
form** of the periodic defects and repairs. The elementary bound `|R_H|<=9H^2`
only gives linear-scale energy near `T~H`, so it does not supply (14).

## 6. What unrestricted deterministic repair averaging can and cannot add

Here is a paper structural observation, not a newly checked declaration.
Take any finite sum `F=sum_{d>=2}c_d g_d` with `F(n)=1` for `1<=n<=H`.
At `n=1`, its reciprocal coefficient charge is `sum c_d/d=1`. Since
`Delta g_d(n)=1/d-1_{d|n}`, for `2<=n<=H` one obtains
`sum_{d|n,d>=2}c_d=1`. Finite Mobius inversion, or induction on `n`, forces

\[
c_d=-\mu(d)\quad(2\le d\le H).
\]

The remaining coefficients obey `sum_{D>H}c_D/D=a_H`. Since `a_H!=0`, setting
`w_D=c_D/(Da_H)` gives `sum w_D=1` and expresses `F` as a deterministic signed
average of the original `F_{H,D}`. For squarefree support, all repair
conductors in this representation are squarefree.

Thus unrestricted signed repair averaging parametrizes the whole finite
squarefree exact-head class, not merely a small proposed subclass. The freedom
is useful, but no easier asymptotic theorem follows from the parametrization.

For a finite repair set, use the actual complete-tail Gram matrix
`K_ij=sum_{t>H}q_t CF_{H,D_i}(t) CF_{H,D_j}(t)`. The exact objective is
`H/(H+2)+w^T K w`, with `1^T w=1`; optionally impose `a_H D^T w=M_H`.
The existing signed projection and complete Gram declarations supply the
finite optimization framework. Optimizing a truncated numerical matrix is
only a way to propose weights; the missing tail must still be certified.

The sharp general obstruction remains the existing actual-zeta theorem: a
hypothetical zero with real part `sigma>1/2` forces every legal exact-head
family, including these signed averages, to have energy at least
`c_rho H^{2sigma-1}` eventually. Mean neutrality cannot remove this Mellin
obstruction. Obtaining (14) or its cofinal weaker version is the substantive
unresolved arithmetic step.

## 7. Reproducible exact rational example

For `H=16`, choose squarefree repairs `D=17`, `E=65=5*13`. Then

\[
a_H=304/5005,\quad M_H=-1,\quad
\alpha_H=2159/1232,\quad \beta_H=-3391/1232,
\quad B_H=182151/4928.
\]

The adjacent script `MobiusCesaroEnergyCertificate20261101.md` uses only
Python `Fraction` arithmetic for the comparisons. A sum through 256 plus
(8) proves

\[
0.930<\mathcal E(F_{16}^0)<0.931.
\]

For the original single repair `F_{16,17}`, a sum through 1024 plus (3) gives
`1.002<E(F_{16,17})<1.005`. The intervals are strictly separated. The two
repair construction therefore reduces actual complete energy in this example,
not merely a truncated objective. This finite computation is **external exact
arithmetic**, not a Lean-checked finite certificate and not an asymptotic claim.

Additional floating-point diagnostics at heads 16, 32, 64, 128, 256 and 512
used all Mobius prefix terms, 15--16 squarefree repair choices between `H+1`
and approximately `4H`, and cutoffs `256H`. Truncated quadratic minimization
reduced the observed energies, but neither those computations nor a selected
sequence of small energies supplies a cofinal bound. They are deliberately
not used as evidence for an asymptotic theorem.

## 8. Lean declarations and verification

`CesaroResidueMean.lean` now supplies `residueCesaroDefect`,
`cesaro_residue_centered`, and `residueCesaroDefect_abs_le`.
`MultiRangeEnergyCertificates.lean` now supplies the general
`conditionalMeanTailSquare_le_centered`.

The new `SquarefreeMobiusCesaroEnergy.lean` supplies:

- `squarefreeMobiusHead_cesaro_centered`, `squarefreeMobiusHead_energy_identity`,
  `squarefreeMobiusHead_tail_bound`;
- `squarefreeMobiusHead_average_cesaro_centered`,
  `squarefreeMobiusHead_average_tail_bound`,
  `squarefreeMobiusHead_average_cubic_tail`;
- `mobiusRepairWeights_constraints`, `meanNeutralMobiusHead_exact`,
  `meanNeutralMobiusHead_cubic_tail`, `meanNeutralMobiusHead_coefficients`,
  and `meanNeutralMobiusHead_mem_divisorSpan`;
- the associated explicit remainder and coefficient-budget definitions and bounds.

The complete assembled development and eight principal axiom inspections
succeeded in job `job_uJxnlDZLirddx6QsjFtZ1hRsAY5hX3cR`:
`verified=true`, `classification=success`, `exit_code=0`, whole-job duration
35.979 seconds. Each inspected endpoint used only `propext`, `Classical.choice`,
and `Quot.sound`. The earlier centered-residue/general-tail development
succeeded in `job_n3F0AvXnXbERHAXWyTYK0VPvcJElwGuv` in 37.192 seconds.
Intermediate compiler failures were repaired before this successful audit.

These are development receipts. The final saved-source checkpoint is the
publication gate and its terminal receipt determines the saved-project
validation scope. No isolated snippet is represented as a complete repository
check. Workspace-opening and polling latency were not instrumented; queue
admission was position one, and the durations above include dependency/import
preparation rather than measuring kernel checking alone.

## Status ledger

| Result | Status |
|---|---|
| Exact signed mean/remainder and complete energy identities | Newly Lean checked in development; saved-source checkpoint gate applies |
| Explicit two-repair heads, actual coefficients, squarefree membership | Newly Lean checked in development; saved-source checkpoint gate applies |
| Coefficient-dependent cubic complete-tail bounds | Newly Lean checked in development; saved-source checkpoint gate applies |
| Global bound (5), distant-repair lower bound (6), comparable-scale `o(H)` | Proved on paper here, not newly formalized |
| Polynomial budget (12), finite-window reduction (13) | Proved on paper from explicit coefficients and checked tail estimate |
| Head-16 separated complete-energy intervals | External exact rational computation |
| Cofinal subpolynomial finite-window estimate (14) or a weaker sufficient bound | Open |
| RH from zero lower logarithmic growth | Existing conditional research reduction; provider still Open |
