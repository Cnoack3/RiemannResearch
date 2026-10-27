# Physical doubling: exact drift, closure obstruction, and measure change

27 October 2026. Continuation of the user's prime-resampling agenda and explicit
request to attack physical doubling using DPP and dQ/dP. These results do not
prove RH. The remaining arithmetic obligation is stated below.

Let Q(n)=1/(zeta(2)n²), P(n)=1/(n(n+1)), g_d(n)=(n mod d)/d, and
V be the closed Q span of squarefree g_d with d≥2. Let P_V denote its
orthogonal projection, r=1−P_V1, and e=‖r‖². Zero is the null physical
coordinate. Physical doubling is T f(n)=f(2n); it differs both from floor
dilation f(floor(n/2)) and from the dyadic conditional projection C₂.

## Established physical operator and exact drift

[QArgumentDoubling.lean](QArgumentDoubling.lean) constructs T as an actual continuous linear operator
using the existing complete Q/Pareto equivalence. Reindexing the whole even
progression gives E_Q[Tf]=4⟨f,1_even⟩. Since 1_even=1−2g₂ and r⊥g₂,

$$
E_Q[Tr]=4e,\qquad E_Q[Tr-r]=3e.
$$

[QSquarefreeArgumentDoubling.lean](QSquarefreeArgumentDoubling.lean) retains the complete orthogonal remainder:

$$
\|Tr-r\|^2=9e^2+\|Tr-r-3e\,1\|^2.
$$

The actual finite-stage physical defects converge in Q norm to Tr−r. They
converge to zero iff r=0. If r≠0 then at least one doubling edge satisfies
r(n)<r(2n). No estimate in this development proves the defects tend to zero.

## An invariance route is ruled out

[QArgumentDoublingObstruction.lean](QArgumentDoublingObstruction.lean) proves the four-coordinate identity

$$
(Tg_3)(4)-(Tg_3)(3)-(Tg_3)(2)+(Tg_3)(1)=1.
$$

Every vector in V satisfies zero here, and so does every vector in the closure
of V plus the constants. Consequently T g₃ is outside both spaces. If w₂ is
the repository's Riesz vector for that functional, then for every F in that
enlarged closure,

$$
\|Tg_3-F\|^2=\frac1{30\zeta(2)}+
 \left\|Tg_3-F-\frac{w_2}{30\zeta(2)}\right\|^2.
$$

Whole-space invariance TV⊆V and commutation TP_V=P_VT are therefore false.
This obstruction also survives adding the constant, so it is not an
obstruction to r=0 or to RH. It applies to the squarefree closure; it does
not refute the older conditional full-conductor doubling program.

## What DPP does and does not supply

For any projected subspace S containing g₂, set p=K_S(1,1). The repository's
normalized divisor mode is e₂=(3·1−8g₂)/sqrt(3), so T e₂=sqrt(3)·1.
[QArgumentDoublingDPP.lean](QArgumentDoublingDPP.lean) proves

$$
\|P_STe_2\|^2=3p=K_S(2,2)+2\ge9/4.
$$

Thus physically doubling the feature family does not preserve the DPP Gram
kernel. Its raw transformed parity diagonal exceeds one and cannot be an
occupation probability. DPP site labels here are divisor modes; sending a
label d to 2d is a different operation from physically sampling f(2n).
Physical doubling destroys orthonormality; this is
not a theorem excluding every possible DPP-based doubling argument.

For DPP terminology and the positive-contraction condition, see Russell
Lyons, *Determinantal probability measures* (2003),
https://arxiv.org/abs/math/0204325, and *Determinantal Probability: Basic
Properties and Conjectures*, §2.3,
https://rdlyons.pages.iu.edu/pdf/icm.pdf. The new calculation is independently
derived from the repository's normalized parity formula.

## What the change of measure supplies

Write Bf(n)=f(n)/(n+1). The densities satisfy
Q(n)/P(n)=(n+1)/(zeta(2)n). The weighted-adjoint formulas are

$$
A_Qf(k)=4\,1_{2\mid k}f(k/2),\qquad
A_Pf(k)=1_{2\mid k}\left(4-\frac2{k/2+1}\right)f(k/2).
$$

[QDoublingMeasureChange.lean](QDoublingMeasureChange.lean) proves pointwise detailed balance, the exact
formula A_P=A_Q(I−B/2), and encodes their difference Df in the actual Q
Hilbert space. Its complete energy and actual doubling action satisfy

$$
\|Df\|_Q^2=\|Bf\|_Q^2,\qquad TDf=2Bf,\qquad
\|Df\|_Q\le\tfrac12\|f\|_Q.
$$

Also |Df(k)|≤2 sqrt(zeta(2))‖f‖ for all k. The squarefree application gives

$$
b=P_VBr=\tfrac12 P_VTDr.
$$

The formula-level adjoints and their complete discrepancy energy are formalized;
the abstract Hilbert-adjoint pairing theorem for A_Q and A_P is not claimed here.
Projection remains essential. Boundedness of Dr and TDr does not establish
boundedness of P_VTDr; the existing correction regularity criterion therefore
remains open.

The final variational sign check uses the already established
`QSquarefreeSmoothedProjection.screened_mean_eq_energy`. Writing
a=⟨r,Br⟩, the new identity TD=2B gives

$$
TDr-2b=2(I-P_V)Br,\qquad E_Q[TDr-2b]=2a.
$$

Here a>0 if r≠0 by strict positivity of B. For any real t, orthogonality
also gives ‖r−t b‖²=e+t²‖b‖². Thus this legal trial has no negative cross
term with which to force e=0. These are consequences of the existing
screened-mean and projection identities, not a new sign assumption.

## Exact remaining RH obligation

The checked conditional consumer is
`QSquarefreeArgumentDoubling.riemannHypothesis_of_limiting_mean_nonincrease`:

$$
E_Q[r(2X)]\le E_Q[r(X)]\quad\Longrightarrow\quad r=0
\quad\Longrightarrow\quad\mathrm{RiemannHypothesis}.
$$

**Open:** prove this inequality for the actual limiting residual, or supply
an estimate forcing the actual stage doubling defects to vanish. The exact
drift identity proves that this inequality is equivalent to r=0; it does not
provide an independent proof of it. Whole-space invariance and naive DPP Gram
invariance cannot serve as providers, because the counterexamples above are
unconditional. No RH-to-squarefree-density converse is asserted.

Wolfram independently confirmed the finite four-coordinate value 1, the
Q/P density ratio, the Pareto doubling multiplier 4−2/(n+1), and the DPP
parity gap 2. These checks are exploratory corroboration, not proof premises.

## Server verification before final checkpoint

The five saved Lean modules were imported together in job
job_SfzMfYOz3IddArY2Y6C7V7XAnSFJ8k88, which succeeded with verified: true and exit code 0.
Seven named theorem axiom audits returned exactly propext, Classical.choice,
and Quot.sound. The exact RH consumer type retains the displayed mean
nonincrease hypothesis. No sorry, admit, local axiom, or unsafe declaration
was added.

Timing measurements are distinct: workspace resume request 79.693 s;
successful server verification including its import build 106.348 s;
queue delay 0.001 s; terminal-result observation through
polling 11.355 s after server completion.
These are not measurements of pure kernel time.
The final aggregate checkpoint and published commit are reported separately
in the accompanying conversation.
