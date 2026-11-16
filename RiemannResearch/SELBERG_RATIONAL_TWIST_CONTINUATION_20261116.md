# Selberg rational twists — verified continuation
Prepared 16 November 2026, America/New_York.

## Result and scope

Priority 1 of the 15 November Gaussian-ray/Estermann continuation is closed by
the declarations in this checkpoint. The exact actual moment is
\[
 M_{\sigma,y,\varepsilon,l,\Delta,u}
 = \sum_{h,k=1}^{\lfloor y^{1+\varepsilon}\rfloor}
   \frac{a_h a_k h^{1-2l}}{k}
   \bigl(\mathcal I_{+}(H,K)+\mathcal I_{-}(H,K)\bigr)
 -\frac{2\sqrt\pi}{\Delta}R_1,
 \qquad H=h/\gcd(h,k),\quad K=k/\gcd(h,k).
\]
Here both rays point outward, the first Estermann exponent is \(2l-1\),
the second is zero, the residue classes are \(+H\) and \(-H\), and the
displacements are \(\tau(H/K)(re^{i\tau\theta}-1)\).
Here a_h is mollifierCoefficient σ y h and R1 is
mollifiedGaussianPoleCoeff σ y ε l Δ u. The original finite mollifier
coefficients and signed Gaussian residue are retained exactly.

The actual-moment theorem assumes \(y>0\), \(0<l<1\), \(\Delta>0\), and
\(0<\theta<\pi\); \(\sigma,\varepsilon,u\) are arbitrary real numbers.
Its only hypotheses are these explicit parameter conditions. No
unproved analytic convergence, tail, density, or moment provider occurs.

## New declarations

All names below are in RiemannResearch.Analysis.ConreyBaluyot.

| Module | Declaration | Exact content |
|---|---|---|
| Analysis/ConreyBaluyotRationalTwist.lean | reducedRationalTwist_pos_coprime | Positivity and coprimality of the reduced numerator and denominator |
| same | reducedRationalTwist_ratio | Cast ratio identity over any characteristic-zero field, including zero natural indices |
| same | rationalTwist_coefficient | Positive-real-base cancellation for arbitrary complex exponent and coefficient |
| same | stdAddChar_rationalTwist | Exact standard additive character for any signed integer numerator |
| same | estermannDampedTerm_displacement | Exact exponential phase/displacement identity for arbitrary complex z and exponents |
| same | estermannDampedSeries_rational_congr | Independence of the chosen rational presentation, without a convergence assumption |
| Analysis/ConreyBaluyotGaussianEstermann.lean | weighted_gaussianArithmeticRayValue_eq_estermann | Exact term identity, with either zero index handled explicitly |
| same | tsum_weighted_gaussianArithmeticRayValue_eq_reduced | Fixed h,k identity with the reduced modulus and both signed rays |
| same | finite_gaussianRay_sum_eq_estermann | Arbitrary complex coefficient arrays on arbitrary positive finite supports |
| same | mollifiedGaussianMoment_eq_estermann | Actual mollified moment with the original signed residue |
| same | gaussianEstermannRay_angle_independent | Each individual signed Estermann ray is angle-independent on (0,pi) |
| same | mollifiedGaussianEstermannValue_angle_independent | The complete finite expression is angle-independent for arbitrary real l |
| same | tendsto_mollifiedGaussianEstermannValue_zero | Exact limit of the integrated damped expression as theta decreases to zero |

## Strengthenings

The coefficient theorem proves, for arbitrary \(A,s\in\mathbb C\) and
positive real \(m,n,h,k\),
\[
 \left(\frac{A n^{s-1}}{k^s}\right)
 \left(\frac{mnh}{k}\right)^{1-s}
 = \frac{A h^{1-s}}{k}m^{-(s-1)}.
\]
All powers are the actual principal complex powers. Specializing
\(s=2l\) gives the coefficient identity used in the moment assembly.

The finite assembly needs no factorization of the coefficient array,
no reality condition on its coefficients, and no restriction \(0<l<1\).
Only its specialization to the actual moment inherits that strip from
the already-proved moment theorem.

The exact signed character identities use arbitrary integer numerators.
The ray phase identity even allows any integer multiplier before the
analytic convergence theorem restricts the multiplier to the two signs.

Each individual Estermann ray, not only their pair or their completed
finite sum, is angle-independent throughout \(0<\theta<\pi\).

The actual finite expression also has the exact one-sided boundary limit
\[
 \lim_{\theta\downarrow0}\mathrm{EstermannValue}(\theta)
 =M_{\sigma,y,\varepsilon,l,\Delta,u}
   +\frac{2\sqrt\pi}{\Delta}R_1.
\]
The limit is taken after evaluating the convergent integrals for positive
angles. It does not claim a termwise exchange at angle zero.

These are fixed-parameter identities. They provide no uniform estimate
as height, width, mollifier length and line vary together. Positive
damping remains necessary for the sum/integral exchange. Do not set
theta=0 inside the damped-series Fubini theorem.

## Next research obligation: global Estermann Mellin contour shift

Do not repeat the initial Mellin transform. It is already provided by
Analysis/ConreyBaluyotEstermannMellin.lean:
- integrable_estermannMellinKernel_vertical;
- norm_estermannMellinKernel_vertical_le;
- estermannDampedSeries_eq_mellinIntegral.

The initial line must satisfy \(c>0\),
\(c+\operatorname{Re}\alpha>1\), and
\(c+\operatorname{Re}\beta>1\).
For the actual application \(\alpha=2l-1,\ \beta=0\), this requires
\(c>\max(1,2-2l)\).

Analysis/ConreyBaluyotEstermannMellinResidues.lean already proves the
local simple residues at \(0,1-\alpha,1-\beta\), including the Gamma
and damping factors, and exposes the rectangle-residue API.
The shifted residues require a unit residue class, distinct shifts,
and the indicated Gamma-regularity range. Gcd reduction now supplies
the coprimality needed to construct the unit in the actual application.

The missing global proof must:
1. Establish the kernel's holomorphy away from the listed poles on the
   complete contour rectangle, and identify every crossed pole.
2. Prove vertical convergence on the new line.
3. Prove both remote-side limits, with enough control to pass to the
   improper integrals. A right-line majorant alone does not do this.
4. Handle coincident poles separately. In the actual application,
   \(l=1/2\) makes \(\alpha=\beta=0\), so the two shifted poles coincide
   at \(s=1\); the distinct-shift simple-residue theorems do not apply.
5. Preserve the exact residue signs and the \(1/(2\pi)\) normalization
   in the real-parameterized vertical integral.

Only after this shift is proved should the actual finite expression be
identified with all of \(M_1+M_2+D_1+D_2+E\), retaining the original
Gaussian pole correction rather than absorbing it without a bound.

## Remaining agenda

| Order | Obligation | Status |
|---|---|---|
| 1 | Exact rational-twist assembly, both signs, reduced modulus, zero indices, original residue | Closed by this checkpoint |
| 2 | Global Estermann Mellin contour shift, both remote sides and coincident poles | Open |
| 3 | Exact complete signed \(M_1+M_2+D_1+D_2+E\) decomposition | Open after 2 |
| 4 | Complete and multilinear Kloosterman estimates with full hypotheses | Open |
| 5 | Cofinal UniformGaussianMollifiedMoment with one eta,C,H and all padded centers | Open |
| Independent | ActualZeroOrdinate.InghamDensityBound | Classical theorem; complete formal provider still open |
| 6 | Existing cofinal density assembly | Apply only after both actual providers exist |

Ingham I2 is closed by ActualInghamMollifierMoment.lean. The independent
Ingham density theorem must not assume the desired Selberg conclusion.
Checked parameter budgets are not analytic providers. No RH proof or
new unconditional uniform moment bound is asserted.

## Provenance and verification

Primary source for the arithmetic strategy:
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.7 and Section 3.3, printed pp. 104-105 and 116-117.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

Wolfram independently simplified the coefficient and phase identities
to True. This is a computational cross-check, not Lean verification.
The generalized formulations are formal strengthenings; no mathematical
novelty claim is made.

The checked starting main was 1e52ba957c483c21c17955ed01becf53de0da89a.
Its full checkpoint is job_facdeV6M0ADlNv591rnn_pjKV31vUTDQ.
This is the joint-convergence checkpoint following
82f398c798c4183b28dd2eb3f793584c983a8531 (actual Euler/ray/moment bridge)
and d04324c890889106d080f059b3b302ebe1adbe03 (ray rotation).

The eight guarded axiom checks passed as
job_wFKja5wQFIEJI6CW1gOd6IMvwtJMCyK2, using only propext,
Classical.choice and Quot.sound (the elementary gcd result needs only
propext and Quot.sound).
BuildBuddy: https://app.buildbuddy.io/invocation/859e3b75-1d04-4664-8fdf-1b17edbb382b

Publication of this continuation requires the full Bazel
//:RiemannResearch target with --config=buildbuddy. The checkpoint's
terminal job record identifies the exact verified and pushed commit.
Focused checks and axiom audits do not replace the full checkpoint.

Retained workspace: ws_O5g_HcTqMq11Vgoxn1u4_9Rz7BHKrorF.
