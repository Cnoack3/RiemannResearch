# Q divisor DPP: Lean continuation of the moving-window analysis

Date: 14 October 2026.
Source: the user-provided QDPP_Finite_Rank_and_Moving_Window_Analysis_2026-10-14
and the published research record QDPPMovingWindowsResearch20261014.md.
The source supports the statements and proof strategies, not a novelty claim.

This continuation formalizes 53 new theorems in five modules. It advances the
unconditional arithmetic and probability parts of the report. It does not
formalize all of its global Euler-product, sine-obstruction, or Poisson-limit
arguments, and it proves no new RH theorem.

## Exact identities and checked providers

Physical site n is counting coordinate i = n - 1. The spectral-law variable
r is also zero based: its physical conductor is R = r + 1.

### Actual Parseval tails, auxiliary probability law, and cardinality

RH/QDivisorDPPSpectralTails.lean proves complete summability and the exact
signed kernel-tail identity:

```
(if i = j then 1 else 0) - basisKernel N i j
  = tsum (fun r => psi_(r+N+1)(i+1) * psi_(r+N+1)(j+1)).
```

No signed summand or residual energy is discarded. The new spectralMass is
the square of the actual normalized divisor-wavelet coordinate.
spectralMass_arithmetic identifies it with

    q(n) * A_R(n)^2 / J_2(R).

spectralMass_tsum proves normalization, and spectralLaw is an actual PMF,
constructed from these nonnegative masses. spectralLaw_cdf and
spectralLaw_tail prove

    K_N(n,n) = P(R_n <= N),
    1 - K_N(n,n) = P(R_n > N).

The auxiliary law is not an inter-stage coupling of DPPs. Independence of its
prime exponents is not established by merely defining this PMF.

basisKernel_trace proves the actual infinite diagonal sum is N.
basisLaw_cardinality applies the existing generic rank-plus-trace theorem:
the extended count setCount of the occupied set is N almost surely.
Thus the global fixed-cardinality statement previously left written is checked.

At distinct sites, basisKernel_hole_cauchy proves

    K_N(n,m)^2 <= (1 - K_N(n,n)) * (1 - K_N(m,m)).

### Prime-local mass and overlap providers

RH/QPrimeWaveletOverlap.lean verifies the complete piecewise local wavelet:
it equals its Jordan weight below the valuation, is minus p^(2v) at v+1,
and is zero above v+1. reversePrimeMass is the exact local spectral mass

    ((1 - p^(-2)) / p^(2v)) * geometricWavelet(p,a,v)^2 / J_2(p^a).

reversePrimeMass_below, reversePrimeMass_last, reversePrimeMass_above,
reversePrimeMass_nonneg, reversePrimeMass_sum, and reversePrimeMass_tsum
give its stated local formulas, support, positivity, and normalization.
In particular the mass at a = v+1 is exactly p^(-2).

The full infinite local absolute-overlap sum is identified with its finite
support sum. The two evaluated cases are

    v = w:  p^(2v) * p^2 / (p^2 - 1),
    v < w:  2 * p^(2v).

The reverse case follows from localAbsoluteOverlap_symm.
These are local exponent calculations; they are not a checked passage to an
infinite Euler product over all primes.

### Pointwise arithmetic and rough-sector estimates

RH/QDivisorWaveletBounds.lean proves, for positive conductors and sites,

    |A_R(n)| <= J_2(R) <= R^2,
    A_R(n)^2 / J_2(R) <= R^2.

RH/QDivisorDPPArithmeticBounds.lean first retains the exact arithmetic
diagonal and then proves

    K_N(n,n) <= N(N+1)(2N+1) / (6 zeta(2) n^2).

For the finite divisor signature shared with site 1, it proves the exact law

    K_N(n,n) = K_N(1,1) / n^2 <= 1 / n^2.

prime_same_signature_one and basisKernel_prime_above_le specialize this to
every prime p > N. qDivisorWavelet_one_value identifies A_R(1) with mu(R);
roughConductorMass_eq and roughConductorMass_tendsto consequently prove

    H_N = sum_(1 <= R <= N) mu(R)^2 / J_2(R)
        = zeta(2) K_N(1,1)  --> zeta(2).

This follows from complete-divisor-basis Parseval, not from a legal-residue
inverse-Gram estimate.

### Actual moving-window probability consumers

Probability/DeterminantalWindowBudgets.lean proves finite union bounds for
occupation and gap probabilities, and allows both the location and dimension
of a finite window to vary. A vanishing sum of vacancy probabilities implies
full occupation in probability; a vanishing diagonal sum implies emptiness.

basisKernel_window_sum_le supplies the concrete arithmetic bound

    E C_N <= h_N N(N+1)(2N+1) / (6 zeta(2) x_N^2)

for a window of h_N sites all at least x_N > 0. The exact expectation provider
is the existing basisLaw_moving_expected_count.

basisLaw_far_window_gap_tendsto proves the markdown's coarse regime:

    h_N N^3 / x_N^2 --> 0
      implies P(the moving window is empty) --> 1.

Its only asymptotic assumption is the displayed geometric budget. The
one-site and finite-window kernel estimates themselves are unconditional.

## RH interpretation and outstanding work

The complete divisor basis includes the conductor-one constant mode.
Its full-basis projection converges to the identity unconditionally.
Therefore its occupancy limit, spectral-law normalization, H_N limit, and
fixed particle count do not prove approximation of 1 by legal residue atoms.

The following providers remain open in Lean in this continuation:

1. Identify all finite prime-exponent marginals of the actual spectralLaw,
   prove their independence, and construct the associated squarefree S law.
   The verified local mass formulas are inputs, not substitutes for this step.
2. Supply the global domination R_n divides nS and the vacancy bound
   1 - K_N(n,n) <= 2n/N. The sharper head-filling and square-root-scale
   hole arguments still require this provider.
3. Supply the column-law coupling Y_R <= R T and the entire-tail bound
   N(N+1)/(zeta(2) x). The finite-window cubic budget above does not verify it.
4. Convert the checked local overlap sums into the exact global Hellinger
   Euler product and its uniform gcd bounds. The general unit-lattice
   Bernoulli/sine obstruction remains written analysis.
5. Formalize the continuum Hilbert-Schmidt estimates and the conditional
   Poisson count and hole limits. No required mean limit has been constructed.
6. Construct a legal-residue approximation estimate or an arithmetic
   identification of a self-adjoint spectral determinant with completed zeta.
   DPP structure, even a hypothetical sine limit, does not discharge this.

The most direct continuation of this file is item 4, using the checked
prime-local overlap sums and actual row normalization. For RH, the separate
legal-residue or zeta-identification bridge remains indispensable.

## Verification and continuation

The five exact source modules are exported from RiemannResearch.lean.
Targeted source builds and the 53-theorem axiom audit were submitted in
job_zX7LwpDDPKzHBQ1dSU4ELkkn3l8Dqa5I, which finished with success,
exit code 0, and verified = true (18.051 seconds).
Its bounded output omitted 22 early axiom lines. Supplemental audit
job_PswJuw8N32hUmQbI1s_YMgJ-NVcde599 succeeded, exit code 0,
verified = true (4.839 seconds), and displayed all 22 omitted results.
Together the outputs confirm that all 53 declarations use only propext,
Classical.choice, and Quot.sound. No sorry, admit, custom axiom, or unsafe
declaration is introduced.

Publication is performed only by the final server-gated checkpoint, validating
the aggregate and changed child modules before push. The final checkpoint job,
scope, and published commit are reported with task completion, separately from
the targeted source and axiom checks.

Retained workspace token: ws_RYPNJ97fuzONZG2xjO4GODpE3hz5S0vi.
Server project root:
 /home/cri_2025/lean-agent-workspaces/ws_RYPNJ97fuzONZG2xjO4GODpE3hz5S0vi/RiemannResearch.
Resume that workspace, recover any pending job before submitting another, and
continue to serialize all Lean verification.
