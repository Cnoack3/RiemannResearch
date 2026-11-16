# Signed leakage: finite rational certificates and a 0.19 bound

16 November 2026. Source: Christian Noack's RH Obligation Triage continuation.

**Status: the all-positive-slope estimate remains Open.** This continuation proves an exact finite rational certificate reduction and improves the unconditional slope from 1/2 to 19/100, including the eventual endpoint.

## The finite rational budget

For m natural, rational c : Fin m -> Q, and K > 0, set

```text
f_c = sum_{i<m} c_i g_{i+2}
e_c(n) = 1 - sum_{i<m} c_i ((n mod (i+2))/(i+2))
A_c = 1 + sum_{i<m} |c_i|
C(m,K,c) = sum_{n=1}^K e_c(n)^2/n^2 + A_c^2/K.
```

Every term of C is finite rational arithmetic. All signed contributions remain inside the squared error. The entire omitted tail is bounded by A_c^2/K. The complete Q norm satisfies ||1-f_c||_Q^2 <= C. For fixed real coefficients, C tends to zeta(2) ||1-f_c||_Q^2 as K tends to infinity. A moving coefficient family still needs its own tail control.

## Exact equivalence, with no target premise

The following are equivalent in Lean:

1. For every epsilon > 0 and J, some N >= J has ||S_N|| <= epsilon H_N.
2. For every epsilon > 0 and J, there are m >= J, K > 0, rational c, with C(m,K,c) < epsilon^2.
3. For every natural j, there are m >= j, K > 0, rational c, with C(m,K,c) < 1/(j+1)^2.

The certificate conditions contain no target-membership, zero-residual, or RH assumption. Their universal existence assertion remains **Open**. The reverse direction from (1) uses its already proved closure consequence, convergence of the actual finite Gram candidates, the exact fixed-vector budget limit, and density of rational coefficient vectors. It does not provide unconditional witnesses for (2) or (3).

One certificate C <= delta^2 gives ||S_N|| <= delta H_N + M at every N. Taking delta = epsilon/2 and H_N >= 2M/epsilon gives the requested slope. Harmonic divergence supplies cofinally late stages after the certificate is supplied.

## Unconditional seven-atom improvement

The repository's checked seven-atom competitor uses conductors 2, 3, 5, 6, 10, 15, 30 and respective coefficients

```text
(985587, 963419, 823721, -158232, 91952, 138611, 146439)/1000000.
```

QSquarefreeRationalUpperBounds.complete_norm_lt supplies complete squared Q-error strictly below 361/10000. The new transfer proves ||S_N|| <= (19/100) H_N + M for every N, and the requested estimate eventually for every epsilon >= 19/100. The endpoint uses the strict error margin. The number 19/100 is not asserted optimal. A fixed certificate does not prove all positive slopes. The full criterion allows nonsquarefree conductors; squarefree-only density is not inferred from this benchmark.

## Declarations and verification

Module: RiemannResearch/RH/QLeakageFiniteCertificates.lean.
Namespace: RiemannResearch.RH.QLeakageFiniteCertificates.

- `synthesis_mem_closure`
- `errorVector_sequence`
- `errorVector_sequence_succ`
- `amplitude_nonneg`
- `physicalError_abs_le`
- `errorVector_abs_le`
- `budget_nonneg`
- `error_norm_sq_le_budget`
- `rationalBudget_cast`
- `budget_continuous`
- `error_energy_series`
- `error_energy_tsum`
- `budget_tendsto`
- `exists_rational_budget_lt_of_mem`
- `partialLeakage_le_of_budget`
- `cofinal_subharmonic_iff_rational_certificates`
- `cofinal_subharmonic_iff_countable_rational_certificates`
- `riemannHypothesis_of_countable_rational_certificates`
- `eventually_partialLeakage_le_of_legal_certificate`
- `sevenAtom_mem_closure`
- `sevenAtom_error_lt`
- `partialLeakage_norm_le_nineteen_hundredths`
- `eventually_partialLeakage_norm_le_of_nineteen_hundredths_le`

All 23 declarations carry guarded transitive-axiom checks accepting exactly propext, Classical.choice, Quot.sound. The triage Site records the terminal saved-file audit and integrated full-project checkpoint separately.

Next obligation: construct witnesses at every natural precision j with the full rational tail budgets verified. A finite list of checked precision levels establishes only those levels.
