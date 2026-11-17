# Highest-viability CRT paper: source and agenda

Source: [highest viability RH.pdf](https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view), 33 pages.

Internal title: *An audited proof attempt at the RH-level CRT estimate: Exact-head extension, the spectral-correction infimum, and the surviving uniformity obstruction*. Printed date: 23 July 2026. Imported for formalization 16 November 2026.

The PDF is source material, not a Lean verification certificate. The variance target and RH remain open.

| ID | Source target | Current status |
|---|---|---|
| G1 | Uniform diagonal pair-kernel ridge energy and residual | Open; new approximate-source Lean bounds and finite witnesses |
| G2 | Exact finite-cutoff target RKHS membership | Exact finite-cutoff membership refuted in Lean |
| G3 | Signed resonance contraction, equations (72)–(73) | Open |
| G4 | Continuous-block certification between nodes | External Arb certificates at x=53,97,199 through t=16 |
| G5 | Compatible corrections over all Mellin blocks | Common correction on [0,16] certified; tail and uniformity open |

The continuation proves trust-region comparisons, a signed approximate-source identity, quantitative residual bounds, and the impossibility of exact interval cancellation of H + zeta(1-z) F(z). See [the theorem catalog](THEOREM_CATALOG_SPECTRAL_CORRECTION_20261116.md) for exact hypotheses, proof status, external certificates, and the revised agenda.

The extracted source is retained at ResearchData/HighestViability20261116/source_extracted.md. Mathematical layout may be damaged; consult the original PDF.
