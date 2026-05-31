import Mccalum.Generalized.Lifting

/-!
# A2 — real root recovery from complex cluster sections (AXIOM)

The single remaining classical real-analysis ingredient, parallel to C (Weierstrass) and E (Zariski).
Weierstrass + Zariski (via `cluster_from_real`) supply the **complex** holomorphic root sections
`ψ_i` of a cluster; A2 is the **real-branch** content that turns them into the real root functions of
the conclusion — the real analog of Zariski's equisingularity / a Schwarz-reflection-at-scale fact.

`real_delineation_of_complex_sections`: given a real-analytic family `fam` whose section polynomial
`fam 0` has a root of multiplicity `m` at `t = 0`, and holomorphic cluster sections `ψ_i`
(analytic, `ψ_i 0 = 0`, distinct, multiplicities summing to `m`) that parametrize — within a cluster
radius `δ₀` — the complex roots near `0` of the complexified family `(fam y).map (ℝ→ℂ)` for real `y`
near `0`, the **real** roots of `fam y` near `0` are finitely many ordered real-analytic functions
with constant multiplicities. The complex hypotheses are exactly what `cluster_from_real` produces, so
this keeps the final theorem on `{C, E, A2}` with C and E load-bearing.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **A2 (AXIOM).** Real root delineation of one cluster, recovered from its complex sections. -/
axiom real_delineation_of_complex_sections {s : ℕ}
    (fam : (Fin s → ℝ) → Polynomial ℝ)
    (hcoeff : ∀ i, AnalyticAt ℝ (fun y => (fam y).coeff i) 0)
    (hdeg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (fam y).natDegree = (fam 0).natDegree)
    (m : ℕ) (hm_pos : 0 < m) (hm : (fam 0).rootMultiplicity 0 = m)
    -- complex cluster sections (supplied by `cluster_from_real` = Weierstrass + Zariski)
    (r : ℕ) (ψ : Fin r → (Fin s → ℂ) → ℂ) (mult : Fin r → ℕ)
    (hψ_an : ∀ i, AnalyticAt ℂ (ψ i) 0) (hψ0 : ∀ i, ψ i 0 = 0)
    (hmult_pos : ∀ i, 0 < mult i) (hsum : ∑ i : Fin r, mult i = m)
    (hψ_distinct : ∀ i j, i ≠ j → ¬ (ψ i =ᶠ[𝓝 (0 : Fin s → ℂ)] ψ j))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    -- the sections parametrize the complex roots of the complexified family within the cluster
    (hcover : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ α : ℂ, ‖α‖ < δ₀ →
      (((fam y).map (algebraMap ℝ ℂ)).IsRoot α ↔ ∃ i, α = ψ i (realEmbedding s y)))
    (hmult_match : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      Function.Injective (fun i => ψ i (realEmbedding s y)) → ∀ i,
        ((fam y).map (algebraMap ℝ ℂ)).rootMultiplicity (ψ i (realEmbedding s y)) = mult i) :
    ∃ (V : Set (Fin s → ℝ)) (δ : ℝ), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧ 0 < δ ∧
      ∃ (η : (Fin s → ℝ) → ℝ),
        AnalyticOn ℝ η V ∧ η 0 = 0 ∧
        (∀ y ∈ V, |η y| < δ) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α| < δ ∧ (fam y).IsRoot α) ↔ α = η y) ∧
        (∀ y ∈ V, (fam y).rootMultiplicity (η y) = m)

end
