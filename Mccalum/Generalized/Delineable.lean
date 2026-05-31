import Mccalum.Generalized.MultiCluster

/-!
# Analytic pseudopolynomial delineability — proved from `{C, E, A2}`

`analytic_pseudopoly_delineable'` is the delineation result, now a **theorem** (no longer the
`analytic_pseudopoly_delineable_nonsep` axiom): the separable case via the analytic IFT
(`separable_family_locally_delineable`), the non-separable case via `multi_cluster_real_delineation`
(Weierstrass + Zariski + A2). This is the file that collapses the main theorem's dependency to
`{C, E, A2}`; it lives above the whole stack so it can use `multi_cluster_real_delineation`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Local delineability of a real-analytic pseudopolynomial family**, proved from `{C, E, A2}`. -/
theorem analytic_pseudopoly_delineable'
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg_bound : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff_an : ∀ i : ℕ, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (hg_pos : 0 < (g 0).natDegree)
    (hg_deg : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    (hP_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0) :
    ∃ (V : Set (Fin s → ℝ)), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧
      ∃ (k : ℕ) (η : Fin k → (Fin s → ℝ) → ℝ) (mult : Fin k → ℕ),
        (∀ i, AnalyticOn ℝ (η i) V) ∧
        (∀ y ∈ V, ∀ i j : Fin k, i < j → η i y < η j y) ∧
        (∀ y ∈ V, ∀ α : ℝ, (g (y, 0)).IsRoot α ↔ ∃ i : Fin k, α = η i y) ∧
        (∀ i, 0 < mult i) ∧
        (∀ y ∈ V, ∀ i, (g (y, 0)).rootMultiplicity (η i y) = mult i) := by
  by_cases hsep : (g 0).Separable
  · have hcoeff' : ∀ i, AnalyticAt ℝ (fun y => (g (y, 0)).coeff i) 0 := fun i =>
      (hg_coeff_an i).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    exact separable_family_locally_delineable (fun y => g (y, 0)) 0 hg_deg hg_pos hcoeff' hsep
  · exact multi_cluster_real_delineation Ng g hg_deg_bound hg_coeff_an hg_pos P hP_an hP_ne
      NA NB A B hA_deg hB_deg hA_coeff hB_coeff hmem hP_oi hg_deg

end
