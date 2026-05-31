import Mccalum.Generalized.ClusterFromReal
import Mccalum.Generalized.A2Axiom

/-!
# F3 — single-cluster real delineation (the `{C, E, A2}` milestone)

`single_cluster_real_delineation` wires the full per-cluster chain on `{C, E, A2}`: it runs
`cluster_from_real` (Weierstrass + Zariski) to get the complex sections and the A2-ready real-slice
`hcover` / `hmult_match`, then applies the A2 axiom `real_delineation_of_complex_sections` to obtain
the **real** root delineation of the section family `g(·,0)` near `0`.

The remaining work for the full theorem is the multi-cluster assembly (enumerate `g(0,0)`'s real
roots, translate each to `0`, apply this, and glue).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- **Single cluster, real (on `{C, E, A2}`).** From the real product family `g` localized at a
multiplicity-`m` cluster root of `g(0,0)` at `t = 0` (with witness `P`, cofactors `A,B`, and section
degree constancy), the real roots of the section family `g(·,0)` near `0` form finitely many ordered
real-analytic functions with constant multiplicities. -/
theorem single_cluster_real_delineation (m : ℕ) (hm_pos : 0 < m)
    (Ng : ℕ) (g : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ) (hg_deg : ∀ w, (g w).natDegree ≤ Ng)
    (hg_coeff : ∀ i, AnalyticAt ℝ (fun w => (g w).coeff i) 0)
    (P : (Fin s → ℝ) × (Fin e → ℝ) → ℝ) (hP_an : AnalyticAt ℝ P 0) (hP_ne : order ℝ P 0 ≠ ⊤)
    (NA NB : ℕ) (A B : (Fin s → ℝ) × (Fin e → ℝ) → Polynomial ℝ)
    (hA_deg : ∀ w, (A w).natDegree ≤ NA) (hB_deg : ∀ w, (B w).natDegree ≤ NB)
    (hA_coeff : ∀ i, AnalyticAt ℝ (fun w => (A w).coeff i) 0)
    (hB_coeff : ∀ i, AnalyticAt ℝ (fun w => (B w).coeff i) 0)
    (hmem : ∀ᶠ w in 𝓝 (0 : (Fin s → ℝ) × (Fin e → ℝ)),
      Polynomial.C (P w) = A w * g w + B w * derivative (g w))
    (hP_oi_real : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), order ℝ P (y, 0) = order ℝ P 0)
    (hm_root : (g 0).rootMultiplicity 0 = m)
    (hg_deg_const : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), (g (y, 0)).natDegree = (g 0).natDegree) :
    ∃ (V : Set (Fin s → ℝ)) (δ : ℝ), IsOpen V ∧ (0 : Fin s → ℝ) ∈ V ∧ 0 < δ ∧
      ∃ (k : ℕ) (η : Fin k → (Fin s → ℝ) → ℝ) (rmult : Fin k → ℕ),
        (∀ i, AnalyticOn ℝ (η i) V) ∧
        (∀ y ∈ V, ∀ i, |η i y| < δ) ∧
        (∀ y ∈ V, ∀ i j : Fin k, i < j → η i y < η j y) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α| < δ ∧ (g (y, 0)).IsRoot α) ↔ ∃ i : Fin k, α = η i y) ∧
        (∀ i, 0 < rmult i) ∧
        (∀ y ∈ V, ∀ i, (g (y, 0)).rootMultiplicity (η i y) = rmult i) := by
  obtain ⟨a, r, ψ, mult, ha_an, ha0, hψ_an, hψ0, hmult_pos, hsum, hdistinct, hroots, hmults,
      hmult_match, δ₀, hδ₀, hcover⟩ :=
    cluster_from_real m hm_pos Ng g hg_deg hg_coeff P hP_an hP_ne NA NB A B hA_deg hB_deg
      hA_coeff hB_coeff hmem hP_oi_real hm_root hg_deg_const
  -- the section coefficient family is real-analytic
  have hcoeff_sec : ∀ i, AnalyticAt ℝ (fun y : Fin s → ℝ => (g (y, 0)).coeff i) 0 := fun i =>
    (hg_coeff i).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  -- apply A2
  exact real_delineation_of_complex_sections (fun y => g (y, 0)) hcoeff_sec hg_deg_const m hm_pos
    hm_root r ψ mult hψ_an hψ0 hmult_pos hsum hdistinct δ₀ hδ₀ hcover hmult_match

end
