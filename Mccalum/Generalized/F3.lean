import Mccalum.Generalized.ClusterFromReal
import Mccalum.Generalized.A2Recovery

/-!
# F3 — single-cluster real delineation (the `{C, E}` milestone)

`single_cluster_real_delineation` wires the full per-cluster chain on `{C, E}`: it runs
`cluster_from_real` (Weierstrass + Zariski 4.1.1), which produces the **single** holomorphic branch
`ξ` of the cluster (the unique root, nonsplitting) together with the real-slice covering and
multiplicity, and then finishes with the **proved** recovery core
`real_delineation_of_single_branch` (`A2Recovery.lean`, 0 custom axioms) to obtain the **real** root
delineation of the section family `g(·,0)` near `0`. No separate real-analysis axiom is needed: the
no-splitting is part of Zariski's Theorem 4.1.1, and the real recovery is proved.

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
      ∃ (η : (Fin s → ℝ) → ℝ),
        AnalyticOn ℝ η V ∧ η 0 = 0 ∧
        (∀ y ∈ V, |η y| < δ) ∧
        (∀ y ∈ V, ∀ α : ℝ, (|α| < δ ∧ (g (y, 0)).IsRoot α) ↔ α = η y) ∧
        (∀ y ∈ V, (g (y, 0)).rootMultiplicity (η y) = m) := by
  -- `cluster_from_real` (C + Zariski 4.1.1) gives the single holomorphic branch `ξ` of the cluster,
  -- real-valued on the slice; the proved recovery core turns it into the real-analytic delineation.
  obtain ⟨ξ, δ₀, hξ_an, hξ0, hδ₀, hξ_cover, hξ_mult⟩ :=
    cluster_from_real m hm_pos Ng g hg_deg hg_coeff P hP_an hP_ne NA NB A B hA_deg hB_deg
      hA_coeff hB_coeff hmem hP_oi_real hm_root hg_deg_const
  exact real_delineation_of_single_branch (fun y => g (y, 0)) m ξ hξ_an hξ0 δ₀ hδ₀
    hξ_cover hξ_mult

end
