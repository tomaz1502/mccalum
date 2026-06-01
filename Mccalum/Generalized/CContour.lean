import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Brick: contour setup for the Weierstrass-division Cauchy proof

`exists_contour_ne_zero`: if `G(z₀, ·)` is analytic at `t = 0` with **finite** order `m > 0` (so `0`
is an isolated zero), and `G` is jointly continuous, then there is a radius `ε > 0` with
`G(z₀, t) ≠ 0` on the circle `|t| = ε`, and moreover `G(z, t) ≠ 0` on that circle for all `z` near
`z₀` (tube lemma). This is exactly the contour on which the Cauchy quotient
`q = (2πi)⁻¹∮ F/(G·(ζ−t))` is defined. Completable with Mathlib's isolated-zeros theorem + the
generalized tube lemma — no SCV analyticity needed.
-/

noncomputable section

open Complex Metric Filter Topology Set

/-- **Contour setup.** -/
theorem exists_contour_ne_zero {E : Type*} [TopologicalSpace E]
    {G : E × ℂ → ℂ} {z₀ : E} {m : ℕ} (hm : 0 < m) (hG : Continuous G)
    (hGt : AnalyticAt ℂ (fun t => G (z₀, t)) 0)
    (hord : analyticOrderAt (fun t => G (z₀, t)) 0 = (m : ℕ∞)) :
    ∃ ε > 0, (∀ t ∈ sphere (0 : ℂ) ε, G (z₀, t) ≠ 0) ∧
      ∀ᶠ z in 𝓝 z₀, ∀ t ∈ sphere (0 : ℂ) ε, G (z, t) ≠ 0 := by
  -- 0 is an isolated zero of `G(z₀, ·)` (finite order ⇒ not eventually zero)
  have hnotzero : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), G (z₀, t) = 0) := by
    rw [← analyticOrderAt_eq_top]; rw [hord]; exact_mod_cast ENat.coe_ne_top m
  have hpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), G (z₀, t) ≠ 0 :=
    hGt.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotzero
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hpunct
  obtain ⟨ε₀, hε₀, hball⟩ := hpunct
  refine ⟨ε₀ / 2, by positivity, ?_, ?_⟩
  · -- on the circle |t| = ε₀/2
    intro t ht
    have ht_norm : ‖t‖ = ε₀ / 2 := mem_sphere_zero_iff_norm.mp ht
    have ht_ne : t ≠ 0 := by
      intro h; rw [h, norm_zero] at ht_norm; linarith
    exact hball (by rw [dist_zero_right, ht_norm]; linarith) ht_ne
  · -- tube lemma: `G ≠ 0` on `(nbhd of z₀) × (sphere ε₀/2)`
    have hopen : IsOpen {p : E × ℂ | G p ≠ 0} := isOpen_compl_singleton.preimage hG
    have hsub : ({z₀} : Set E) ×ˢ sphere (0 : ℂ) (ε₀ / 2) ⊆ {p : E × ℂ | G p ≠ 0} := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      rw [mem_singleton_iff] at hz; subst hz
      have ht_norm : ‖t‖ = ε₀ / 2 := mem_sphere_zero_iff_norm.mp ht
      have ht_ne : t ≠ 0 := by intro h; rw [h, norm_zero] at ht_norm; linarith
      exact hball (by rw [dist_zero_right, ht_norm]; linarith) ht_ne
    obtain ⟨u, v, hu, _, hz₀u, hsphv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton (isCompact_sphere (0 : ℂ) (ε₀ / 2)) hopen hsub
    filter_upwards [hu.mem_nhds (hz₀u rfl)] with z hz t ht
    exact huv ⟨hz, hsphv ht⟩
