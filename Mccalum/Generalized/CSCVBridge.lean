import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Several-complex-variables bridge — Step 4 build (WIP)

This file builds the missing several-complex-variables infrastructure needed to discharge `osgood`
(equivalently, the bridge `jointly ℂ-differentiable ⇒ analytic` on `ℂⁿ`). Per `CBridge.lean`, the
polydisc–Cauchy route is proved through the iterated/torus Cauchy representation (`bridge_torus_repr`);
what remains ("Step 4") is to **expand the Cauchy kernel into a several-variable power series** and
package it as a `HasFPowerSeriesOnBall` on `ℂ²` (then `ℂⁿ`).

Foundation stone: the **Cauchy-kernel geometric expansion** `(ζ − z)⁻¹ = ∑_j (z−z₀)^j/(ζ−z₀)^{j+1}`
for `‖z − z₀‖ < ‖ζ − z₀‖`. This is the 1-variable analytic engine; the several-variable kernel is its
(two-fold) product, integrated term-by-term over the torus.
-/

noncomputable section

open Complex

/-- **Cauchy-kernel geometric expansion.** For `‖z − z₀‖ < ‖ζ − z₀‖`,
`∑_j (z−z₀)^j / (ζ−z₀)^{j+1} = (ζ − z)⁻¹` (a `HasSum`). The summand is the `z`-power-series coefficient
of the Cauchy kernel; this is the engine that turns the Cauchy integral into a power series. -/
theorem hasSum_cauchy_kernel {z₀ z ζ : ℂ} (h : ‖z - z₀‖ < ‖ζ - z₀‖) :
    HasSum (fun j : ℕ => (z - z₀) ^ j / (ζ - z₀) ^ (j + 1)) ((ζ - z)⁻¹) := by
  have hζ0 : ζ - z₀ ≠ 0 := fun h0 => absurd h (by rw [h0, norm_zero]; exact not_lt.mpr (norm_nonneg _))
  have hζ0pos : 0 < ‖ζ - z₀‖ := norm_pos_iff.mpr hζ0
  have hζz : ζ - z ≠ 0 := fun h0 => by rw [sub_eq_zero] at h0; rw [h0] at h; exact lt_irrefl _ h
  have hq : ‖(z - z₀) / (ζ - z₀)‖ < 1 := by rw [norm_div]; exact (div_lt_one hζ0pos).mpr h
  have hmul := (hasSum_geometric_of_norm_lt_one hq).mul_right (ζ - z₀)⁻¹
  have hf : (fun j : ℕ => (z - z₀) ^ j / (ζ - z₀) ^ (j + 1))
      = fun j : ℕ => ((z - z₀) / (ζ - z₀)) ^ j * (ζ - z₀)⁻¹ := by
    funext j; rw [div_pow, pow_succ, div_mul_eq_div_div, div_eq_mul_inv]
  have hs : (ζ - z)⁻¹ = (1 - (z - z₀) / (ζ - z₀))⁻¹ * (ζ - z₀)⁻¹ := by
    have h1q : 1 - (z - z₀) / (ζ - z₀) = (ζ - z) / (ζ - z₀) := by field_simp; ring
    rw [h1q, inv_div]; field_simp
  rw [hf, hs]; exact hmul

end
