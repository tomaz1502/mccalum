import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# C argument-principle, base case (WIP)

Toward the `z = 0` base case of the argument principle needed for `weierstrass_division`:
for `G(ζ) = ζᵐ·v(ζ)` with `v` analytic and non-vanishing on the closed disc,
`(2πi)⁻¹ ∮_{|ζ|=R} G'(ζ)/G(ζ) dζ = m`. The logarithmic derivative splits as
`G'/G = m/ζ + v'/v`, and `∮ m/ζ = 2πi·m` (residue, **proved below, sorry-free**),
`∮ v'/v = 0` (Cauchy–Goursat, `v ≠ 0` on the disc).

This isolates the genuinely-Mathlib-supported half of the argument-principle gap (the residue), and
documents the remaining obligation (the log-derivative split + Cauchy–Goursat for `v'/v`).
-/

noncomputable section

open Complex Metric Topology
open scoped Real

/-- **Residue at the center (sorry-free).** `∮_{|ζ|=R} a/ζ dζ = 2πi·a`. The literal source of the
`m` in the argument-principle base case (take `a = m`). -/
theorem circleIntegral_const_div_center (R : ℝ) (h0 : 0 < R) (a : ℂ) :
    (∮ z in C(0, R), a / z) = 2 * π * I * a := by
  have h := circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
    (E := ℂ) h0 (c := 0) (f := fun _ => a) (s := ∅) Set.countable_empty
    continuousOn_const (fun z _ => differentiableAt_const a)
  simpa [sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- **`v'/v` integrates to zero (sorry-free given the hypotheses).** Cauchy–Goursat for the
logarithmic derivative of a non-vanishing function on the disc. -/
theorem circleIntegral_logDeriv_eq_zero {R : ℝ} (h0 : 0 ≤ R) {v : ℂ → ℂ}
    (hv : ContinuousOn (fun z => deriv v z / v z) (closedBall 0 R))
    (hd : ∀ z ∈ ball (0 : ℂ) R, DifferentiableAt ℂ (fun z => deriv v z / v z) z) :
    (∮ z in C(0, R), deriv v z / v z) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable h0 Set.countable_empty hv
    (fun z hz => hd z hz.1)

/-- **Argument-principle base case (`z = 0`), sorry-free.** For `G(ζ) = ζᵐ·v(ζ)` with `v` analytic
and non-vanishing on the closed disc, `∮_{|ζ|=R} (logarithmic derivative of G) dζ = 2πi·m`. (The
logarithmic derivative `logDeriv G = deriv G / G` is the integrand `G'/G`.) Together with the
propagation step (full argument principle, the documented gap) this gives the `m` for `weierstrass_division`. -/
theorem circleIntegral_logDeriv_pow_mul {m : ℕ} {R : ℝ} (hR : 0 < R) (v : ℂ → ℂ)
    (hv : ∀ z ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ v z)
    (hv0 : ∀ z ∈ closedBall (0 : ℂ) R, v z ≠ 0) :
    (∮ z in C(0, R), logDeriv (fun w => w ^ m * v w) z) = 2 * π * I * (m : ℂ) := by
  -- `logDeriv v = deriv v / v` is analytic on the closed disc
  have hlog_an : ∀ z ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ (fun w => deriv v w / v w) z :=
    fun z hz => ((hv z hz).deriv).div (hv z hz) (hv0 z hz)
  have hz0_of_sphere : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz; exact (ne_of_lt hR) hz
  -- split `logDeriv G = m/ζ + deriv v/v` on the sphere
  have hsplit : Set.EqOn (logDeriv (fun w => w ^ m * v w))
      (fun z => (m : ℂ) / z + deriv v z / v z) (sphere (0 : ℂ) R) := by
    intro z hz
    have hzball : z ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hz
    have hz0 : z ≠ 0 := hz0_of_sphere z hz
    rw [logDeriv_mul (f := fun w => w ^ m) (g := v) z (pow_ne_zero m hz0) (hv0 z hzball)
      (differentiableAt_pow m) (hv z hzball).differentiableAt, logDeriv_pow, logDeriv_apply]
  rw [circleIntegral.integral_congr hR.le hsplit]
  -- additivity (both pieces continuous on the sphere, hence integrable)
  have hint1 : CircleIntegrable (fun z : ℂ => (m : ℂ) / z) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (ContinuousOn.div continuousOn_const continuousOn_id fun z hz => hz0_of_sphere z hz)
  have hint2 : CircleIntegrable (fun z : ℂ => deriv v z / v z) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (fun z hz => ((hlog_an z (sphere_subset_closedBall hz)).continuousAt).continuousWithinAt)
  rw [circleIntegral.integral_add hint1 hint2, circleIntegral_const_div_center R hR,
    circleIntegral_logDeriv_eq_zero hR.le
      (fun z hz => ((hlog_an z hz).continuousAt).continuousWithinAt)
      (fun z hz => (hlog_an z (ball_subset_closedBall hz)).differentiableAt)]
  ring

/-!
The only remaining gap for the full argument principle is the **propagation** to `z ≠ 0` near `0`
(the integral is locally constant `= m`), which needs `(2πi)⁻¹∮ G'/G ∈ ℤ` for a general non-vanishing
family — the genuinely missing theorem (see `C_cauchy_scope.md`). The base case above is now in hand.
-/

end
