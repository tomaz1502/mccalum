import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# C keystone (WIP): analyticity of a parametric contour integral

The reusable workhorse for the Cauchy-integral proof of `weierstrass_division`: the quotient `q`, the
remainder coefficients `ρₖ`, and the power sums `pₖ` are all of the form
`z ↦ ∮_{|ζ|=R} Φ(z, ζ) dζ`, and we need each to be `AnalyticAt ℂ` in the parameter `z`.

This file records exactly **how far Mathlib carries the keystone** (see `C_cauchy_scope.md`):

* **One complex parameter (`z : ℂ`): fully supported.** `circleIntegral_analyticAt_of_differentiable_nhds`
  below is sorry-free — Mathlib's `DifferentiableOn.analyticAt` (holomorphy ⇒ analyticity, one complex
  variable) makes the analyticity step *free* once differentiability on a neighborhood is known. And
  differentiability on a neighborhood is provided by `hasDerivAt_integral_of_dominated_loc_of_lip`
  (`ParametricIntervalIntegral.lean`, `𝕜 = ℂ`); the only real work there is the *domination* bound,
  which follows from joint analyticity of `Φ` (bounded `∂_z Φ` on the compact contour).

* **Several complex parameters (`z : ℂⁿ`, our actual setting `CParam = ℂ^{s+e}`): GAP.** Mathlib's
  holomorphy ⇒ analyticity bridge is **one variable only** (`f : ℂ → E`). The `n`-variable lift
  (joint ℂ-differentiable on an open set of `ℂⁿ` ⇒ analytic) is **not in Mathlib** — it is the genuine
  missing ingredient for the keystone (provable via iterated one-variable Cauchy / a polydisc power
  series, or Osgood/Hartogs; a natural upstream contribution).
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Filter Topology

/-- **Keystone, one complex parameter (sorry-free).** If `z ↦ ∮_{C(c,R)} Φ(z,ζ) dζ` is differentiable
in `z` on a neighborhood of `z₀`, it is `AnalyticAt` at `z₀`. (The holomorphy ⇒ analyticity step is
Mathlib's `DifferentiableOn.analyticAt`; one complex variable.) -/
theorem circleIntegral_analyticAt_of_differentiable_nhds
    {Φ : ℂ → ℂ → ℂ} {c : ℂ} {R : ℝ} {z₀ : ℂ}
    (hd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun w => ∮ ζ in C(c, R), Φ w ζ) z) :
    AnalyticAt ℂ (fun z => ∮ ζ in C(c, R), Φ z ζ) z₀ := by
  obtain ⟨U, hU_sub, hU_open, hU_mem⟩ := eventually_nhds_iff.mp hd
  exact DifferentiableOn.analyticAt
    (fun z hz => (hU_sub z hz).differentiableWithinAt) (hU_open.mem_nhds hU_mem)

/-!
## Remaining obligations for the one-parameter case (named, not yet proved)

The hypothesis `hd` above is discharged by `hasDerivAt_integral_of_dominated_loc_of_lip` applied to
the interval-integral form `∮ ζ in C(c,R), Φ z ζ = ∫ θ in 0..2π, (circleMap 0 R θ * I) • Φ z (circleMap c R θ)`.
Its obligations, all standard given `Φ` analytic on a neighborhood of `{z₀} × sphere c R`:

* `AEStronglyMeasurable` of the integrand in `θ` for `z` near `z₀` — from continuity;
* `IntervalIntegrable` of the integrand at `z₀` — continuous on the compact `[0,2π]`;
* a **Lipschitz domination** `LipschitzOnWith (bound θ) (fun z => …) s` with `bound` integrable —
  the genuine work: `∂_z Φ` is bounded on the compact contour (analytic ⇒ `C¹` ⇒ bounded derivative
  on compacts), giving a *constant* `bound`;
* the a.e. pointwise `HasDerivAt (fun z => integrand) … z` — from analyticity of `Φ` in `z`.

## The several-parameter keystone (the gap)

For `z : E` with `E` a finite-dimensional complex space (here `CParam s e`), the intended statement is

  `(∀ ζ ∈ sphere c R, AnalyticAt ℂ (fun zζ : E × ℂ => Φ zζ.1 zζ.2) (z₀, ζ)) →`
  `AnalyticAt ℂ (fun z => ∮ ζ in C(c, R), Φ z ζ) z₀`.

Differentiation under the integral still gives ℂ-Fréchet-differentiability of `z ↦ ∮ Φ(z,ζ) dζ` on a
neighborhood; the missing step is **`DifferentiableOn ℂ` (on an open set of `E`) ⇒ `AnalyticOnNhd ℂ`**,
which Mathlib has only for `E = ℂ`. Building that several-variable bridge (or invoking Osgood/Hartogs)
is the first real sub-project; it is independent of integrals and belongs upstream.
-/

end
