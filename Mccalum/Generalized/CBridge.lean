import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions

/-!
# Several-variable holomorphy ⇒ analyticity bridge (WIP — the C keystone bottleneck)

The keystone of the Cauchy-integral proof of `weierstrass_division` needs: a function on `ℂⁿ` that is
ℂ-Fréchet differentiable on an open set is **analytic** there. Mathlib has this **only for one complex
variable** (`DifferentiableOn.analyticOnNhd`, `f : ℂ → E`). This file states the several-variable
bridge and isolates its genuine core — **Osgood's lemma** — which is the missing several-complex-
variables theorem (a natural upstream Mathlib contribution).

**Status.** The one-variable base case is proved (it is just Mathlib). `osgood` (the inductive core) is
a `sorry` with a precise proof outline; everything past it (the `ℂⁿ` bridge by induction, and the
keystone `parametric integral is analytic`) reduces to it.
-/

noncomputable section

open Complex Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Base case (one complex variable) — proved (Mathlib).** -/
theorem bridge_one_var {f : ℂ → F} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U :=
  hf.analyticOnNhd hU

/-- **Osgood's lemma (the genuine several-complex-variables core — `sorry`).**

If `f : ℂ × E' → ℂ` is continuous near `(z₀, w₀)` and *separately analytic* (analytic in `z` for each
fixed `w` near `w₀`, and analytic in `w` for each fixed `z` near `z₀`), then it is *jointly* analytic
at `(z₀, w₀)`.

Proof outline (Hörmander, Thm 2.2.8 / Osgood): Cauchy in `z` on a small circle `∂D(z₀, r)` gives
`f(z,w) = ∑_k a_k(w)·(z − z₀)^k`, with `a_k(w) = (2πi)⁻¹ ∮_{∂D} f(ζ,w)/(ζ − z₀)^{k+1} dζ`. Each `a_k`
is analytic in `w` because it is a contour integral of the `w`-analytic family `f(ζ, ·)` — i.e. the
**keystone** ("parametric contour integral is analytic") in the `E'` variables. The joint power series
in `(z, w)` then assembles from the `a_k`. The `w`-keystone in turn reduces (differentiate under the
integral + this very bridge) to this lemma in *fewer* `E'` variables, so the rigorous statement is a
**simultaneous induction on `dim E'`** of `{osgood, bridge, keystone}`. That interconnected induction,
plus the multivariable power-series bookkeeping, is the missing development. -/
theorem osgood {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : ℂ × E' → ℂ} {z₀ : ℂ} {w₀ : E'}
    (hcont : ContinuousAt f (z₀, w₀))
    (hz : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ (fun z => f (z, w)) z₀)
    (hw : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ (fun w => f (z, w)) w₀) :
    AnalyticAt ℂ f (z₀, w₀) := by
  sorry

/-!
## How the bridge follows from `osgood` (outline)

For `f : (Fin n → ℂ) → F` differentiable on open `U`, induct on `n` via
`(Fin (n+1) → ℂ) ≃ₗ ℂ × (Fin n → ℂ)`:
* analytic in the first coordinate by `bridge_one_var` (one variable);
* analytic in the remaining coordinates by the induction hypothesis;
* jointly analytic by `osgood` (continuity is automatic: differentiable ⇒ continuous).

A general finite-dimensional complex domain `E` reduces to `Fin n → ℂ` by a `ContinuousLinearEquiv`
(analyticity transports under composition with continuous-linear maps, which are analytic). The repo's
parameter space `CParam s e = (Fin s → ℂ) × (Fin e → ℂ)` is such an `E`.

Once the bridge holds, the **keystone** (`CKeystone.lean`) is immediate: differentiate-under-integral
(Mathlib `hasFDerivAt_integral_of_dominated_…`, several-parameter form, with domination from joint
analyticity of the integrand) gives ℂ-differentiability of `z ↦ ∮ Φ(z,ζ) dζ` on a neighborhood, and
the bridge upgrades it to analyticity.
-/

end
