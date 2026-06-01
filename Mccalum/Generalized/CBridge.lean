import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Integral.TorusIntegral

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

open Complex Filter Topology Metric
open scoped Real

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
`f(z,w) = ∑_k a_k(w)·(z − z₀)^k`, with `a_k(w) = (2πi)⁻¹ ∮_{∂D} f(ζ,w)/(ζ − z₀)^{k+1} dζ`.

**Recommended formalization route — vector-valued holomorphy** (cleanest given Mathlib; from this
file's exploration). Let `K ⊆ E'` be a small closed ball around `w₀` and `H := C(K, ℂ)` the Banach
space of continuous functions on `K` (sup norm). Consider `g : ℂ → H`, `g z := (w ↦ f (z, w))|_K`.
* `g` is **ℂ-differentiable** near `z₀` (the difference quotients converge in sup-norm, from joint
  continuity + analyticity in `z`). Then by Mathlib's one-variable `Differentiable.analyticAt`
  — which holds for **any** complex Banach codomain — `g` is **analytic**, so
  `g z = ∑_k a_k · (z − z₀)^k` with `a_k ∈ H`, the series converging **in sup-norm, i.e. uniformly in
  `w ∈ K`**. This handles the `z`-direction *and the uniformity* for free — the main payoff.
* Each coefficient `a_k ∈ H` is then shown **analytic in `w`** (it is a `w`-Taylor datum of the
  `w`-analytic slices; or a contour integral of the `w`-analytic family `f(ζ,·)`).
* The uniform-in-`w` series `∑_k a_k(w)(z−z₀)^k` with `a_k` analytic in `w` assembles to a **joint**
  power series at `(z₀, w₀)` (each partial sum is jointly analytic; uniform convergence upgrades the
  limit — the analogue of `TendstoLocallyUniformlyOn.differentiableOn`, which Mathlib currently has
  only for the **one-variable** domain `ℂ`).

The two remaining obligations (`a_k` analytic in `w`; uniform-limit ⇒ jointly analytic in several
variables) still recurse on `dim E'` through the keystone, so the rigorous result is a **simultaneous
induction on `dim E'`** of `{osgood, bridge, keystone}`. This is the missing SCV development — Mathlib
has *no* several-complex-variables analyticity (no multivariable Cauchy formula; the
several-variable locally-uniform-limit theorem is also absent). A multi-session / upstream effort. -/
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

/-- **Inductive step of the SCV bridge (deploys `osgood`).** If the holomorphy⇒analyticity bridge
holds on `E'` (the induction hypothesis), then — given `osgood` — it holds on `ℂ × E'`: a function
`f` that is jointly ℂ-differentiable on an open `U ⊆ ℂ × E'` is analytic there. At each point, the
`z`-slices are differentiable (hence analytic by `bridge_one_var`) and the `w`-slices are
differentiable (hence analytic by the `E'`-bridge), and `f` is continuous; `osgood` upgrades separate
analyticity + continuity to joint analyticity. Iterating this from `bridge_one_var` gives the bridge
on `ℂⁿ`, which discharges the keystone. -/
theorem bridge_prod {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (hbridge_E' : ∀ {g : E' → ℂ} {V : Set E'}, IsOpen V → DifferentiableOn ℂ g V → AnalyticOnNhd ℂ g V)
    {f : ℂ × E' → ℂ} {U : Set (ℂ × E')} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U := by
  rintro ⟨z₀, w₀⟩ hp
  obtain ⟨u, v, hu_o, hv_o, hz₀u, hw₀v, huv⟩ := isOpen_prod_iff.mp hU z₀ w₀ hp
  refine osgood ((hf.differentiableAt (hU.mem_nhds hp)).continuousAt) ?_ ?_
  · -- `z`-slices analytic at `z₀`, for `w` near `w₀`
    filter_upwards [hv_o.mem_nhds hw₀v] with w hwv
    have hslice : DifferentiableOn ℂ (fun z => f (z, w)) u := fun z hzu =>
      ((hf.differentiableAt (hU.mem_nhds (huv (Set.mk_mem_prod hzu hwv)))).comp z
        (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const w))).differentiableWithinAt
    exact bridge_one_var hu_o hslice z₀ hz₀u
  · -- `w`-slices analytic at `w₀`, for `z` near `z₀`
    filter_upwards [hu_o.mem_nhds hz₀u] with z hzu
    have hslice : DifferentiableOn ℂ (fun w => f (z, w)) v := fun w hwv =>
      ((hf.differentiableAt (hU.mem_nhds (huv (Set.mk_mem_prod hzu hwv)))).comp w
        (DifferentiableAt.prodMk (differentiableAt_const z) differentiableAt_id)).differentiableWithinAt
    exact hbridge_E' hv_o hslice w₀ hw₀v

/-! ## Toward `osgood`'s core: the polydisc–Cauchy route

For the **bridge** the keystone actually needs (jointly ℂ-differentiable ⇒ analytic), the cleanest
route is the polydisc Cauchy formula — it avoids `osgood`'s separate-analyticity entirely:
1. **`z`-slice Cauchy** (below): `f(z,w) = (2πi)⁻¹∮_ζ f(ζ,w)/(ζ−z)` (1-variable Cauchy on the slice).
2. **`w`-slice Cauchy** inside: `f(ζ,w) = (2πi)⁻¹∮_η f(ζ,η)/(η−w)`.
3. **Fubini** ⟹ the torus integral `f(z,w) = (2πi)⁻²∮∮ f(ζ,η)/((ζ−z)(η−w))`.
4. **expand the kernel** `1/((ζ−z)(η−w)) = ∑_{j,k} (z−z₀)^j(w−w₀)^k/((ζ−z₀)^{j+1}(η−w₀)^{k+1})`
   and assemble a **several-variable power series** ⟹ analytic.

Steps 1–3 are completable with Mathlib's 1-variable Cauchy + `TorusIntegral`. **Step 4 is the
irreducible Mathlib gap**: constructing a `HasFPowerSeriesAt` on `ℂ²` (a `FormalMultilinearSeries`
from the double-indexed coefficients with convergence) — Mathlib has no several-variable
power-series-from-integral nor a several-variable locally-uniform-limit theorem. -/

/-- **Step 1: `z`-slice Cauchy representation** of a jointly ℂ-differentiable function. On a small
polydisc around `(z₀, w₀) ∈ U`, `f(z, w) = (2πi)⁻¹∮_{|ζ−z₀|=r} f(ζ,w)/(ζ − z) dζ`. The slice `f(·,w)`
is holomorphic on the closed disc (restriction of the jointly-differentiable `f`), so this is the
one-variable Cauchy integral formula. Completable; the first concrete step of the polydisc route. -/
theorem bridge_z_repr {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : ℂ × E' → ℂ} {U : Set (ℂ × E')} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z₀ : ℂ} {w₀ : E'} (hp : (z₀, w₀) ∈ U) :
    ∃ r > 0, ∃ v ∈ 𝓝 w₀, ∀ w ∈ v, ∀ z ∈ ball z₀ r,
      f (z, w) = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f (ζ, w) := by
  obtain ⟨u, v, hu_o, hv_o, hz₀u, hw₀v, huv⟩ := isOpen_prod_iff.mp hU z₀ w₀ hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hu_o z₀ hz₀u
  refine ⟨r / 2, by positivity, v, hv_o.mem_nhds hw₀v, fun w hwv z hz => ?_⟩
  have hmemU : ∀ ζ ∈ closedBall z₀ (r / 2), (ζ, w) ∈ U := fun ζ hζ =>
    huv (Set.mk_mem_prod (hball (closedBall_subset_ball (by linarith) hζ)) hwv)
  have hslice_diff : ∀ ζ ∈ closedBall z₀ (r / 2), DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ :=
    fun ζ hζ => (hf.differentiableAt (hU.mem_nhds (hmemU ζ hζ))).comp ζ
      (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const w))
  exact (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hz (fun ζ hζ => (hslice_diff ζ hζ).continuousAt.continuousWithinAt)
    (fun ζ hζ => hslice_diff ζ (ball_subset_closedBall hζ.1))).symm

/-- **Steps 1–3 combined: the iterated (torus) Cauchy representation on `ℂ²`.** A jointly
ℂ-differentiable `f : ℂ × ℂ → ℂ` equals, on a small polydisc around `(z₀, w₀)`, the iterated double
Cauchy integral `f(z,w) = (2πi)⁻²∮_ζ∮_η f(ζ,η)/((ζ−z)(η−w))`. Proof: 1-variable Cauchy in `z` (the
`z`-slice is holomorphic), then 1-variable Cauchy in `w` for each `ζ` on the `z`-circle, substituted
under the outer integral. This is the furthest the polydisc route goes *completably* — what remains
(Step 4) is expanding the kernel into a several-variable power series, the irreducible Mathlib gap. -/
theorem bridge_torus_repr {f : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z₀ w₀ : ℂ} (hp : (z₀, w₀) ∈ U) :
    ∃ rz > 0, ∃ rw > 0, ∀ z ∈ ball z₀ rz, ∀ w ∈ ball w₀ rw,
      f (z, w) = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz), (ζ - z)⁻¹ •
        ((2 * π * I : ℂ)⁻¹ • ∮ η in C(w₀, rw), (η - w)⁻¹ • f (ζ, η)) := by
  obtain ⟨u, v, hu_o, hv_o, hz₀u, hw₀v, huv⟩ := isOpen_prod_iff.mp hU z₀ w₀ hp
  obtain ⟨rz, hrz, hballz⟩ := Metric.isOpen_iff.mp hu_o z₀ hz₀u
  obtain ⟨rw, hrw, hballw⟩ := Metric.isOpen_iff.mp hv_o w₀ hw₀v
  refine ⟨rz / 2, by positivity, rw / 2, by positivity, fun z hz w hw => ?_⟩
  have hdiff : ∀ ζ ∈ closedBall z₀ (rz / 2), ∀ η ∈ closedBall w₀ (rw / 2),
      DifferentiableAt ℂ f (ζ, η) := fun ζ hζ η hη => hf.differentiableAt (hU.mem_nhds
        (huv (Set.mk_mem_prod (hballz (closedBall_subset_ball (by linarith) hζ))
          (hballw (closedBall_subset_ball (by linarith) hη)))))
  -- slice differentiability (composition with the affine embeddings)
  have hzs : ∀ ζ ∈ closedBall z₀ (rz / 2), DifferentiableAt ℂ (fun ζ' => f (ζ', w)) ζ :=
    fun ζ hζ => (hdiff ζ hζ w (ball_subset_closedBall hw)).comp ζ
      (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const w))
  have hws : ∀ ζ ∈ closedBall z₀ (rz / 2), ∀ η ∈ closedBall w₀ (rw / 2),
      DifferentiableAt ℂ (fun η' => f (ζ, η')) η := fun ζ hζ η hη =>
    (hdiff ζ hζ η hη).comp η (DifferentiableAt.prodMk (differentiableAt_const ζ) differentiableAt_id)
  -- Step 1: `z`-Cauchy
  have hstep1 : f (z, w) = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, rz / 2), (ζ - z)⁻¹ • f (ζ, w) :=
    (two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hz (fun ζ hζ => (hzs ζ hζ).continuousAt.continuousWithinAt)
      (fun ζ hζ => hzs ζ (ball_subset_closedBall hζ.1))).symm
  -- Step 2: `w`-Cauchy for each `ζ` on the `z`-circle, substituted under the outer integral
  rw [hstep1]
  congr 1
  refine circleIntegral.integral_congr (by positivity) (fun ζ hζ => ?_)
  have hζcb : ζ ∈ closedBall z₀ (rz / 2) := sphere_subset_closedBall hζ
  rw [(two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw (fun η hη => (hws ζ hζcb η hη).continuousAt.continuousWithinAt)
    (fun η hη => hws ζ hζcb η (ball_subset_closedBall hη.1))).symm]

end
