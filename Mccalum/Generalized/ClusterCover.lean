import Mccalum.Generalized.WeierstrassDivision
import Mccalum.Generalized.Lifting
import Mccalum.Generalized.AnalyticOrderPoly

/-!
# Cluster covering / multiplicity transfer bridges

The two bridges that turn `cluster_from_real`'s complex Weierstrass data into the real-slice
covering / multiplicity statements consumed by the A2 axiom:
* `isRoot_eq_of_unit_factor` — a unit factor doesn't change zeros near `0`;
* `cover_of_weierstrass` — produces A2's `hcover`;
* `multmatch_of_weierstrass` — produces A2's `hmult_match`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

variable {s e : ℕ}

/-- A unit factor doesn't change the zero set near `0`: if `F =ᶠ u · H` with `u 0 ≠ 0`, then `F` and
`H` have the same zeros near `0`. -/
lemma isRoot_eq_of_unit_factor (F H u : CParam s e × ℂ → ℂ)
    (hu0 : u 0 ≠ 0) (hu : AnalyticAt ℂ u 0)
    (hfac : F =ᶠ[𝓝 (0 : CParam s e × ℂ)] fun zt => u zt * H zt) :
    ∀ᶠ zt in 𝓝 (0 : CParam s e × ℂ), (F zt = 0 ↔ H zt = 0) := by
  have hu_ne : ∀ᶠ zt in 𝓝 (0 : CParam s e × ℂ), u zt ≠ 0 := by
    have hcont : ContinuousAt u 0 := hu.continuousAt
    exact hcont.eventually_ne hu0
  filter_upwards [hfac, hu_ne] with zt hf hune
  rw [hf]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hune
  · intro h; rw [h, mul_zero]

/-- **Covering transfer.** From the `u`-unit Weierstrass factorization, the complex covering of
`weierstrassPoly` by `ψ`, and the section-level map agreement, the complex roots of the complexified
section family `(fam y).map ℝ→ℂ` within a cluster radius `δ₀` are exactly the `ψ_i (realEmbedding y)`. -/
lemma cover_of_weierstrass (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (g_poly : (CParam s e → ℂ)[X])
    (u : CParam s e × ℂ → ℂ) (hu0 : u 0 ≠ 0) (hu_an : AnalyticAt ℂ u 0)
    (hfac : polyToFun s e g_poly =ᶠ[𝓝 0]
      fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt)
    {r : ℕ} (ψ : Fin r → ((Fin s → ℂ) → ℂ))
    (hroots : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
      (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ ∃ i, α = ψ i y)
    (fam : (Fin s → ℝ) → Polynomial ℂ)
    (hfam_map : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      g_poly.map (Pi.evalRingHom (fun _ => ℂ) ((realEmbedding s y, 0) : CParam s e)) = fam y) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ α : ℂ, ‖α‖ < δ₀ →
      ((fam y).IsRoot α ↔ ∃ i, α = ψ i (realEmbedding s y)) := by
  have hUF := isRoot_eq_of_unit_factor (polyToFun s e g_poly)
    (polyToFun s e (weierstrassPolyFun m a)) u hu0 hu_an hfac
  have hroots_pb : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ α : ℂ,
      (weierstrassPoly m a ((realEmbedding s y, 0) : CParam s e)).IsRoot α
        ↔ ∃ i, α = ψ i (realEmbedding s y) := by
    have htend2 : Filter.Tendsto (realEmbedding s) (𝓝 0) (𝓝 0) := by
      have := (realEmbedding s).continuous.tendsto (0 : Fin s → ℝ); rwa [map_zero] at this
    exact htend2.eventually hroots
  -- pull `hUF` back along `(y,α) ↦ ((realEmbedding s y, 0), α)`
  have htend : Filter.Tendsto
      (fun yα : (Fin s → ℝ) × ℂ => (((realEmbedding s yα.1, 0) : CParam s e), yα.2)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous
        (fun yα : (Fin s → ℝ) × ℂ => (((realEmbedding s yα.1, 0) : CParam s e), yα.2)) := by fun_prop
    have := hcont.tendsto (0 : (Fin s → ℝ) × ℂ)
    simpa [map_zero] using this
  have hUF_pb := htend.eventually hUF
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hUF_pb
  refine ⟨ε, hε, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Fin s → ℝ) hε, hroots_pb, hfam_map]
    with y hy_ball hroots_y hfam_y
  intro α hα
  have hpt : dist ((y, α) : (Fin s → ℝ) × ℂ) 0 < ε := by
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · simpa [dist_zero_right] using Metric.mem_ball.mp hy_ball
    · simpa [dist_zero_right] using hα
  have huf := hball hpt
  have e1 : (fam y).IsRoot α
      ↔ polyToFun s e g_poly ((realEmbedding s y, 0), α) = 0 := by
    rw [Polynomial.IsRoot.def, ← hfam_y, polyToFun_apply]
  have e2 : polyToFun s e (weierstrassPolyFun m a) ((realEmbedding s y, 0), α) = 0
      ↔ (weierstrassPoly m a ((realEmbedding s y, 0) : CParam s e)).IsRoot α := by
    simp [polyToFun_weierstrassPolyFun, Polynomial.IsRoot.def]
  rw [e1, huf, e2, hroots_y]

/-- **Multiplicity transfer.** Under the unit factorization, the multiplicity of a section root
`ψ_i (realEmbedding y)` in the complexified family `fam y` equals its multiplicity `mult i` in the
Weierstrass polynomial — via `analyticOrderAt = rootMultiplicity` and order-invariance under the
unit factor. -/
lemma multmatch_of_weierstrass (m : ℕ) (hm_pos : 0 < m) (a : Fin m → (CParam s e → ℂ))
    (g_poly : (CParam s e → ℂ)[X])
    (u : CParam s e × ℂ → ℂ) (hu0 : u 0 ≠ 0) (hu_an : AnalyticAt ℂ u 0)
    (hfac : polyToFun s e g_poly =ᶠ[𝓝 0]
      fun zt => u zt * polyToFun s e (weierstrassPolyFun m a) zt)
    {r : ℕ} (ψ : Fin r → ((Fin s → ℂ) → ℂ)) (mult : Fin r → ℕ)
    (hψ_an : ∀ i, AnalyticAt ℂ (ψ i) 0) (hψ0 : ∀ i, ψ i 0 = 0)
    (hmults : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ), Function.Injective (fun i => ψ i y) →
      ∀ i, (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ i y) = mult i)
    (fam : (Fin s → ℝ) → Polynomial ℂ) (hfam_ne : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), fam y ≠ 0)
    (hfam_map : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      g_poly.map (Pi.evalRingHom (fun _ => ℂ) ((realEmbedding s y, 0) : CParam s e)) = fam y) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), Function.Injective (fun i => ψ i (realEmbedding s y)) → ∀ i,
      (fam y).rootMultiplicity (ψ i (realEmbedding s y)) = mult i := by
  -- a common good neighbourhood: factorization holds, `u` is nonzero and analytic
  have hgood : ∀ᶠ zt in 𝓝 (0 : CParam s e × ℂ),
      polyToFun s e g_poly zt = u zt * polyToFun s e (weierstrassPolyFun m a) zt
      ∧ u zt ≠ 0 ∧ AnalyticAt ℂ u zt := by
    filter_upwards [hfac, hu_an.continuousAt.eventually_ne hu0, hu_an.eventually_analyticAt]
      with zt h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨W, hWsub, hWopen, hW0⟩ := eventually_nhds_iff.mp hgood
  -- pull `hmults` back to real `y`
  have hmults_pb : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      Function.Injective (fun i => ψ i (realEmbedding s y)) →
      ∀ i, (weierstrassPoly m a ((realEmbedding s y, 0) : CParam s e)).rootMultiplicity
        (ψ i (realEmbedding s y)) = mult i := by
    have htend : Filter.Tendsto (realEmbedding s) (𝓝 0) (𝓝 0) := by
      have := (realEmbedding s).continuous.tendsto (0 : Fin s → ℝ); rwa [map_zero] at this
    exact htend.eventually hmults
  -- each section point lands in `W` for `y` near `0`
  have hmem_i : ∀ i, ∀ᶠ y in 𝓝 (0 : Fin s → ℝ),
      (((realEmbedding s y, 0) : CParam s e), ψ i (realEmbedding s y)) ∈ W := by
    intro i
    have hca : ContinuousAt
        (fun y : Fin s → ℝ => (((realEmbedding s y, 0) : CParam s e), ψ i (realEmbedding s y))) 0 := by
      have h1 : ContinuousAt (fun y : Fin s → ℝ => ((realEmbedding s y, 0) : CParam s e)) 0 := by
        fun_prop
      have h2 : ContinuousAt (fun y : Fin s → ℝ => ψ i (realEmbedding s y)) 0 :=
        ((hψ_an i).continuousAt.comp_of_eq (realEmbedding s).continuous.continuousAt (map_zero _))
      exact h1.prodMk h2
    have h0 : (((realEmbedding s (0 : Fin s → ℝ), 0) : CParam s e),
        ψ i (realEmbedding s (0 : Fin s → ℝ))) = 0 := by simp [map_zero, hψ0 i]
    exact hca.preimage_mem_nhds (by rw [h0]; exact hWopen.mem_nhds hW0)
  have hall_mem : ∀ᶠ y in 𝓝 (0 : Fin s → ℝ), ∀ i,
      (((realEmbedding s y, 0) : CParam s e), ψ i (realEmbedding s y)) ∈ W :=
    (eventually_all (ι := Fin r)).mpr hmem_i
  filter_upwards [hmults_pb, hfam_ne, hfam_map, hall_mem] with y hmult_y hfam_y_ne hfam_y hmem_y
  intro hinj i
  set α := ψ i (realEmbedding s y) with hα
  set z := (realEmbedding s y, (0 : Fin e → ℂ)) with hz
  -- the section eval functions
  set fEval : ℂ → ℂ := fun t => (fam y).eval t with hfEval
  set hEval : ℂ → ℂ := fun t => (weierstrassPoly m a z).eval t with hhEval
  set uSec : ℂ → ℂ := fun t => u (z, t) with huSec
  -- germ factorization of `fEval` at `α`: holds on the open slice of `W`
  have hslice_open : IsOpen {t : ℂ | ((z, t) : CParam s e × ℂ) ∈ W} :=
    hWopen.preimage (by fun_prop)
  have hα_slice : α ∈ {t : ℂ | ((z, t) : CParam s e × ℂ) ∈ W} := hmem_y i
  have hfac_germ : fEval =ᶠ[𝓝 α] uSec * hEval := by
    filter_upwards [hslice_open.mem_nhds hα_slice] with t ht
    have hgt := hWsub _ ht
    show (fam y).eval t = u (z, t) * (weierstrassPoly m a z).eval t
    have hfg : polyToFun s e g_poly (z, t) = (fam y).eval t := by rw [polyToFun_apply, hfam_y]
    have hwp : polyToFun s e (weierstrassPolyFun m a) (z, t) = (weierstrassPoly m a z).eval t := by
      rw [polyToFun_weierstrassPolyFun]
    rw [← hfg, hgt.1, hwp]
  -- analyticity at `α`
  have hpt_an : AnalyticAt ℂ u (z, α) := (hWsub _ hα_slice).2.2
  have hincl_an : AnalyticAt ℂ (fun t : ℂ => ((z, t) : CParam s e × ℂ)) α :=
    analyticAt_const.prod analyticAt_id
  have huSec_an : AnalyticAt ℂ uSec α := hpt_an.comp_of_eq hincl_an rfl
  have huSecα : uSec α ≠ 0 := (hWsub _ hα_slice).2.1
  have hhEval_an : AnalyticAt ℂ hEval α :=
    (AnalyticOnNhd.eval_polynomial (weierstrassPoly m a z)) α (Set.mem_univ α)
  -- orders agree, convert to root multiplicities
  have hord : analyticOrderAt fEval α = analyticOrderAt hEval α :=
    analyticOrderAt_eq_of_unit_factor huSec_an huSecα hhEval_an hfac_germ
  rw [hfEval, hhEval, analyticOrderAt_polynomial_eval hfam_y_ne α,
    analyticOrderAt_polynomial_eval (weierstrassPoly_monic m a hm_pos z).ne_zero α] at hord
  have hrm : (fam y).rootMultiplicity α = (weierstrassPoly m a z).rootMultiplicity α := by
    exact_mod_cast hord
  rw [hrm]; exact hmult_y hinj i

end
