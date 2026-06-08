import Mccalum.Puiseux.Conclusion2E1
import Mccalum.Generalized.CParamWiring
import Mccalum.Generalized.FamilyGlobalize
import Mccalum.Generalized.SeparableDiscr
import Mccalum.Generalized.CoordTranslate
import Mccalum.Generalized.A5Coincidence
import Mccalum.Generalized.ZariskiFactorization

/-!
# Conclusion 2, codim-1 — Weierstrass setup (e = 1)

`branch_orders_constant_e1_weierstrass` is the Conclusion-2 analogue of
`ZariskiE1.irreducible_section_single_root_e1`: from an irreducible Weierstrass family `H` over
`CParam s 1` with finite, section-constant discriminant order, it produces a Puiseux parametrization
`φ` and a primitive `d`-th root `ζ` whose branch-difference orders are locally constant — i.e.
Lemma 4.2.7 for the actual axiom data. It reuses the `ZariskiE1` coordinate/globalization setup and
feeds `branch_orders_constant_e1`.
-/

noncomputable section

open Polynomial Filter Metric Set CoordTranslate CParamWiring
open scoped Topology

namespace Puiseux

/-- **Lemma 4.2.7 for the codim-1 axiom data.** For an irreducible Weierstrass family `H` of degree
`d ≥ 2` over `CParam s 1` with finite, section-constant discriminant order, there is a (globalized)
Weierstrass family `qt`, a Puiseux parametrization `φ`, and a primitive `d`-th root of unity `ζ`,
such that the branch-difference orders `ord_u(φ(z,ζⁱu) − φ(z,ζʲu))` are locally constant in `z`
near `0`. -/
theorem branch_orders_constant_e1_weierstrass {s : ℕ}
    (H : CParam s 1 → Polynomial ℂ) (d : ℕ) (hd : 2 ≤ d)
    (hH_fam : IsWeierstrassFamily H d) (hH_irr : WeierstrassIrreducible H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s 1) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s 1)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s 1)) :
    ∃ (qt : (Fin (s + 1) → ℂ) → Polynomial ℂ) (φ : (Fin s → ℂ) × ℂ → ℂ) (ζ : ℂ),
      IsPrimitiveRoot ζ d ∧
      ∀ᶠ z in 𝓝 (0 : Fin s → ℂ), ∀ i j : Fin d, i ≠ j →
        analyticOrderAt (fun u => φ (z, ζ ^ (i : ℕ) * u) - φ (z, ζ ^ (j : ℕ) * u)) 0
        = analyticOrderAt
            (fun u => φ ((0 : Fin s → ℂ), ζ ^ (i : ℕ) * u)
              - φ ((0 : Fin s → ℂ), ζ ^ (j : ℕ) * u)) 0 := by
  classical
  have hd0 : 0 < d := by omega
  set Φ := cparamEquiv s with hΦ
  have hΦsymm0 : Φ.symm 0 = 0 := by rw [hΦ]; exact map_zero _
  have hΦsym_an : AnalyticAt ℂ (fun z => Φ.symm z) (0 : Fin (s + 1) → ℂ) :=
    (Φ.symm : (Fin (s + 1) → ℂ) →L[ℂ] CParam s 1).analyticAt 0
  have hΦ0 : Φ (0 : CParam s 1) = 0 := by rw [hΦ]; exact map_zero _
  have hΦ_an : AnalyticAt ℂ (fun w => Φ w) (0 : CParam s 1) :=
    (Φ : CParam s 1 →L[ℂ] (Fin (s + 1) → ℂ)).analyticAt 0
  -- the family `q := H ∘ Φ.symm` and its globalization `qt`
  set q : (Fin (s + 1) → ℂ) → Polynomial ℂ := fun z => H (Φ.symm z) with hq
  have hq_monic : ∀ z, (q z).Monic := fun z => hH_fam.monic _
  have hq_deg : ∀ z, (q z).natDegree = d := fun z => hH_fam.degree_eq _
  have hq_coeff0 : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (0 : Fin (s + 1) → ℂ) := fun i =>
    (hH_fam.coeff_analyticAt i).comp_of_eq hΦsym_an hΦsymm0
  obtain ⟨qt, r, hr0, hqt_monic, hqt_deg, hqt_cont, hqt_eq, hqt_ana⟩ :=
    FamilyGlobalize.exists_globalized_family q hq_monic hq_deg hq_coeff0
  have hq0 : q 0 = X ^ d := by show H (Φ.symm 0) = X ^ d; rw [hΦsymm0]; exact hH_fam.eval_zero
  have hqt0 : qt 0 = X ^ d := by rw [hqt_eq 0 (mem_ball_self hr0)]; exact hq0
  -- discriminant order facts (transported through `Φ`), as in `ZariskiE1`
  set D : (Fin (s + 1) → ℂ) → ℂ := fun z => (q z).discr with hD
  have hHdisc_an : AnalyticAt ℂ (fun w => (H w).discr) (0 : CParam s 1) :=
    familyDiscr_analyticAt H d hd0 hH_fam.monic hH_fam.degree_eq hH_fam.coeff_analyticAt
  have hDan : AnalyticAt ℂ D 0 := hHdisc_an.comp_of_eq hΦsym_an hΦsymm0
  have hD0 : D 0 = 0 := by show (q 0).discr = 0; rw [hq0]; exact discr_X_pow_eq_zero hd
  have hDw : ∀ w, order ℂ D w = order ℂ (fun u => (H u).discr) (Φ.symm w) := fun w =>
    order_comp_cle Φ.symm (fun u => (H u).discr) w
  have hord0 : order ℂ D 0 = order ℂ (fun w => (H w).discr) (0 : CParam s 1) := by
    rw [hDw 0, hΦsymm0]
  have hconst : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ),
      order ℂ D w = order ℂ D 0 := by
    have htail : Tendsto (fun w : Fin (s + 1) → ℂ => Fin.tail w)
        (𝓝[{z | z 0 = 0}] (0 : Fin (s + 1) → ℂ)) (𝓝 (0 : Fin s → ℂ)) := by
      have hc : Continuous (fun w : Fin (s + 1) → ℂ => Fin.tail w) :=
        continuous_pi (fun i => continuous_apply _)
      have h0 : Fin.tail (0 : Fin (s + 1) → ℂ) = 0 := by funext i; rfl
      exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
    filter_upwards [htail.eventually hHdisc_oi, eventually_mem_nhdsWithin] with w hw_oi hw_mem
    have hw0 : w 0 = 0 := hw_mem
    have hΦw : Φ.symm w = (Fin.tail w, (0 : Fin 1 → ℂ)) := by
      rw [hΦ, cparamEquiv_symm_apply]; refine Prod.ext rfl ?_; funext i; simp [hw0]
    rw [hDw w, hΦw, hw_oi]; exact hord0.symm
  have hsep_ev : ∀ᶠ z in 𝓝 (0 : Fin (s + 1) → ℂ), z 0 ≠ 0 → D z ≠ 0 :=
    DiscNormalForm.sep_off_hyperplane D hDan hD0 (by rw [hord0]; exact hHdisc_ne) hconst
  obtain ⟨δ₀, hδ₀, hsep_ball⟩ := Metric.eventually_nhds_iff.mp hsep_ev
  -- working radius and region
  set R₀ : ℝ := min r δ₀ with hR₀
  have hR₀0 : 0 < R₀ := lt_min hr0 hδ₀
  have hR₀r : R₀ ≤ r := min_le_left _ _
  have hR₀δ₀ : R₀ ≤ δ₀ := min_le_right _ _
  set c : ℝ := Real.log (R₀ / 2) with hc
  have hexpc : Real.exp c = R₀ / 2 := by rw [hc, Real.exp_log (by positivity)]
  set δz : ℝ := R₀ / 2 with hδzdef
  have hδz : 0 < δz := by positivity
  -- `baseU s δz c ⊆ ball 0 R₀`
  have hbaseU_ball : ∀ y ∈ baseU s δz c, y ∈ ball (0 : Fin (s + 1) → ℂ) R₀ := by
    intro y hy
    rw [mem_ball_zero_iff]
    calc ‖y‖ ≤ max (‖y 0‖) (‖Fin.tail y‖) := norm_le_max_zero_tail y
      _ < R₀ := by
          refine max_lt ?_ ?_
          · have h := hy.2.1; rw [hexpc] at h; linarith [half_lt_self hR₀0]
          · have h := hy.2.2; rw [hδzdef] at h; linarith [half_lt_self hR₀0]
  have hanaU : ∀ i, ∀ y ∈ baseU s δz c, AnalyticAt ℂ (fun z => (qt z).coeff i) y :=
    fun i y hy => hqt_ana i y (ball_subset_ball hR₀r (hbaseU_ball y hy))
  have hsep_baseU : ∀ y ∈ baseU s δz c, (qt y).Separable := by
    intro y hy
    have hyR₀ : y ∈ ball (0 : Fin (s + 1) → ℂ) R₀ := hbaseU_ball y hy
    rw [hqt_eq y (ball_subset_ball hR₀r hyR₀)]
    have hdy : D y ≠ 0 := hsep_ball (by
      rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.mp hyR₀) hR₀δ₀)
      (norm_pos_iff.mp hy.1)
    exact separable_of_discr_ne_zero (hq_monic y) (by rw [hq_deg y]; omega) hdy
  -- irreducibility of `qt`
  have hirr : UnivIrreducibleGen qt := by
    refine univIrreducibleGen_of_germ qt hqt_monic hqt_deg
      (fun i => hqt_ana i 0 (mem_ball_self hr0)) ?_
    rintro ⟨dA, dB, HA, HB, hdA, hdB, hHAm, hHAd, hHAc, hHA0, hHBm, hHBd, hHBc, hHB0, heq⟩
    apply hH_irr.2
    have hfam : ∀ (HX : (Fin (s + 1) → ℂ) → Polynomial ℂ) (dX : ℕ),
        (∀ y, (HX y).Monic) → (∀ y, (HX y).natDegree = dX) →
        (∀ i, AnalyticAt ℂ (fun y => (HX y).coeff i) 0) → HX 0 = X ^ dX →
        IsWeierstrassFamily (fun w => HX (Φ w)) dX := by
      intro HX dX hm hdg hcf h0
      refine ⟨fun w => hm _, fun w => hdg _, fun i => (hcf i).comp_of_eq hΦ_an hΦ0, fun i hi => ?_⟩
      show (HX (Φ (0 : CParam s 1))).coeff i = 0
      rw [hΦ0, h0, Polynomial.coeff_X_pow, if_neg (by omega)]
    have hprod : ∀ᶠ w in 𝓝 (0 : CParam s 1), H w = HA (Φ w) * HB (Φ w) := by
      have hqeq : ∀ᶠ x in 𝓝 (0 : Fin (s + 1) → ℂ), q x = HA x * HB x := by
        filter_upwards [heq, isOpen_ball.mem_nhds (mem_ball_self hr0)] with x hx hxr
        rw [← hqt_eq x hxr]; exact hx
      have hΦtend : Tendsto (fun w : CParam s 1 => Φ w) (𝓝 0) (𝓝 (0 : Fin (s + 1) → ℂ)) := by
        have := Φ.continuous.tendsto (0 : CParam s 1); rwa [hΦ0] at this
      filter_upwards [hΦtend.eventually hqeq] with w hw
      have hqΦ : q (Φ w) = H w := by show H (Φ.symm (Φ w)) = H w; rw [Φ.symm_apply_apply]
      rw [← hqΦ]; exact hw
    exact ⟨dA, dB, fun w => HA (Φ w), fun w => HB (Φ w), hdA, hdB,
      hfam HA dA hHAm hHAd hHAc hHA0, hfam HB dB hHBm hHBd hHBc hHB0, hprod⟩
  -- contour radii
  set R : ℝ := min 1 (R₀ / 2) / 2 with hRdef
  have hR0 : 0 < R := by have := lt_min one_pos (by positivity : (0:ℝ) < R₀/2); positivity
  set ρ : ℝ := R / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρR : ρ < R := by rw [hρdef]; linarith [half_lt_self hR0]
  have hRc : R ^ d < Real.exp c := by
    rw [hexpc]
    have hRle1 : R ≤ 1 := by
      rw [hRdef]; have : min 1 (R₀ / 2) ≤ 1 := min_le_left _ _; linarith
    have hRleR₀4 : R ≤ R₀ / 4 := by
      rw [hRdef]; have : min 1 (R₀ / 2) ≤ R₀ / 2 := min_le_right _ _; linarith
    calc R ^ d ≤ R ^ 1 := pow_le_pow_of_le_one hR0.le hRle1 (by omega)
      _ = R := pow_one R
      _ ≤ R₀ / 4 := hRleR₀4
      _ < R₀ / 2 := by linarith [hR₀0]
  -- discriminant obligations for `qt`, transferred from `D` (`qt = q` on `ball 0 r`)
  have hqtD : ∀ w ∈ ball (0 : Fin (s + 1) → ℂ) r,
      (fun y => (qt y).discr) =ᶠ[𝓝 w] D := by
    intro w hw
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy
    show (qt y).discr = (q y).discr; rw [hqt_eq y hy]
  have hqtD0 : order ℂ (fun y => (qt y).discr) 0 = order ℂ D 0 :=
    order_congr_of_eventuallyEq' (hqtD 0 (mem_ball_self hr0))
  have hdisc_ne : order ℂ (fun y => (qt y).discr) (0 : Fin (s + 1) → ℂ) ≠ ⊤ := by
    rw [hqtD0, hord0]; exact hHdisc_ne
  have hdisc_const : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ),
      order ℂ (fun y => (qt y).discr) w = order ℂ (fun y => (qt y).discr) 0 := by
    filter_upwards [hconst,
      (nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr0)) :
        ball (0 : Fin (s + 1) → ℂ) r ∈ 𝓝[_] (0 : Fin (s + 1) → ℂ))] with w hw_const hw_ball
    rw [order_congr_of_eventuallyEq' (hqtD w hw_ball), hqtD0, hw_const]
  have hord_ne0 : order ℂ D 0 ≠ 0 := order_ne_zero_of_eq_zero D 0 hD0
  have hdisc_vanish : ∀ᶠ y in 𝓝 (0 : Fin (s + 1) → ℂ), y 0 = 0 → (qt y).discr = 0 := by
    have hDvanish : ∀ᶠ w in 𝓝[{z : Fin (s + 1) → ℂ | z 0 = 0}] (0 : Fin (s + 1) → ℂ), D w = 0 := by
      filter_upwards [hconst] with w hw
      by_contra hDw
      exact hord_ne0 (hw.symm.trans (order_eq_zero_of_ne D w hDw))
    rw [eventually_nhdsWithin_iff] at hDvanish
    filter_upwards [hDvanish, isOpen_ball.mem_nhds (mem_ball_self hr0)] with y hy_imp hy_ball hy0
    show (qt y).discr = 0
    rw [hqt_eq y hy_ball]; exact hy_imp hy0
  have hsep_nbhd : ∀ᶠ z in 𝓝 (0 : Fin s → ℂ),
      ∀ᶠ u in 𝓝[≠] (0 : ℂ), (qt (Fin.cons (u ^ d) z)).Separable := by
    have hκ : Continuous
        (fun p : (Fin s → ℂ) × ℂ => (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ)) := by
      refine continuous_pi (fun j => ?_)
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; exact (continuous_pow d).comp continuous_snd
      · simp only [Fin.cons_succ]; exact (continuous_apply i).comp continuous_fst
    have hκ0 : (Fin.cons ((0 : ℂ) ^ d) (0 : Fin s → ℂ) : Fin (s + 1) → ℂ) = 0 := by
      funext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp [zero_pow hd0.ne']
    have htend : Tendsto (fun p : (Fin s → ℂ) × ℂ => (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ))
        (𝓝 ((0 : Fin s → ℂ), (0 : ℂ))) (𝓝 0) := by
      have h1 := hκ.tendsto ((0 : Fin s → ℂ), (0 : ℂ))
      simpa only [hκ0] using h1
    have hpre : ∀ᶠ p in 𝓝 ((0 : Fin s → ℂ), (0 : ℂ)),
        (Fin.cons (p.2 ^ d) p.1 : Fin (s + 1) → ℂ) ∈ ball 0 R₀ :=
      htend.eventually (ball_mem_nhds 0 hR₀0)
    rw [nhds_prod_eq] at hpre
    filter_upwards [hpre.curry] with z hz_u
    filter_upwards [hz_u.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu_ball hu_ne
    have hune : u ≠ 0 := hu_ne
    have hyball : (Fin.cons (u ^ d) z : Fin (s + 1) → ℂ) ∈ ball 0 R₀ := hu_ball
    rw [hqt_eq _ (ball_subset_ball hR₀r hyball)]
    refine separable_of_discr_ne_zero (hq_monic _) (by rw [hq_deg _]; omega) ?_
    refine hsep_ball (by
      rw [dist_zero_right]
      exact lt_of_lt_of_le (mem_ball_zero_iff.mp hyball) hR₀δ₀) ?_
    rw [Fin.cons_zero]; exact pow_ne_zero d hune
  obtain ⟨φ, ζ, hζ, _hpar, hbranch⟩ :=
    branch_orders_constant_e1 hd0 hqt_monic hqt_deg hqt_cont
      (fun i => hqt_ana i 0 (mem_ball_self hr0)) hqt0 hirr hδz hanaU hsep_baseU hsep_nbhd
      hρ hρR hRc hdisc_vanish hdisc_ne hdisc_const
  exact ⟨qt, φ, ζ, hζ, hbranch⟩

end Puiseux
