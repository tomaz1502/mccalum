import Mccalum.Generalized.WeierstrassDefs
import Mccalum.Generalized.CWeierstrassSynthesis

/-!
# The classical analytic ingredients: convergent Weierstrass division (PROVED) & Zariski sections

* `weierstrass_division` — convergent Weierstrass division. **No longer an axiom:** it is now a
  `theorem`, discharged by `weierstrass_division_proved` (the full Cauchy-integral proof in Layer
  C/B/A, depending only on `propext, Classical.choice, Quot.sound`).
* `zariski_single_branch` — Zariski's Theorem 4.1.1 (a single holomorphic root section under
  `disc ≢ 0` and constant discriminant order along the section). This remains an axiom.

The basic definitions (`CParam`, `weierstrassPoly`, `weierstrassDiscFn`, and their monic/degree/order
properties) live in the axiom-free base `Mccalum.Generalized.WeierstrassDefs`, so the proof chain
discharging `weierstrass_division` can be imported here without a cycle.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- **Convergent Weierstrass division (Phase C) — now a theorem.** Discharged by
`weierstrass_division_proved` (several-variable holomorphy⇒analyticity bridge, the argument principle,
Newton's identities, and the `G = u·W` synthesis). -/
theorem weierstrass_division {s e : ℕ}
    (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0) :=
  weierstrass_division_proved G hG m hreg

/-- **Weierstrass division by a Weierstrass polynomial** — the special case `G = h`. -/
theorem weierstrass_division_analytic {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (F : CParam s e × ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
      F =ᶠ[𝓝 0] fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ) :=
  (weierstrass_division (fun wt => (weierstrassPoly m a wt.1).eval wt.2)
    (weierstrassPolyEval_analyticAt m a ha_an) m (weierstrassPolyEval_order m a ha0)).1 F hF

/-- **Uniqueness of Weierstrass division by a Weierstrass polynomial** — the `G = h` case. -/
theorem weierstrass_division_unique {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ))
    (hq : AnalyticAt ℂ q 0) (hρ : ∀ i, AnalyticAt ℂ (ρ i) 0)
    (hzero : (fun wt => q wt * (weierstrassPoly m a wt.1).eval wt.2
        + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0) :
    q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0 :=
  (weierstrass_division (fun wt => (weierstrassPoly m a wt.1).eval wt.2)
    (weierstrassPolyEval_analyticAt m a ha_an) m (weierstrassPolyEval_order m a ha0)).2 q ρ hq hρ hzero

/-- **Zariski's theorem 4.1.1 — single holomorphic root section (Phase E, AXIOM).**

Given a monic Weierstrass polynomial `h(w, t) = t^m + ∑ a_i(w) t^i` (coefficients analytic,
`a_i(0) = 0`) whose discriminant `disc(h)` (i) does not vanish identically and (ii) has constant
vanishing order along the section `T = ℂˢ × {0}` near `0`, the roots of `h` over `T` are a **single**
holomorphic section `ψ : ℂˢ → ℂ` (nonsplitting) of multiplicity `m`. The single deepest ingredient
(Chapter 4 / Puiseux–Newton–monodromy); nothing of it is in Mathlib. -/
axiom zariski_single_branch {s e : ℕ}
    (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ ψ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m)

end
