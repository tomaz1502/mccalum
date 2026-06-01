import Mccalum.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The two classical analytic axioms: convergent Weierstrass preparation & Zariski root sections

This file isolates the **two genuinely deep, classical analytic-geometry ingredients** of
McCallum's generalized lifting proof as clean, named axioms:

* `weierstrass_preparation_analytic` — convergent Weierstrass preparation (Phase C).
* `zariski_single_branch` — Zariski's Theorem 4.1.1: a single holomorphic root section
  (nonsplitting) under `disc ≢ 0` and constant discriminant order along the section (Phase E).

Both are stated at the **analytic-function level** (coefficients / roots as `AnalyticAt ℂ`
functions), deliberately decoupled from the germ-ring substrate `𝒪ₙ`
(`Mccalum.Generalized.AnalyticGerm`): the germ ring is an internal tool of Phase D and need not
appear in the public interfaces of C/E. The connective phases A, D, F (proved separately) wire the
real lifting axiom against these two, so that — once they are in place — the main theorem
`mccallum_3_2_3_generalized` depends only on these two axioms plus the standard
`propext, Classical.choice, Quot.sound`.

These are NOT the end state: both are standard, citable classical theorems (Weierstrass
preparation; Zariski equisingularity / Newton–Puiseux), to be discharged in a later effort. Stating
them crisply here pins down exactly the interface they must satisfy.

## Parameter conventions

The lifting problem has parameter space `ℝˢ × ℝᵉ` and a distinguished polynomial variable `t`.
Complexified, the parameter space is `CParam s e = (ℂˢ) × (ℂᵉ)`; the **section** is
`T = ℂˢ × {0}` (the `e`-directions are the "transverse" factor that only exists to make the
witness order finite — see the lifting axiom). Roots are localized at a real root `β` of
`g(0,0)`, shifted to `t = 0`, so a Weierstrass polynomial has all roots `→ 0` along `T`.
-/

noncomputable section

open Filter Polynomial
open scoped Topology

/-- Complexified parameter space: `s` section variables × `e` transverse variables. -/
abbrev CParam (s e : ℕ) : Type := (Fin s → ℂ) × (Fin e → ℂ)

/-- The monic degree-`m` polynomial `t^m + ∑_{i<m} a_i(w)·t^i` (a Weierstrass polynomial in `t`
when `a_i(0) = 0`), with coefficients evaluated at the parameter point `w`. -/
def weierstrassPoly {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) (w : CParam s e) :
    Polynomial ℂ :=
  X ^ m + ∑ i : Fin m, C (a i w) * X ^ (i : ℕ)

/-- The discriminant of the section Weierstrass polynomial, as a function of the *full* parameter
`w` (its order along the section `T` is the Zariski equisingularity invariant). -/
def weierstrassDiscFn {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ)) :
    CParam s e → ℂ :=
  fun w => Polynomial.discr (weierstrassPoly m a w)

/-- **Convergent Weierstrass division (Phase C, the single AXIOM).**

The one classical analytic input of Phase C, in its primitive form (division by an arbitrary
`t`-regular germ). If `G : (ℂˢ × ℂᵉ) × ℂ → ℂ` is analytic at `0` and its restriction `t ↦ G(0,t)`
vanishes to order exactly `m` at `t = 0` (so `G` is "`t`-regular of order `m`"), then **(existence)**
every analytic germ `F` divides as `F = q·G + r` with `q` analytic and `r = ∑_{i<m} ρ_i(z) t^i` a
degree-`<m` polynomial remainder (analytic coefficients), and **(uniqueness)** the only such division
of the zero germ is the trivial one.

This is the classical convergent (analytic) Weierstrass division theorem (existence + uniqueness),
which is the *primitive* of Phase C: Weierstrass **preparation** is the corollary obtained by
dividing `t^m` by `G` (`weierstrass_preparation_analytic`), and division **by a Weierstrass
polynomial** (`weierstrass_division_analytic` / `_unique`) is the special case `G = h`. Mathlib has
only the *formal* version (`PowerSeries.exists_isWeierstrassDivision`); the convergence of `q`, `r` is
the deep content (classically via the Cauchy-integral division formula). -/
axiom weierstrass_division {s e : ℕ}
    (G : CParam s e × ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (m : ℕ) (hreg : analyticOrderAt (fun t : ℂ => G (0, t)) 0 = (m : ℕ∞)) :
    (∀ F : CParam s e × ℂ → ℂ, AnalyticAt ℂ F 0 →
      ∃ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
        AnalyticAt ℂ q 0 ∧ (∀ i, AnalyticAt ℂ (ρ i) 0) ∧
        F =ᶠ[𝓝 0] fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) ∧
    (∀ (q : CParam s e × ℂ → ℂ) (ρ : Fin m → (CParam s e → ℂ)),
      AnalyticAt ℂ q 0 → (∀ i, AnalyticAt ℂ (ρ i) 0) →
      (fun wt => q wt * G wt + ∑ i : Fin m, ρ i wt.1 * wt.2 ^ (i : ℕ)) =ᶠ[𝓝 0] 0 →
      q =ᶠ[𝓝 0] 0 ∧ ∀ i, ρ i =ᶠ[𝓝 (0 : CParam s e)] 0)

/-- Pointwise expansion of the Weierstrass polynomial's evaluation. -/
private lemma weierstrassPoly_eval_eq {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (w : CParam s e) (t : ℂ) :
    (weierstrassPoly m a w).eval t = t ^ m + ∑ i : Fin m, a i w * t ^ (i : ℕ) := by
  simp only [weierstrassPoly, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]

/-- The Weierstrass polynomial's evaluation `(w,t) ↦ h(w,t)` is analytic at `0`. -/
private lemma weierstrassPolyEval_analyticAt {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2) 0 := by
  have heq : (fun wt : CParam s e × ℂ => (weierstrassPoly m a wt.1).eval wt.2)
      = fun wt => wt.2 ^ m + ∑ i : Fin m, a i wt.1 * wt.2 ^ (i : ℕ) :=
    funext fun wt => weierstrassPoly_eval_eq m a wt.1 wt.2
  rw [heq]
  have hsnd : AnalyticAt ℂ (fun wt : CParam s e × ℂ => wt.2) 0 := analyticAt_snd
  have hfst : AnalyticAt ℂ (fun wt : CParam s e × ℂ => wt.1) 0 := analyticAt_fst
  refine (hsnd.pow m).add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
  exact ((ha_an i).comp_of_eq hfst rfl).mul (hsnd.pow (i : ℕ))

/-- On the distinguished line `w = 0`, the Weierstrass polynomial is `t ↦ t^m`, of order `m`. -/
private lemma weierstrassPolyEval_order {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha0 : ∀ i, a i 0 = 0) :
    analyticOrderAt (fun t : ℂ => (weierstrassPoly m a (0 : CParam s e)).eval t) 0 = (m : ℕ∞) := by
  have heq : (fun t : ℂ => (weierstrassPoly m a (0 : CParam s e)).eval t) = fun t : ℂ => t ^ m := by
    funext t; rw [weierstrassPoly_eval_eq]; simp [ha0]
  rw [heq, show (fun t : ℂ => t ^ m) = (id : ℂ → ℂ) ^ m from rfl,
    analyticOrderAt_pow analyticAt_id m, analyticOrderAt_id]
  simp [nsmul_eq_mul]

/-- **Weierstrass division by a Weierstrass polynomial** — derived from `weierstrass_division` as the
special case `G = h` (a Weierstrass polynomial is `t`-regular of order `m`, since `h(0,t) = t^m`). -/
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

/-- **Uniqueness of Weierstrass division by a Weierstrass polynomial** — the `G = h` case of
`weierstrass_division`'s uniqueness clause. -/
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

-- `weierstrass_preparation_analytic` is now a **theorem**, derived from `weierstrass_division`
-- (the unit argument) in `Mccalum.Generalized.WeierstrassPrep`.

/-- **Zariski's theorem 4.1.1 — single holomorphic root section (Phase E, AXIOM).**

This is the *exact* statement of Theorem 4.1.1 of the thesis (an adaptation of Zariski 1975).
Given a monic Weierstrass polynomial `h(w, t) = t^m + ∑ a_i(w) t^i` (coefficients analytic,
`a_i(0) = 0`, so all roots cluster at `t = 0` on the section) whose **discriminant `F = disc(h)`
(i) does not vanish identically** (`order F 0 ≠ ⊤`) and **(ii) has constant vanishing order along the
section** `T = ℂˢ × {0}` near `0`, the roots of `h` over `T` are a **single** holomorphic section
`ψ : ℂˢ → ℂ` — the *unique distinct root* (nonsplitting) — of multiplicity `m`:

`h((y,0), α) = 0  ⟺  α = ψ(y)`  for `y, α` near `0`, with `rootMultiplicity (ψ y) = m`.

Both hypotheses match 4.1.1: `F ≢ 0` is "F does not vanish identically" (satisfied in the application
because `h` is squarefree, from squarefree `f`); constant order along `T` is the output of the
(ambient) order-additivity / `DiscOrder` step. The single-`ψ` conclusion is 4.1.1's nonsplitting; the
multiplicity `m` is its order-invariance of `h` along the graph of `ψ`. This is the single deepest
ingredient (Chapter 4 / Puiseux–Newton–monodromy); nothing of it is in Mathlib. -/
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
