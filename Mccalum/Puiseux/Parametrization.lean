import Mccalum.Generalized.Monodromy
import Mccalum.Puiseux.Covering
import Mccalum.Puiseux.RootCover
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Lemma 4.2.6 (Newton–Puiseux parametrization) — the `s = 0` (classical) case

For an irreducible univariate Weierstrass family `q` of degree `m` (the codimension-one, no-section
case), the roots of `q` over the punctured transverse disc are parametrized by `w = uᵐ`, `t = φ(u)`
for a single holomorphic `φ`. The construction (the convergent/covering route, C1–C4 of the
Newton–Puiseux sub-project):

* **universal cover**: the punctured disc `Δ* = {0 < |w| < e^c}` has the half-plane `H = {Re τ < c}`
  as universal cover via `w = exp τ`; `H` is convex, hence contractible and simply connected;
* **lift**: pulling the root cover back along `exp : H → Δ*` (a map from a simply-connected space)
  yields, by `IsCoveringMap.existsUnique_continuousMap_lifts`, a continuous — then analytic — root
  section `ρ : H → ℂ`, `(q (exp τ)).eval (ρ τ) = 0`;
* **period**: the connected `m`-sheeted cover has single-`m`-cycle monodromy, so `ρ(τ + 2πi·m) = ρ τ`;
* **descent**: `φ(u) := ρ (m · log u)` is single-valued (the period), `w = uᵐ`, analytic, and bounded,
  hence extends across `u = 0` (removable singularity).

This file is **work in progress** (not yet wired into the main build). It begins with the
universal-cover domain and the analytic root lift — the validation that the C1 ↔ `rootCover` ↔ C4.3
interfaces compose.
-/

noncomputable section

open Filter Topology Complex Polynomial
open scoped Real

namespace Puiseux

/-! ### Lift uniqueness and periodicity (the covering-theoretic core of the period) -/

section Lift

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
  [SimplyConnectedSpace A] [LocPathConnectedSpace A] {p : E → X}

/-- **Lift uniqueness.** Two continuous lifts of the same map over a simply-connected (and
locally-path-connected) domain that agree at one point are equal. -/
theorem lift_unique (cov : IsCoveringMap p) {F G : C(A, E)}
    (hFG : (p ∘ F : A → X) = (p ∘ G : A → X)) (a₀ : A) (h : F a₀ = G a₀) : F = G := by
  have hcont : Continuous (p ∘ (G : A → E)) := cov.continuous.comp G.continuous
  obtain ⟨_, _, huniq⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨p ∘ (G : A → E), hcont⟩ a₀ (G a₀) rfl
  rw [huniq F ⟨h, hFG⟩, huniq G ⟨rfl, rfl⟩]

/-- **Periodicity propagation.** If `F` lifts `f`, the shift `s` preserves `f` (`f ∘ s = f`), and the
lift is fixed by `s` at one point, then it is fixed everywhere: `F (s a) = F a` for all `a`. -/
theorem lift_periodic (cov : IsCoveringMap p) {F : C(A, E)} {f : C(A, X)}
    (hF : (p ∘ F : A → X) = f) (s : C(A, A)) (hs : (f ∘ s : A → X) = f)
    (a₀ : A) (h0 : F (s a₀) = F a₀) : ∀ a, F (s a) = F a := by
  have key : F.comp s = F := by
    refine lift_unique cov ?_ a₀ h0
    funext a
    show p (F (s a)) = p (F a)
    calc p (F (s a)) = f (s a) := congrFun hF (s a)
      _ = f a := congrFun hs a
      _ = p (F a) := (congrFun hF a).symm
  intro a
  exact DFunLike.congr_fun key a

end Lift

/-- The open left half-plane `{τ : Re τ < c}` — the universal cover of the punctured disc of radius
`e^c` via `w = exp τ`. -/
def halfPlane (c : ℝ) : Set ℂ := {τ : ℂ | τ.re < c}

lemma isOpen_halfPlane (c : ℝ) : IsOpen (halfPlane c) :=
  isOpen_lt (by fun_prop) continuous_const

lemma convex_halfPlane (c : ℝ) : Convex ℝ (halfPlane c) := by
  refine fun x hx y hy s t hs ht hst => ?_
  simp only [halfPlane, Set.mem_setOf_eq] at hx hy ⊢
  have hre : (s • x + t • y).re = s * x.re + t * y.re := by
    simp [Complex.add_re, Complex.real_smul]
  rw [hre]
  rcases lt_or_eq_of_le hs with hs0 | hs0
  · have h1 : s * x.re < s * c := by nlinarith
    have h2 : t * y.re ≤ t * c := by nlinarith
    have hsum : s * x.re + t * y.re < s * c + t * c := by linarith
    rwa [← add_mul, hst, one_mul] at hsum
  · have ht1 : t = 1 := by rw [← hs0] at hst; linarith
    rw [← hs0, ht1, zero_mul, one_mul, zero_add]; exact hy

lemma halfPlane_nonempty (c : ℝ) : (halfPlane c).Nonempty :=
  ⟨((c - 1 : ℝ) : ℂ), by
    simp only [halfPlane, Set.mem_setOf_eq, Complex.ofReal_re]; linarith⟩

instance instLocPathConnected_halfPlane (c : ℝ) :
    LocPathConnectedSpace (halfPlane c) :=
  (isOpen_halfPlane c).locPathConnectedSpace

instance instContractible_halfPlane (c : ℝ) : ContractibleSpace (halfPlane c) :=
  (convex_halfPlane c).contractibleSpace (halfPlane_nonempty c)

instance instSimplyConnected_halfPlane (c : ℝ) : SimplyConnectedSpace (halfPlane c) :=
  SimplyConnectedSpace.ofContractible _

/-- The shift `τ ↦ τ + T` on the half-plane, for an imaginary period `T` (so it preserves `Re`). -/
def shiftHP {c : ℝ} (T : ℂ) (hT : T.re = 0) : C(↥(halfPlane c), ↥(halfPlane c)) where
  toFun τ := ⟨τ.val + T, by
    show (τ.val + T).re < c
    rw [Complex.add_re, hT, add_zero]; exact τ.property⟩
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _

@[simp] lemma shiftHP_apply {c : ℝ} (T : ℂ) (hT : T.re = 0) (τ : ↥(halfPlane c)) :
    (shiftHP T hT τ : ℂ) = τ.val + T := rfl

/-- `exp` maps the half-plane `{Re τ < c}` into the punctured disc `{0 < |w| < e^c}`. -/
lemma exp_mem_punctured_disc {c : ℝ} {τ : ℂ} (hτ : τ ∈ halfPlane c) :
    Complex.exp τ ≠ 0 ∧ ‖Complex.exp τ‖ < Real.exp c := by
  have hτ' : τ.re < c := hτ
  refine ⟨Complex.exp_ne_zero τ, ?_⟩
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.mpr hτ'

/-- The base point `w = exp τ` of the transverse disc, as an element of `Fin 1 → ℂ`. -/
def ptOf (τ : ℂ) : Fin 1 → ℂ := fun _ => Complex.exp τ

lemma norm_ptOf (τ : ℂ) : ‖ptOf τ‖ = ‖Complex.exp τ‖ :=
  pi_norm_const (Complex.exp τ)

lemma continuous_ptOf : Continuous ptOf := by
  unfold ptOf; fun_prop

lemma analyticAt_ptOf (τ : ℂ) : AnalyticAt ℂ ptOf τ := by
  rw [analyticAt_pi_iff]
  intro _
  show AnalyticAt ℂ (fun s => Complex.exp s) τ
  exact analyticAt_cexp

lemma norm_fin_one (x : Fin 1 → ℂ) : ‖x‖ = ‖x 0‖ :=
  le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => le_of_eq (by rw [Subsingleton.elim i 0]))) (norm_le_pi_norm x 0)

/-- `Fin 1 → ℂ` points are determined by their single coordinate. -/
lemma fin_one_ext {x y : Fin 1 → ℂ} (h : x 0 = y 0) : x = y :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

/-- **Orbit covers the fibre (transitivity, the disc analogue of `exp_lift_covers_fiber`).** For a
covering `p : E → ↥U` with path-connected total space and a half-plane lift `F` of `exp`, every point
of the fibre over `p (F a₀)` is `F (a₀ + k·2πi)` for some `k : ℤ`. The base loop lifts through the
*full* `exp : ℂ → ℂ*`, and the lift automatically stays in the half-plane since the base lies in the
disc. -/
theorem halfplane_lift_orbit {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {U : Set (Fin 1 → ℂ)} {c : ℝ} {p : E → ↥U} (cov : IsCoveringMap p)
    (hUdisc : ∀ x : Fin 1 → ℂ, x ∈ U → ‖x‖ < Real.exp c)
    (hUne : ∀ x : Fin 1 → ℂ, x ∈ U → x 0 ≠ 0)
    (F : C(↥(halfPlane c), E))
    (hF : ∀ τ : ↥(halfPlane c), ((p (F τ)).val : Fin 1 → ℂ) = ptOf τ.val)
    (a₀ : ↥(halfPlane c)) {e' : E} (he' : p e' = p (F a₀)) :
    ∃ k : ℤ, ∃ h : a₀.val + (k : ℂ) * (2 * (π : ℂ) * Complex.I) ∈ halfPlane c,
      F ⟨a₀.val + (k : ℂ) * (2 * (π : ℂ) * Complex.I), h⟩ = e' := by
  classical
  set baseC : ↥U → {z : ℂ // z ≠ 0} := fun x => ⟨x.val 0, hUne x.val x.property⟩ with hbaseC
  have hbaseC_cont : Continuous baseC :=
    ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
  let δ : Path (F a₀) e' := PathConnectedSpace.somePath (F a₀) e'
  let bℓ : C(unitInterval, ↥U) := (⟨p, cov.continuous⟩ : C(E, ↥U)).comp δ.toContinuousMap
  let ℓ : C(unitInterval, {z : ℂ // z ≠ 0}) := (⟨baseC, hbaseC_cont⟩ : C(↥U, _)).comp bℓ
  have hℓ0 : ℓ 0 = Complex.expNeZero a₀.val := by
    apply Subtype.ext
    show (p (δ 0)).val 0 = Complex.exp a₀.val
    rw [δ.source, hF a₀]; rfl
  let η : C(unitInterval, ℂ) := Complex.isCoveringMap_exp.liftPath ℓ a₀.val hℓ0
  have hη_lifts : Complex.expNeZero ∘ η = ℓ := Complex.isCoveringMap_exp.liftPath_lifts ℓ a₀.val hℓ0
  have hη0 : η 0 = a₀.val := Complex.isCoveringMap_exp.liftPath_zero ℓ a₀.val hℓ0
  have hexp_η : ∀ s, Complex.exp (η s) = (p (δ s)).val 0 := by
    intro s; exact congrArg Subtype.val (congrFun hη_lifts s)
  have hηH : ∀ s, η s ∈ halfPlane c := by
    intro s
    show (η s).re < c
    have hb : ‖Complex.exp (η s)‖ < Real.exp c := by
      rw [hexp_η s, ← norm_fin_one]
      exact hUdisc _ (p (δ s)).property
    rw [Complex.norm_exp] at hb
    exact Real.exp_lt_exp.mp hb
  let ηH : C(unitInterval, ↥(halfPlane c)) := ⟨fun s => ⟨η s, hηH s⟩, η.continuous.subtype_mk _⟩
  -- both `F ∘ ηH` and `δ` lift `bℓ` from `F a₀`, hence are equal
  have hsrc : bℓ 0 = p (F a₀) := by show p (δ 0) = p (F a₀); rw [δ.source]
  have hFη_lifts : (p : E → ↥U) ∘ (F.comp ηH) = bℓ := by
    funext s
    show p (F ⟨η s, hηH s⟩) = p (δ s)
    apply Subtype.ext
    apply fin_one_ext
    rw [hF ⟨η s, hηH s⟩]
    show Complex.exp (η s) = (p (δ s)).val 0
    exact hexp_η s
  have hFη0 : (F.comp ηH) 0 = F a₀ := by
    show F ⟨η 0, hηH 0⟩ = F a₀
    congr 1; exact Subtype.ext hη0
  have heq : F.comp ηH = δ.toContinuousMap := by
    rw [(cov.eq_liftPath_iff' (Γ := F.comp ηH) hsrc).mpr ⟨hFη_lifts, hFη0⟩,
      (cov.eq_liftPath_iff' (Γ := δ.toContinuousMap) hsrc).mpr ⟨rfl, δ.source⟩]
  -- `η 1 = a₀.val + k·2πi`
  have hexp1 : Complex.exp (η 1) = Complex.exp a₀.val := by
    rw [hexp_η 1, δ.target, he']
    exact congrFun (hF a₀) 0
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp
    (show Complex.exp (η 1 - a₀.val) = 1 by
      rw [Complex.exp_sub, hexp1, div_self (Complex.exp_ne_zero _)])
  have hη1_eq : η 1 = a₀.val + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by linear_combination hk
  refine ⟨k, hη1_eq ▸ hηH 1, ?_⟩
  have hsub : (⟨a₀.val + (k : ℂ) * (2 * (π : ℂ) * Complex.I), hη1_eq ▸ hηH 1⟩ : ↥(halfPlane c))
      = ηH 1 := Subtype.ext hη1_eq.symm
  rw [hsub]
  have hc1 : (F.comp ηH) 1 = δ.toContinuousMap 1 := DFunLike.congr_fun heq 1
  exact hc1.trans δ.target

/-- `k · 2πi` is purely imaginary. -/
lemma intMul_two_pi_I_re (k : ℤ) : ((k : ℂ) * (2 * (π : ℂ) * Complex.I)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

lemma natMul_two_pi_I_re (m : ℕ) : ((m : ℂ) * (2 * (π : ℂ) * Complex.I)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- **The `m`-sheet period (disc analogue of `exp_lift_period_card`).** With the orbit covering the
`m`-element fibre, pigeonhole + the period-propagation `lift_periodic` force the period to be exactly
`m`: `F (x + m·2πi) = F x` for all `x` in the half-plane. -/
theorem halfplane_lift_period {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {U : Set (Fin 1 → ℂ)} {c : ℝ} {p : E → ↥U} (cov : IsCoveringMap p)
    (hUdisc : ∀ x : Fin 1 → ℂ, x ∈ U → ‖x‖ < Real.exp c)
    (hUne : ∀ x : Fin 1 → ℂ, x ∈ U → x 0 ≠ 0)
    (F : C(↥(halfPlane c), E))
    (hF : ∀ τ : ↥(halfPlane c), ((p (F τ)).val : Fin 1 → ℂ) = ptOf τ.val)
    (a₀ : ↥(halfPlane c)) (m : ℕ) [Fintype {e // p e = p (F a₀)}]
    (hcard : Fintype.card {e // p e = p (F a₀)} = m)
    (x : ↥(halfPlane c)) :
    ∃ h : x.val + (m : ℂ) * (2 * (π : ℂ) * Complex.I) ∈ halfPlane c,
      F ⟨x.val + (m : ℂ) * (2 * (π : ℂ) * Complex.I), h⟩ = F x := by
  classical
  set T₀ : ℂ := 2 * (π : ℂ) * Complex.I with hT₀
  -- the base map and its shift-invariance
  let f : C(↥(halfPlane c), ↥U) := ⟨fun τ => p (F τ), cov.continuous.comp F.continuous⟩
  have hpF : (p ∘ (F : ↥(halfPlane c) → E) : ↥(halfPlane c) → ↥U) = f := rfl
  have hexpkT : ∀ k : ℤ, Complex.exp ((k : ℂ) * T₀) = 1 :=
    fun k => Complex.exp_int_mul_two_pi_mul_I k
  -- membership of shifted points
  have hmemHP : ∀ (τ : ↥(halfPlane c)) (k : ℤ), τ.val + (k : ℂ) * T₀ ∈ halfPlane c := by
    intro τ k
    show (τ.val + (k : ℂ) * T₀).re < c
    rw [Complex.add_re, hT₀, intMul_two_pi_I_re, add_zero]; exact τ.property
  -- the shifted point and the orbit
  let shiftPt : ℤ → ↥(halfPlane c) := fun k => ⟨a₀.val + (k : ℂ) * T₀, hmemHP a₀ k⟩
  have hbase_inv : ∀ (τ : ↥(halfPlane c)) (k : ℤ),
      p (F ⟨τ.val + (k : ℂ) * T₀, hmemHP τ k⟩) = p (F τ) := by
    intro τ k
    apply Subtype.ext; apply fin_one_ext
    rw [hF ⟨τ.val + (k : ℂ) * T₀, hmemHP τ k⟩, hF τ]
    show Complex.exp (τ.val + (k : ℂ) * T₀) = Complex.exp τ.val
    rw [Complex.exp_add, hexpkT k, mul_one]
  have hmem : ∀ k : ℤ, p (F (shiftPt k)) = p (F a₀) := fun k => hbase_inv a₀ k
  let orbZ : ℤ → {e // p e = p (F a₀)} := fun k => ⟨F (shiftPt k), hmem k⟩
  -- period propagation: a coincidence at gap `d` propagates to all indices
  have key : ∀ d : ℤ, F (shiftPt d) = F a₀ → ∀ k : ℤ, F (shiftPt (k + d)) = F (shiftPt k) := by
    intro d hd
    have hshift_inv : (f ∘ (shiftHP ((d : ℂ) * T₀) (by
        rw [hT₀, intMul_two_pi_I_re])) : ↥(halfPlane c) → ↥U) = f := by
      funext τ
      show p (F ⟨τ.val + (d : ℂ) * T₀, _⟩) = p (F τ)
      exact hbase_inv τ d
    have h0 : F (shiftHP ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) a₀) = F a₀ := by
      show F ⟨a₀.val + (d : ℂ) * T₀, _⟩ = F a₀; exact hd
    have := lift_periodic cov hpF (shiftHP ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]))
      hshift_inv a₀ h0
    intro k
    have hk := this (shiftPt k)
    show F (shiftPt (k + d)) = F (shiftPt k)
    rw [show shiftPt (k + d)
        = shiftHP ((d : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) (shiftPt k) from
        Subtype.ext (show a₀.val + ((k + d : ℤ) : ℂ) * T₀
          = a₀.val + ((k : ℤ) : ℂ) * T₀ + ((d : ℤ) : ℂ) * T₀ by push_cast; ring)]
    exact hk
  -- integer-multiple period
  have keyZ : ∀ d : ℤ, F (shiftPt d) = F a₀ → ∀ (n k : ℤ), orbZ (k + n * d) = orbZ k := by
    intro d hd n
    induction n using Int.induction_on with
    | zero => intro k; simp
    | succ j ih =>
        intro k
        apply Subtype.ext
        show F (shiftPt (k + (j + 1) * d)) = F (shiftPt k)
        have e1 : k + (j + 1) * d = (k + j * d) + d := by ring
        rw [e1, key d hd (k + j * d)]
        exact congrArg Subtype.val (ih k)
    | pred j ih =>
        intro k
        apply Subtype.ext
        show F (shiftPt (k + (-j - 1) * d)) = F (shiftPt k)
        have e1 : k + (-j - 1) * d = (k + (-(j + 1)) * d) := by ring
        have e2 : (k + (-(j + 1)) * d) + d = k + (-j) * d := by ring
        have := key d hd (k + (-(j + 1)) * d)
        rw [e2] at this
        rw [e1, ← this]
        exact congrArg Subtype.val (ih k)
  -- it suffices to find a period `d` with `1 ≤ d ≤ m`
  suffices hsuff : ∃ d : ℤ, 1 ≤ d ∧ d ≤ (m : ℤ) ∧ F (shiftPt d) = F a₀ by
    obtain ⟨d, hd1, hdm, hd⟩ := hsuff
    have hd0 : (0 : ℤ) < d := by omega
    have hsurj : Function.Surjective (fun a : Fin d.toNat => orbZ (a.val : ℤ)) := by
      intro y
      obtain ⟨k, _, hk⟩ := halfplane_lift_orbit cov hUdisc hUne F hF a₀ y.2
      have hyk : y = orbZ k := Subtype.ext hk.symm
      have hk0nonneg : 0 ≤ k % d := Int.emod_nonneg k hd0.ne'
      have hk0lt : k % d < d := Int.emod_lt_of_pos k hd0
      have hsplit : k = (k % d) + (k / d) * d := by
        have h := Int.emod_add_mul_ediv k d
        rw [mul_comm (k / d) d]; omega
      have hkk0 : orbZ k = orbZ (k % d) := by
        conv_lhs => rw [hsplit]
        exact keyZ d hd (k / d) (k % d)
      refine ⟨⟨(k % d).toNat, by omega⟩, ?_⟩
      show orbZ (((k % d).toNat : ℤ)) = y
      rw [Int.toNat_of_nonneg hk0nonneg, ← hkk0, ← hyk]
    have hcard_le := Fintype.card_le_of_surjective _ hsurj
    rw [Fintype.card_fin, hcard] at hcard_le
    have hdeq : d = (m : ℤ) := by omega
    have hmemM : ∀ τ : ↥(halfPlane c), τ.val + (m : ℂ) * T₀ ∈ halfPlane c := by
      intro τ; show (τ.val + (m : ℂ) * T₀).re < c
      rw [Complex.add_re, hT₀, natMul_two_pi_I_re, add_zero]; exact τ.property
    have hexpM : Complex.exp ((m : ℂ) * T₀) = 1 := by
      rw [hT₀, show (m : ℂ) = ((m : ℤ) : ℂ) from (Int.cast_natCast m).symm]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have hbaseM : ∀ τ : ↥(halfPlane c), p (F ⟨τ.val + (m : ℂ) * T₀, hmemM τ⟩) = p (F τ) := by
      intro τ
      apply Subtype.ext; apply fin_one_ext
      rw [hF ⟨τ.val + (m : ℂ) * T₀, hmemM τ⟩, hF τ]
      show Complex.exp (τ.val + (m : ℂ) * T₀) = Complex.exp τ.val
      rw [Complex.exp_add, hexpM, mul_one]
    refine ⟨hmemM x, ?_⟩
    set sm : C(↥(halfPlane c), ↥(halfPlane c)) :=
      shiftHP ((m : ℂ) * T₀) (by rw [hT₀]; exact natMul_two_pi_I_re m) with hsm
    have hshift_inv : (f ∘ sm : ↥(halfPlane c) → ↥U) = f := by funext τ; exact hbaseM τ
    have h0 : F (sm a₀) = F a₀ := by
      show F ⟨a₀.val + (m : ℂ) * T₀, _⟩ = F a₀
      have hd' : F (shiftPt d) = F a₀ := hd
      rwa [show shiftPt d = (⟨a₀.val + (m : ℂ) * T₀, hmemM a₀⟩ : ↥(halfPlane c)) from
        Subtype.ext (show a₀.val + (d : ℂ) * T₀ = a₀.val + (m : ℂ) * T₀ by
          rw [hdeq]; push_cast; ring)] at hd'
    exact lift_periodic cov hpF sm hshift_inv a₀ h0 x
  -- pigeonhole on `m+1` orbit points
  obtain ⟨i, j, hij, heqij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (m + 1) => orbZ ((i : ℕ) : ℤ))
    (by rw [Fintype.card_fin, hcard]; exact Nat.lt_succ_self _)
  have hi := i.isLt
  have hj := j.isLt
  have hijval : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
  have hkey : ∀ a b : ℤ, a < b → orbZ a = orbZ b → F (shiftPt (b - a)) = F a₀ := by
    intro a b hab horb
    have hva : F (shiftPt a) = F (shiftPt b) := congrArg Subtype.val horb
    set s := shiftHP ((↑(b - a) : ℂ) * T₀) (by rw [hT₀, intMul_two_pi_I_re]) with hs
    have hshift_inv : (f ∘ s : ↥(halfPlane c) → ↥U) = f := by
      funext τ
      show p (F ⟨τ.val + (↑(b - a) : ℂ) * T₀, _⟩) = p (F τ)
      exact hbase_inv τ (b - a)
    have hanchor : F (s (shiftPt a)) = F (shiftPt a) := by
      show F ⟨(shiftPt a).val + (↑(b - a) : ℂ) * T₀, _⟩ = F (shiftPt a)
      rw [show (⟨(shiftPt a).val + ((b - a : ℤ) : ℂ) * T₀,
          hmemHP (shiftPt a) (b - a)⟩ : ↥(halfPlane c)) = shiftPt b from
        Subtype.ext (show a₀.val + ((a : ℤ) : ℂ) * T₀ + ((b - a : ℤ) : ℂ) * T₀
          = a₀.val + ((b : ℤ) : ℂ) * T₀ by push_cast; ring)]
      exact hva.symm
    have hall := lift_periodic cov hpF s hshift_inv (shiftPt a) hanchor a₀
    exact hall
  rcases lt_or_gt_of_ne hijval with hlt | hgt
  · exact ⟨(j : ℕ) - (i : ℕ), by omega, by omega,
      hkey _ _ (by exact_mod_cast hlt) heqij⟩
  · exact ⟨(i : ℕ) - (j : ℕ), by omega, by omega,
      hkey _ _ (by exact_mod_cast hgt) heqij.symm⟩

/-- **A continuous root of an analytic separable family is analytic.** If `ρ` is a continuous root
section `(q (g τ)).eval (ρ τ) = 0` of a monic analytic family with `g` analytic and `q (g τ₁)`
separable, then `ρ` is analytic at `τ₁` (it locally coincides with one of the analytic root sections,
by continuity + the separation of distinct roots). -/
theorem analyticAt_continuous_root {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {g : W → Fin n → ℂ} {ρ : W → ℂ} {τ₁ : W}
    (hg : AnalyticAt ℂ g τ₁)
    (hcoeff : ∀ i, AnalyticAt ℂ (fun z => (q z).coeff i) (g τ₁))
    (hsep : (q (g τ₁)).Separable)
    (hρc : ContinuousAt ρ τ₁)
    (hρr : ∀ᶠ τ in 𝓝 τ₁, (q (g τ)).eval (ρ τ) = 0) :
    AnalyticAt ℂ ρ τ₁ := by
  classical
  obtain ⟨V, φ, hVopen, hgτ₁V, _, _, hφan, hφinj, hφroots⟩ :=
    exists_local_root_sections q hmonic hdeg hcoeff hsep Set.univ isOpen_univ (Set.mem_univ _)
  have hgcont : ContinuousAt g τ₁ := hg.continuousAt
  have hgV : ∀ᶠ τ in 𝓝 τ₁, g τ ∈ V := hgcont (hVopen.mem_nhds hgτ₁V)
  have hφcat : ∀ i, ContinuousAt (fun τ => φ i (g τ)) τ₁ := fun i =>
    (((hφan i).analyticAt (hVopen.mem_nhds hgτ₁V)).continuousAt).comp hgcont
  -- `ρ τ₁` is a root, so `= φ i₀ (g τ₁)` for some `i₀`
  have hρ₁_root : (q (g τ₁)).eval (ρ τ₁) = 0 := hρr.self_of_nhds
  have hρ₁_mem : ρ τ₁ ∈ (q (g τ₁)).roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots').mpr ⟨(hmonic (g τ₁)).ne_zero, hρ₁_root⟩
  rw [hφroots (g τ₁) hgτ₁V, Finset.mem_image] at hρ₁_mem
  obtain ⟨i₀, _, hi₀⟩ := hρ₁_mem
  -- near `τ₁`, `ρ` coincides with `φ i₀ ∘ g`
  have hsep_ev : ∀ᶠ τ in 𝓝 τ₁, ρ τ = φ i₀ (g τ) := by
    have hclose : ∀ᶠ τ in 𝓝 τ₁,
        ∀ i, i ≠ i₀ → ‖ρ τ - φ i₀ (g τ)‖ < ‖φ i (g τ) - φ i₀ (g τ)‖ := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_imp_distrib_left]
      intro hi
      have hlhs : Tendsto (fun τ => ‖ρ τ - φ i₀ (g τ)‖) (𝓝 τ₁) (𝓝 0) := by
        have hd : Tendsto (fun τ => ρ τ - φ i₀ (g τ)) (𝓝 τ₁) (𝓝 (ρ τ₁ - φ i₀ (g τ₁))) :=
          hρc.sub (hφcat i₀)
        rw [hi₀, sub_self] at hd
        simpa using (continuous_norm.tendsto (0 : ℂ)).comp hd
      have hrhs : Tendsto (fun τ => ‖φ i (g τ) - φ i₀ (g τ)‖) (𝓝 τ₁)
          (𝓝 ‖φ i (g τ₁) - φ i₀ (g τ₁)‖) :=
        (continuous_norm.continuousAt).comp ((hφcat i).sub (hφcat i₀))
      have hpos : 0 < ‖φ i (g τ₁) - φ i₀ (g τ₁)‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun h => hi (hφinj (g τ₁) hgτ₁V h)
      exact hlhs.eventually_lt hrhs hpos
    filter_upwards [hclose, hgV, hρr] with τ hτ hτV hτroot
    -- `ρ τ` is a root, = `φ j (g τ)` for some `j`; `hτ` forces `j = i₀`
    have hmem : ρ τ ∈ (q (g τ)).roots.toFinset := by
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots').mpr ⟨(hmonic (g τ)).ne_zero, hτroot⟩
    rw [hφroots (g τ) hτV, Finset.mem_image] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    by_cases hji : j = i₀
    · rw [← hj, hji]
    · exfalso
      have hcontra := hτ j hji
      rw [← hj] at hcontra
      exact lt_irrefl _ hcontra
  have hsep_ev' : ρ =ᶠ[𝓝 τ₁] fun τ => φ i₀ (g τ) := hsep_ev
  exact (((hφan i₀).analyticAt (hVopen.mem_nhds hgτ₁V)).comp hg).congr hsep_ev'.symm

/-- A local analytic branch of `log` near any `u₀ ≠ 0` (principal `log` on the slit plane, a rotated
branch on the negative axis). -/
lemma exists_local_log_branch {u₀ : ℂ} (hu₀ : u₀ ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L u₀ ∧ (∀ᶠ u in 𝓝 u₀, Complex.exp (L u) = u) := by
  by_cases hs : u₀ ∈ Complex.slitPlane
  · exact ⟨Complex.log, analyticAt_clog hs,
      by filter_upwards [isOpen_ne.mem_nhds hu₀] with u hu using Complex.exp_log hu⟩
  · have hu₀re : u₀.re < 0 := by
      rw [Complex.mem_slitPlane_iff, not_or, not_lt] at hs
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (h.trans Complex.zero_re.symm)
          ((not_not.mp hs.2).trans Complex.zero_im.symm)) hu₀
    have hneg : -u₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl (by rw [Complex.neg_re]; linarith)
    refine ⟨fun u => Complex.log (-u) + ↑π * Complex.I,
      ((analyticAt_clog hneg).comp analyticAt_id.neg).add analyticAt_const, ?_⟩
    filter_upwards [isOpen_ne.mem_nhds hu₀] with u hu
    show Complex.exp (Complex.log (-u) + ↑π * Complex.I) = u
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hu), Complex.exp_pi_mul_I]
    ring

/-- The fibre of the root cover over a base point `b = rootProj e₀` is in bijection with the roots of
`q b` (each root `t` gives the variety point `(b, t)`, and conversely). -/
def rootCover_fiberEquiv {N : ℕ} (q : (Fin N → ℂ) → Polynomial ℂ)
    {U : Set (Fin N → ℂ)} (e₀ : ↥(rootProj q ⁻¹' U)) (hq : q (e₀.val.val.1) ≠ 0) :
    {e // U.restrictPreimage (rootProj q) e = U.restrictPreimage (rootProj q) e₀}
      ≃ ↥((q (e₀.val.val.1)).roots.toFinset) where
  toFun e := ⟨e.val.val.val.2, by
    rw [Multiset.mem_toFinset]
    have hbase : e.val.val.val.1 = e₀.val.val.1 :=
      congrArg Subtype.val e.property
    have hr : (q e.val.val.val.1).eval e.val.val.val.2 = 0 := e.val.val.property
    rw [hbase] at hr
    exact (Polynomial.mem_roots').mpr ⟨hq, hr⟩⟩
  invFun t := ⟨⟨⟨(e₀.val.val.1, t.val),
      (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp t.property)).2⟩, e₀.property⟩,
    Subtype.ext rfl⟩
  left_inv e := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    have hbase : e.val.val.val.1 = e₀.val.val.1 := congrArg Subtype.val e.property
    show (e₀.val.val.1, e.val.val.val.2) = e.val.val.val
    rw [← hbase]
  right_inv t := by apply Subtype.ext; rfl

/-- **The analytic root lift over the universal cover (Lemma 4.2.6, step 1).** For an irreducible
univariate Weierstrass family `q` separable on the punctured disc of radius `δ`, the root cover lifts
along `exp : H → Δ*` (from the simply-connected half-plane `H = {Re τ < log δ}`) to a *continuous* root
section `ρ : H → ℂ` with `(q (exp τ)).eval (ρ τ) = 0`, normalized to `ρ τ₀ = t₀`. -/
theorem exists_root_lift (q : (Fin 1 → ℂ) → Polynomial ℂ) (m : ℕ)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x : Fin 1 → ℂ, 0 < ‖x‖ → ‖x‖ < δ → (q x).Separable)
    (hpc : PathConnectedSpace ↥(rootProj q ⁻¹' {x : Fin 1 → ℂ | 0 < ‖x‖ ∧ ‖x‖ < δ}))
    {τ₀ : ℂ} (hτ₀ : τ₀ ∈ halfPlane (Real.log δ))
    {t₀ : ℂ} (ht₀ : (q (ptOf τ₀)).eval t₀ = 0) :
    ∃ ρ : ℂ → ℂ, ρ τ₀ = t₀ ∧
      ContinuousOn ρ (halfPlane (Real.log δ)) ∧
      (∀ τ ∈ halfPlane (Real.log δ), (q (ptOf τ)).eval (ρ τ) = 0) ∧
      (∀ τ ∈ halfPlane (Real.log δ), AnalyticAt ℂ ρ τ) ∧
      (∀ τ ∈ halfPlane (Real.log δ),
        ρ (τ + (m : ℂ) * (2 * (π : ℂ) * Complex.I)) = ρ τ) ∧
      (∀ τ ∈ halfPlane (Real.log δ), ∀ t : ℂ, (q (ptOf τ)).eval t = 0 →
        ∃ τ' ∈ halfPlane (Real.log δ), Complex.exp τ' = Complex.exp τ ∧ ρ τ' = t) := by
  classical
  set c := Real.log δ with hc
  set U : Set (Fin 1 → ℂ) := {x | 0 < ‖x‖ ∧ ‖x‖ < δ} with hU
  haveI : PathConnectedSpace ↥(rootProj q ⁻¹' U) := hpc
  -- `exp τ ∈ U` for `τ ∈ H`
  have hmem : ∀ τ : ℂ, τ ∈ halfPlane c → ptOf τ ∈ U := by
    intro τ hτ
    refine ⟨?_, ?_⟩
    · rw [norm_ptOf]; exact norm_pos_iff.mpr (Complex.exp_ne_zero τ)
    · rw [norm_ptOf, Complex.norm_exp]
      calc Real.exp τ.re < Real.exp c := Real.exp_lt_exp.mpr hτ
        _ = δ := by rw [hc]; exact Real.exp_log hδ
  have hUsep : ∀ y ∈ U, (q y).Separable := fun y hy => hsep y hy.1 hy.2
  have cov : IsCoveringMap (U.restrictPreimage (rootProj q)) :=
    rootCover_isCoveringMap q hmonic hdeg hcoeff hUsep
  -- the base map `f : H → ↥U`, `τ ↦ exp τ`
  let f : C(↥(halfPlane c), ↥U) :=
    ⟨fun τ => ⟨ptOf τ.val, hmem τ.val τ.property⟩,
      (continuous_ptOf.comp continuous_subtype_val).subtype_mk _⟩
  -- the base point and a chosen root over it
  let a₀ : ↥(halfPlane c) := ⟨τ₀, hτ₀⟩
  let e₀ : ↥(rootProj q ⁻¹' U) :=
    ⟨⟨(ptOf τ₀, t₀), ht₀⟩, hmem τ₀ hτ₀⟩
  have he : (U.restrictPreimage (rootProj q)) e₀ = f a₀ := rfl
  -- lift
  obtain ⟨F, ⟨hF0, hFlift⟩, _⟩ := cov.existsUnique_continuousMap_lifts f a₀ e₀ he
  -- the root section, extended by `0` off `H`
  set ρ : ℂ → ℂ := fun τ => if h : τ ∈ halfPlane c then ((F ⟨τ, h⟩).val.val.2) else 0 with hρdef
  have hval : ρ τ₀ = t₀ := by
    show (if h : τ₀ ∈ halfPlane c then ((F ⟨τ₀, h⟩).val.val.2) else 0) = t₀
    rw [dif_pos hτ₀]; show (F a₀).val.val.2 = t₀; rw [hF0]
  have hcont : ContinuousOn ρ (halfPlane c) := by
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.congr (f := fun τ : ↥(halfPlane c) => ((F τ).val.val.2)) ?_ ?_
    · exact continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp F.continuous))
    · intro τ
      rw [Set.restrict_apply]
      show (F τ).val.val.2 = if h : (τ : ℂ) ∈ halfPlane c then ((F ⟨τ.val, h⟩).val.val.2) else 0
      rw [dif_pos τ.property]
  have hroot : ∀ τ ∈ halfPlane c, (q (ptOf τ)).eval (ρ τ) = 0 := by
    intro τ hτ
    show (q (ptOf τ)).eval (if h : τ ∈ halfPlane c then ((F ⟨τ, h⟩).val.val.2) else 0) = 0
    rw [dif_pos hτ]
    have hbase : (F ⟨τ, hτ⟩).val.val.1 = ptOf τ :=
      congrArg Subtype.val (congrFun hFlift ⟨τ, hτ⟩)
    have hr : (q (F ⟨τ, hτ⟩).val.val.1).eval (F ⟨τ, hτ⟩).val.val.2 = 0 :=
      (F ⟨τ, hτ⟩).val.property
    rw [hbase] at hr; exact hr
  have hF_lift : ∀ τ : ↥(halfPlane c),
      ((U.restrictPreimage (rootProj q) (F τ)).val : Fin 1 → ℂ) = ptOf τ.val :=
    fun τ => congrArg Subtype.val (congrFun hFlift τ)
  have hUdisc : ∀ x : Fin 1 → ℂ, x ∈ U → ‖x‖ < Real.exp c := by
    intro x hx; rw [hc, Real.exp_log hδ]; exact hx.2
  have hUne : ∀ x : Fin 1 → ℂ, x ∈ U → x 0 ≠ 0 := by
    intro x hx; rw [← norm_pos_iff, ← norm_fin_one]; exact hx.1
  refine ⟨ρ, hval, hcont, hroot, ?_, ?_, ?_⟩
  · -- analyticity via `analyticAt_continuous_root`
    intro τ₁ hτ₁
    refine analyticAt_continuous_root q m hmonic hdeg (analyticAt_ptOf τ₁) (fun i => hcoeff i _)
      (hsep (ptOf τ₁) (hmem τ₁ hτ₁).1 (hmem τ₁ hτ₁).2)
      (hcont.continuousAt ((isOpen_halfPlane c).mem_nhds hτ₁)) ?_
    filter_upwards [(isOpen_halfPlane c).mem_nhds hτ₁] with τ hτ
    exact hroot τ hτ
  · -- periodicity via `halfplane_lift_period`
    have hbU : (F a₀).val.val.1 ∈ U := (F a₀).property
    haveI : Fintype {e // U.restrictPreimage (rootProj q) e
        = U.restrictPreimage (rootProj q) (F a₀)} :=
      Fintype.ofEquiv _ (rootCover_fiberEquiv q (F a₀) (hmonic _).ne_zero).symm
    have hcardm : Fintype.card {e // U.restrictPreimage (rootProj q) e
        = U.restrictPreimage (rootProj q) (F a₀)} = m := by
      rw [Fintype.card_congr (rootCover_fiberEquiv q (F a₀) (hmonic _).ne_zero), Fintype.card_coe,
        Multiset.toFinset_card_of_nodup (nodup_roots (hUsep _ hbU)),
        splits_iff_card_roots.mp (IsAlgClosed.splits _), hdeg _]
    intro τ hτ
    obtain ⟨hmemτ, hper⟩ := halfplane_lift_period cov hUdisc hUne F hF_lift a₀ m hcardm ⟨τ, hτ⟩
    simp only [hρdef]
    rw [dif_pos hmemτ, dif_pos hτ, hper]
  · -- surjectivity onto the fibre via `halfplane_lift_orbit`
    intro τ hτ t hroott
    have he' : U.restrictPreimage (rootProj q) (⟨⟨(ptOf τ, t), hroott⟩, hmem τ hτ⟩ :
        ↥(rootProj q ⁻¹' U)) = U.restrictPreimage (rootProj q) (F ⟨τ, hτ⟩) :=
      Subtype.ext (hF_lift ⟨τ, hτ⟩).symm
    obtain ⟨k, hk_mem, hk_eq⟩ := halfplane_lift_orbit cov hUdisc hUne F hF_lift ⟨τ, hτ⟩ he'
    refine ⟨τ + (k : ℂ) * (2 * (π : ℂ) * Complex.I), hk_mem, ?_, ?_⟩
    · rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · simp only [hρdef]
      rw [dif_pos hk_mem, hk_eq]

/-- **Descent (Lemma 4.2.6, step 3).** The period makes `φ(u) := ρ(m·log u)` single-valued and
analytic on the punctured disc `0 < ‖u‖`, `‖u‖ᵐ < δ`, satisfying `(q uᵐ).eval (φ u) = 0`. The log
branch cut is invisible because the jump `±2πi` in `log` is a period of `ρ`. -/
theorem descend_phi {ρ : ℂ → ℂ} {δ : ℝ} {m : ℕ} (hm : 0 < m)
    {q : (Fin 1 → ℂ) → Polynomial ℂ}
    (hρ_root : ∀ τ ∈ halfPlane (Real.log δ), (q (ptOf τ)).eval (ρ τ) = 0)
    (hρ_an : ∀ τ ∈ halfPlane (Real.log δ), AnalyticAt ℂ ρ τ)
    (hρ_period : ∀ τ ∈ halfPlane (Real.log δ),
      ρ (τ + (m : ℂ) * (2 * (π : ℂ) * Complex.I)) = ρ τ)
    (hρ_surj : ∀ τ ∈ halfPlane (Real.log δ), ∀ t : ℂ, (q (ptOf τ)).eval t = 0 →
      ∃ τ' ∈ halfPlane (Real.log δ), Complex.exp τ' = Complex.exp τ ∧ ρ τ' = t) :
    ∃ φ : ℂ → ℂ,
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → (q (fun _ => u ^ m)).eval (φ u) = 0) ∧
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → AnalyticAt ℂ φ u) ∧
      (∀ u t : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ →
        ((q (fun _ => u ^ m)).eval t = 0 ↔ ∃ u' : ℂ, u' ^ m = u ^ m ∧ φ u' = t)) := by
  set c := Real.log δ with hc
  set T₀ : ℂ := (m : ℂ) * (2 * (π : ℂ) * Complex.I) with hT₀
  have hT₀re : T₀.re = 0 := by rw [hT₀]; exact natMul_two_pi_I_re m
  have hshiftmem : ∀ (j : ℤ) (τ : ℂ), τ ∈ halfPlane c → τ + (j : ℂ) * T₀ ∈ halfPlane c := by
    intro j τ hτ
    show (τ + (j : ℂ) * T₀).re < c
    rw [Complex.add_re, Complex.mul_re, hT₀re, Complex.intCast_im]
    simpa using hτ
  have hmemτ : ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → (m : ℂ) * Complex.log u ∈ halfPlane c := by
    intro u hu hud
    show ((m : ℂ) * Complex.log u).re < c
    rw [Complex.mul_re, Complex.log_re, Complex.natCast_im, Complex.natCast_re, hc, ← Real.log_pow]
    simpa using Real.log_lt_log (by positivity) hud
  -- ℤ-multiple period
  have hperiodZ : ∀ (k : ℤ) (τ : ℂ), τ ∈ halfPlane c → ρ (τ + (k : ℂ) * T₀) = ρ τ := by
    intro k
    induction k using Int.induction_on with
    | zero => intro τ _; simp
    | succ j ih =>
        intro τ hτ
        have e : τ + (((j : ℤ) + 1 : ℤ) : ℂ) * T₀ = (τ + ((j : ℤ) : ℂ) * T₀) + T₀ := by
          push_cast; ring
        rw [e, hρ_period _ (hshiftmem (j : ℤ) τ hτ), ih τ hτ]
    | pred j ih =>
        intro τ hτ
        have hp := hρ_period _ (hshiftmem (-(j : ℤ) - 1) τ hτ)
        rw [show (τ + ((-(j : ℤ) - 1 : ℤ) : ℂ) * T₀) + T₀ = τ + ((-(j : ℤ) : ℤ) : ℂ) * T₀ from
          by push_cast; ring] at hp
        rw [← hp, ih τ hτ]
  refine ⟨fun u => ρ ((m : ℂ) * Complex.log u), ?_, ?_, ?_⟩
  · -- root equation
    intro u hu hud
    have hr := hρ_root _ (hmemτ u hu hud)
    rwa [show ptOf ((m : ℂ) * Complex.log u) = (fun _ => u ^ m) from by
      funext _
      show Complex.exp ((m : ℂ) * Complex.log u) = u ^ m
      rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu)]] at hr
  · -- analyticity, branch-cut-invisible via the period
    intro u₀ hu₀ hud₀
    obtain ⟨L, hL_an, hL_exp⟩ := exists_local_log_branch (norm_pos_iff.mp hu₀)
    have hexp0 : Complex.exp (L u₀) = u₀ := hL_exp.self_of_nhds
    have hLre : (L u₀).re = Real.log ‖u₀‖ := by
      have hh : Real.exp (L u₀).re = ‖u₀‖ := by rw [← Complex.norm_exp, hexp0]
      rw [← hh, Real.log_exp]
    have hLmem : (m : ℂ) * L u₀ ∈ halfPlane c := by
      show ((m : ℂ) * L u₀).re < c
      rw [Complex.mul_re, hLre, Complex.natCast_im, Complex.natCast_re, hc, ← Real.log_pow]
      simpa using Real.log_lt_log (by positivity) hud₀
    have hφeq : (fun u => ρ ((m : ℂ) * Complex.log u)) =ᶠ[𝓝 u₀] fun u => ρ ((m : ℂ) * L u) := by
      filter_upwards [hL_exp, isOpen_ne.mem_nhds (norm_pos_iff.mp hu₀),
        (isOpen_lt (continuous_norm.pow m) continuous_const).mem_nhds hud₀] with u hexp hune hud
      have huu : 0 < ‖u‖ := norm_pos_iff.mpr hune
      have hdiff : Complex.exp (L u - Complex.log u) = 1 := by
        rw [Complex.exp_sub, hexp, Complex.exp_log hune, div_self hune]
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hdiff
      have hmL : (m : ℂ) * L u = (m : ℂ) * Complex.log u + (k : ℂ) * T₀ := by
        rw [hT₀]
        have hLu : L u = Complex.log u + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
          linear_combination hk
        rw [hLu]; ring
      show ρ ((m : ℂ) * Complex.log u) = ρ ((m : ℂ) * L u)
      rw [hmL, hperiodZ k _ (hmemτ u huu hud)]
    have hinner : AnalyticAt ℂ (fun u => (m : ℂ) * L u) u₀ := analyticAt_const.mul hL_an
    have hcomp : AnalyticAt ℂ (ρ ∘ fun u => (m : ℂ) * L u) u₀ :=
      AnalyticAt.comp (g := ρ) (f := fun u => (m : ℂ) * L u) (hρ_an _ hLmem) hinner
    exact hcomp.congr hφeq.symm
  · -- the iff: the roots of `q (uᵐ)` are exactly `{φ u' : u'ᵐ = uᵐ}`
    have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    intro u t hu hud
    constructor
    · -- forward: a root is `φ u'` for some `u'` with `u'ᵐ = uᵐ`
      intro hroott
      have hexpu : Complex.exp ((m : ℂ) * Complex.log u) = u ^ m := by
        rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu)]
      have hroot' : (q (ptOf ((m : ℂ) * Complex.log u))).eval t = 0 := by
        rwa [show ptOf ((m : ℂ) * Complex.log u) = (fun _ => u ^ m) from funext fun _ => hexpu]
      obtain ⟨τ', hτ'mem, hexpτ', hρτ'⟩ := hρ_surj _ (hmemτ u hu hud) t hroot'
      refine ⟨Complex.exp (τ' / (m : ℂ)), ?_, ?_⟩
      · have hmul : (m : ℂ) * (τ' / (m : ℂ)) = τ' := by field_simp
        have hpow : (Complex.exp (τ' / (m : ℂ))) ^ m = Complex.exp τ' := by
          rw [← Complex.exp_nat_mul, hmul]
        rw [hpow, hexpτ']; exact hexpu
      · show ρ ((m : ℂ) * Complex.log (Complex.exp (τ' / (m : ℂ)))) = t
        obtain ⟨k₀, hk₀⟩ := Complex.exp_eq_one_iff.mp
          (show Complex.exp (Complex.log (Complex.exp (τ' / (m : ℂ))) - τ' / (m : ℂ)) = 1 by
            rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero _),
              div_self (Complex.exp_ne_zero _)])
        have hml : (m : ℂ) * Complex.log (Complex.exp (τ' / (m : ℂ))) = τ' + (k₀ : ℂ) * T₀ := by
          have hlog : Complex.log (Complex.exp (τ' / (m : ℂ)))
              = τ' / (m : ℂ) + (k₀ : ℂ) * (2 * (π : ℂ) * Complex.I) := by linear_combination hk₀
          rw [hlog, hT₀]; field_simp
        rw [hml, hperiodZ k₀ τ' hτ'mem, hρτ']
    · -- backward: `φ u'` is a root
      rintro ⟨u', hu'm, hφu'⟩
      have h2 : ‖u'‖ ^ m = ‖u‖ ^ m := by rw [← norm_pow, ← norm_pow, hu'm]
      have hu'pos : 0 < ‖u'‖ := by
        have h1 : (0 : ℝ) < ‖u‖ ^ m := pow_pos hu m
        have hne : ‖u'‖ ≠ 0 := fun h => by
          rw [h, zero_pow hm.ne'] at h2; exact absurd h2.symm (ne_of_gt h1)
        exact (norm_nonneg u').lt_of_ne (Ne.symm hne)
      have hr := hρ_root _ (hmemτ u' hu'pos (by rw [h2]; exact hud))
      rw [show ptOf ((m : ℂ) * Complex.log u') = (fun _ => u' ^ m) from funext fun _ => by
        show Complex.exp ((m : ℂ) * Complex.log u') = u' ^ m
        rw [Complex.exp_nat_mul, Complex.exp_log (norm_pos_iff.mp hu'pos)], hu'm] at hr
      have hval : ρ ((m : ℂ) * Complex.log u') = t := hφu'
      rwa [hval] at hr

/-- **Lemma 4.2.6, `s = 0` (modulo removable singularity).** For an irreducible univariate Weierstrass
family `q` of degree `m`, separable on the punctured disc with path-connected root cover, the roots over
the punctured `w`-disc are parametrized by `w = uᵐ`, `t = φ(u)` with `φ` analytic on the punctured
`u`-disc. Combines the analytic lift (`exists_root_lift`) with the descent (`descend_phi`). -/
theorem exists_param_s0 (q : (Fin 1 → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x : Fin 1 → ℂ, 0 < ‖x‖ → ‖x‖ < δ → (q x).Separable)
    (hpc : PathConnectedSpace ↥(rootProj q ⁻¹' {x : Fin 1 → ℂ | 0 < ‖x‖ ∧ ‖x‖ < δ})) :
    ∃ φ : ℂ → ℂ,
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → (q (fun _ => u ^ m)).eval (φ u) = 0) ∧
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → AnalyticAt ℂ φ u) ∧
      (∀ u t : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ →
        ((q (fun _ => u ^ m)).eval t = 0 ↔ ∃ u' : ℂ, u' ^ m = u ^ m ∧ φ u' = t)) := by
  -- a base point `τ₀ ∈ H` and a root `t₀` of `q (exp τ₀)`
  have hτ₀ : ((Real.log δ - 1 : ℝ) : ℂ) ∈ halfPlane (Real.log δ) := by
    show ((Real.log δ - 1 : ℝ) : ℂ).re < Real.log δ
    rw [Complex.ofReal_re]; linarith
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (q (ptOf ((Real.log δ - 1 : ℝ) : ℂ))) (by
    rw [Polynomial.degree_eq_natDegree (hmonic _).ne_zero, hdeg]; exact_mod_cast hm.ne')
  obtain ⟨ρ, _, _, hρ_root, hρ_an, hρ_period, hρ_surj⟩ :=
    exists_root_lift q m hmonic hdeg hcoeff hδ hsep hpc hτ₀ ht₀
  exact descend_phi hm hρ_root hρ_an hρ_period hρ_surj

/-- **Root bound (Lagrange, `Fin n → ℂ` base).** For a monic family with `q 0 = Xᵐ` (so the lower
coefficients vanish at `0`), all roots of `q y` lie within `‖·‖ ≤ R` for `y` near `0`. Discharges the
`hbdd` hypothesis. -/
theorem roots_eventually_bounded {n : ℕ} (q : (Fin n → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, Continuous (fun y => (q y).coeff i)) (hq0 : q 0 = X ^ m)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ R := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := min 1 (R ^ m) / (m + 1) with hδdef
  have hmin_pos : 0 < min 1 (R ^ m) := lt_min one_pos (by positivity)
  have hδpos : 0 < δ := div_pos hmin_pos (by positivity)
  have hδm_lt : δ * (m : ℝ) < min 1 (R ^ m) := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (by linarith) hmin_pos
  have hδm1 : δ * (m : ℝ) < 1 := lt_of_lt_of_le hδm_lt (min_le_left _ _)
  have hδmR : δ * (m : ℝ) < R ^ m := lt_of_lt_of_le hδm_lt (min_le_right _ _)
  have ha0 : ∀ i, i < m → (q 0).coeff i = 0 := fun i hi => by
    rw [hq0, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi)]
  have hev : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ i ∈ Finset.range m, ‖(q y).coeff i‖ ≤ δ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    refine (((hcoeff i).continuousAt.norm).eventually_lt continuousAt_const ?_).mono fun y h => h.le
    rw [ha0 i (Finset.mem_range.mp hi)]; simpa using hδpos
  filter_upwards [hev] with y hy t ht
  have htroot : (q y).eval t = 0 :=
    (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp ht)).2
  have h0 : t ^ m = -∑ i ∈ Finset.range m, (q y).coeff i * t ^ i := by
    have hevr : (q y).eval t = ∑ i ∈ Finset.range (m + 1), (q y).coeff i * t ^ i := by
      rw [Polynomial.eval_eq_sum_range, hdeg y]
    rw [Finset.sum_range_succ,
      show (q y).coeff m = 1 from by rw [← hdeg y]; exact (hmonic y).coeff_natDegree, one_mul,
      htroot] at hevr
    linear_combination -hevr
  have hnorm : ‖t‖ ^ m ≤ δ * ∑ i ∈ Finset.range m, ‖t‖ ^ i := by
    have he : ‖t‖ ^ m = ‖∑ i ∈ Finset.range m, (q y).coeff i * t ^ i‖ := by
      rw [← norm_pow, h0, norm_neg]
    rw [he]
    calc ‖∑ i ∈ Finset.range m, (q y).coeff i * t ^ i‖
        ≤ ∑ i ∈ Finset.range m, ‖(q y).coeff i * t ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range m, ‖(q y).coeff i‖ * ‖t‖ ^ i := by simp only [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range m, δ * ‖t‖ ^ i :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hy i hi) (by positivity)
      _ = δ * ∑ i ∈ Finset.range m, ‖t‖ ^ i := by rw [Finset.mul_sum]
  rcases le_total 1 ‖t‖ with hr1 | hr1
  · exfalso
    have hsum_le : ∑ i ∈ Finset.range m, ‖t‖ ^ i ≤ (m : ℝ) * ‖t‖ ^ (m - 1) := by
      calc ∑ i ∈ Finset.range m, ‖t‖ ^ i
          ≤ ∑ _i ∈ Finset.range m, ‖t‖ ^ (m - 1) :=
            Finset.sum_le_sum fun i hi =>
              pow_le_pow_right₀ hr1 (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
        _ = (m : ℝ) * ‖t‖ ^ (m - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpow_pos : 0 < ‖t‖ ^ (m - 1) := pow_pos (lt_of_lt_of_le one_pos hr1) _
    have hrm_eq : ‖t‖ ^ m = ‖t‖ * ‖t‖ ^ (m - 1) := by
      rw [mul_comm ‖t‖ (‖t‖ ^ (m - 1)), ← pow_succ, Nat.sub_add_cancel hm]
    have hrm : ‖t‖ * ‖t‖ ^ (m - 1) ≤ (δ * (m : ℝ)) * ‖t‖ ^ (m - 1) := by
      rw [← hrm_eq, mul_assoc]
      exact le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    have hr_le : ‖t‖ ≤ δ * (m : ℝ) := le_of_mul_le_mul_right hrm hpow_pos
    linarith
  · have hsum_le : ∑ i ∈ Finset.range m, ‖t‖ ^ i ≤ (m : ℝ) := by
      calc ∑ i ∈ Finset.range m, ‖t‖ ^ i
          ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => pow_le_one₀ (norm_nonneg t) hr1
        _ = (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hrm : ‖t‖ ^ m ≤ δ * (m : ℝ) := le_trans hnorm (mul_le_mul_of_nonneg_left hsum_le hδpos.le)
    exact le_of_lt (lt_of_pow_lt_pow_left₀ m hR.le (lt_of_le_of_lt hrm hδmR))

/-- **Lemma 4.2.6, `s = 0`, with the removable singularity at `u = 0`.** The parametrization `φ` is
bounded near `0` (its values are roots of `q`, which stay bounded), so it extends to a function
analytic on the *full* `u`-disc. -/
theorem exists_param_s0_full (q : (Fin 1 → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x : Fin 1 → ℂ, 0 < ‖x‖ → ‖x‖ < δ → (q x).Separable)
    (hpc : PathConnectedSpace ↥(rootProj q ⁻¹' {x : Fin 1 → ℂ | 0 < ‖x‖ ∧ ‖x‖ < δ}))
    {ε : ℝ} (hbdd : ∀ᶠ y in 𝓝 (0 : Fin 1 → ℂ), ∀ t ∈ (q y).roots.toFinset, ‖t‖ ≤ ε) :
    ∃ φ : ℂ → ℂ,
      (∀ u : ℂ, ‖u‖ ^ m < δ → AnalyticAt ℂ φ u) ∧
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → (q (fun _ => u ^ m)).eval (φ u) = 0) ∧
      (∀ u t : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ →
        ((q (fun _ => u ^ m)).eval t = 0 ↔ ∃ u' : ℂ, u' ^ m = u ^ m ∧ φ u' = t)) := by
  obtain ⟨φ, hφ_root, hφ_an, hφ_iff⟩ := exists_param_s0 q m hm hmonic hdeg hcoeff hδ hsep hpc
  -- the punctured disc is a punctured neighbourhood of `0`
  have hdiscmem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ ^ m < δ :=
    nhdsWithin_le_nhds ((isOpen_lt (continuous_norm.pow m) continuous_const).mem_nhds
      (show ‖(0 : ℂ)‖ ^ m < δ by rw [norm_zero, zero_pow hm.ne']; exact hδ))
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ φ z := by
    filter_upwards [hdiscmem, self_mem_nhdsWithin] with z hz hz0
    exact (hφ_an z (norm_pos_iff.mpr hz0) hz).differentiableAt
  -- boundedness near `0`: `φ z` is a root of `q (z ^ m)`, and roots stay bounded
  have hbz : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖φ z‖ ≤ ε := by
    have hmap : Tendsto (fun z : ℂ => (fun _ : Fin 1 => z ^ m)) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun z : ℂ => (fun _ : Fin 1 => z ^ m)) := by fun_prop
      simpa [zero_pow hm.ne'] using hcont.tendsto 0
    have hbdd' : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        ∀ t ∈ (q (fun _ => z ^ m)).roots.toFinset, ‖t‖ ≤ ε :=
      nhdsWithin_le_nhds (hmap.eventually hbdd)
    filter_upwards [hbdd', hdiscmem, self_mem_nhdsWithin] with z hzbdd hzd hz0
    refine hzbdd (φ z) ?_
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots').mpr ⟨(hmonic _).ne_zero, hφ_root z (norm_pos_iff.mpr hz0) hzd⟩
  -- the removable-singularity extension `g`
  set g : ℂ → ℂ := Function.update φ 0 (limUnder (𝓝[≠] (0 : ℂ)) φ) with hg
  have hg0 : AnalyticAt ℂ g 0 :=
    analyticAt_update_limUnder_of_bddUnder hd ⟨ε + ‖φ 0‖, by
      rw [Filter.eventually_map]
      filter_upwards [hbz] with z hz
      calc ‖φ z - φ 0‖ ≤ ‖φ z‖ + ‖φ 0‖ := norm_sub_le _ _
        _ ≤ ε + ‖φ 0‖ := by linarith⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u hud
    by_cases hu0 : u = 0
    · rw [hu0]; exact hg0
    · have heq : g =ᶠ[𝓝 u] φ := by
        filter_upwards [isOpen_ne.mem_nhds hu0] with z hz
        exact Function.update_of_ne hz _ _
      exact (hφ_an u (norm_pos_iff.mpr hu0) hud).congr heq.symm
  · intro u hu hud
    rw [show g u = φ u from Function.update_of_ne (norm_pos_iff.mp hu) _ _]
    exact hφ_root u hu hud
  · -- the iff transfers to the extension `g` (which equals `φ` off `0`)
    intro u t hu hud
    have hune : u ≠ 0 := norm_pos_iff.mp hu
    have hkey : ∀ u' : ℂ, u' ^ m = u ^ m → u' ≠ 0 := fun u' hu'm h0 => by
      rw [h0, zero_pow hm.ne'] at hu'm; exact pow_ne_zero m hune hu'm.symm
    rw [hφ_iff u t hu hud]
    refine ⟨fun ⟨u', hu'm, h⟩ => ⟨u', hu'm, ?_⟩, fun ⟨u', hu'm, h⟩ => ⟨u', hu'm, ?_⟩⟩
    · rw [show g u' = φ u' from Function.update_of_ne (hkey u' hu'm) _ _]; exact h
    · rw [show g u' = φ u' from Function.update_of_ne (hkey u' hu'm) _ _] at h; exact h

/-- **Lemma 4.2.6, `s = 0`, for an irreducible Weierstrass family (analytic prerequisites discharged).**
The root-bound (`hbdd`) and path-connectedness (`hpc`) hypotheses of `exists_param_s0_full` are
discharged here from irreducibility and the Weierstrass structure (`roots_eventually_bounded` and
`rootCover_pathConnected`); only separability off `0` (the discriminant condition) remains a hypothesis. -/
theorem exists_param_irreducible (q : (Fin 1 → ℂ) → Polynomial ℂ) (m : ℕ) (hm : 0 < m)
    (hmonic : ∀ y, (q y).Monic) (hdeg : ∀ y, (q y).natDegree = m)
    (hcoeff : ∀ i, ∀ y, AnalyticAt ℂ (fun z => (q z).coeff i) y)
    (hq0 : q 0 = X ^ m) (hirr : UnivIrreducible q)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x : Fin 1 → ℂ, 0 < ‖x‖ → ‖x‖ < δ → (q x).Separable) :
    ∃ φ : ℂ → ℂ,
      (∀ u : ℂ, ‖u‖ ^ m < δ → AnalyticAt ℂ φ u) ∧
      (∀ u : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ → (q (fun _ => u ^ m)).eval (φ u) = 0) ∧
      (∀ u t : ℂ, 0 < ‖u‖ → ‖u‖ ^ m < δ →
        ((q (fun _ => u ^ m)).eval t = 0 ↔ ∃ u' : ℂ, u' ^ m = u ^ m ∧ φ u' = t)) := by
  set U : Set (Fin 1 → ℂ) := {x | 0 < ‖x‖ ∧ ‖x‖ < δ} with hU
  have hcont : ∀ i, Continuous (fun y => (q y).coeff i) :=
    fun i => continuous_iff_continuousAt.mpr fun y => (hcoeff i y).continuousAt
  have hUeq : U = Metric.ball (0 : Fin 1 → ℂ) δ \ {0} := by
    ext x
    simp only [hU, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, Set.mem_diff,
      Set.mem_singleton_iff, norm_pos_iff]
    tauto
  have hUopen : IsOpen U := by rw [hUeq]; exact Metric.isOpen_ball.sdiff isClosed_singleton
  have hrank : (1 : Cardinal) < Module.rank ℝ (Fin 1 → ℂ) := by
    rw [(LinearEquiv.funUnique (Fin 1) ℝ ℂ).rank_eq, Complex.rank_real_complex]
    exact_mod_cast Nat.one_lt_two
  have hUconn : IsPreconnected U := by
    rw [hUeq]; exact (isPathConnected_ball_diff_singleton hrank hδ).isConnected.isPreconnected
  have hU0 : U ∈ 𝓝[≠] (0 : Fin 1 → ℂ) := by
    rw [hUeq, Set.diff_eq, Set.inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds 0 hδ)
  have hbdd := roots_eventually_bounded q m hm hmonic hdeg hcont hq0 (R := 1) one_pos
  have hpc : PathConnectedSpace ↥(rootProj q ⁻¹' U) :=
    rootCover_pathConnected q hm hmonic hdeg hcoeff hq0 hirr hUopen hUconn
      (fun y hy => hsep y hy.1 hy.2) hU0 zero_le_one (hbdd.filter_mono nhdsWithin_le_nhds)
  exact exists_param_s0_full q m hm hmonic hdeg hcoeff hδ hsep hpc hbdd

end Puiseux
