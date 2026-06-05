import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.LocPathConnected

/-!
# C1: the `uᵐ` reference cover and its transitive monodromy

The convergent/covering route to the Puiseux parametrization identifies the connected root-covering of
the punctured disc with the standard `m`-fold cover `u ↦ uᵐ : ℂ* → ℂ*` (`isCoveringMap_npow`, Mathlib).
This file lays the foundation:

* `transitive_monodromy_of_pathConnected` — path-connected total space ⟹ transitive monodromy
  (reusable; recalled from the archived monodromy work, fully proved);
* `Complex.instPathConnectedSpaceNeZero` — `ℂ* = {z ≠ 0}` is path-connected (`ℝ²` minus a point);
* `isCoveringMap_npow_transitive` — the `uᵐ` cover has transitive monodromy: any two points of one
  fiber are joined by a base loop whose lift carries one to the other. This is the structural input to
  the cover classification (C2).
-/

noncomputable section

open Topology

/-- **Path-connected total space ⟹ transitive monodromy.** For a covering `p : E → X` with `E`
path-connected, any two points `e₀, e₁` of the same fiber are joined by a base loop `γ` whose lift
from `e₀` ends at `e₁`. (A path `δ : e₀ ⤳ e₁` projects to a loop `p ∘ δ`; by uniqueness of lifts the
lift of `p ∘ δ` from `e₀` is `δ`, ending at `e₁`.) -/
theorem transitive_monodromy_of_pathConnected {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) [PathConnectedSpace E]
    {e₀ e₁ : E} (hpe : p e₀ = p e₁) :
    ∃ (γ : C(unitInterval, X)) (hγ0 : γ 0 = p e₀),
      γ 1 = p e₀ ∧ cov.liftPath γ e₀ hγ0 1 = e₁ := by
  let δ : Path e₀ e₁ := PathConnectedSpace.somePath e₀ e₁
  let dc : C(unitInterval, E) := δ.toContinuousMap
  have h0 : dc 0 = e₀ := δ.source
  have h1 : dc 1 = e₁ := δ.target
  have hγ0 : (⟨p ∘ dc, cov.continuous.comp dc.continuous⟩ : C(unitInterval, X)) 0 = p e₀ := by
    show p (dc 0) = p e₀; rw [h0]
  refine ⟨⟨p ∘ dc, cov.continuous.comp dc.continuous⟩, hγ0, ?_, ?_⟩
  · show p (dc 1) = p e₀; rw [h1, hpe]
  · have hdceq : dc = cov.liftPath ⟨p ∘ dc, cov.continuous.comp dc.continuous⟩ e₀ hγ0 :=
      (cov.eq_liftPath_iff' (Γ := dc) hγ0).mpr ⟨rfl, h0⟩
    rw [← hdceq]; exact h1

/-- `ℂ* = {z ≠ 0}` is path-connected: it is `ℝ²` (real rank `2 > 1`) minus a point. -/
instance Complex.instPathConnectedSpaceNeZero : PathConnectedSpace {z : ℂ // z ≠ 0} := by
  have h : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) 0
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-- **The `uᵐ` cover has transitive monodromy.** For `m ≠ 0`, any two `m`-th roots `e₀, e₁` of the
same value (`e₀ᵐ = e₁ᵐ`) are joined by a loop in `ℂ*` whose lift along `u ↦ uᵐ` carries `e₀` to `e₁`.
This is the cyclic (`m`-cycle) monodromy of the reference cover, the input to C2's classification. -/
theorem isCoveringMap_npow_transitive (m : ℕ) (hm : (m : ℂ) ≠ 0)
    {e₀ e₁ : {z : ℂ // z ≠ 0}}
    (h : (⟨(e₀ : ℂ) ^ m, pow_ne_zero m e₀.2⟩ : {z : ℂ // z ≠ 0})
       = ⟨(e₁ : ℂ) ^ m, pow_ne_zero m e₁.2⟩) :
    ∃ (γ : C(unitInterval, {z : ℂ // z ≠ 0}))
        (hγ0 : γ 0 = ⟨(e₀ : ℂ) ^ m, pow_ne_zero m e₀.2⟩),
      γ 1 = ⟨(e₀ : ℂ) ^ m, pow_ne_zero m e₀.2⟩ ∧
        (isCoveringMap_npow m hm).liftPath γ e₀ hγ0 1 = e₁ :=
  transitive_monodromy_of_pathConnected (isCoveringMap_npow m hm) h

/-- **Transitive cyclic action ⟹ generator has full order.** A permutation `σ` of a finite set whose
powers act transitively (`∀ a b, ∃ k, σᵏ a = b`) satisfies `σ^(card) = 1`. (Transitivity forces `σ` to
be a single cycle on all `card` elements, so `orderOf σ = card`.)

This is the combinatorial heart of the cover classification: the monodromy generator `σ` of a
*connected* `m`-sheeted cover acts transitively on the fiber (C1), hence `σᵐ = id` — exactly the
periodicity that makes the pulled-back root function `φ(u)` single-valued (C3). -/
theorem Equiv.Perm.pow_card_eq_one_of_transitive {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (htrans : ∀ a b : α, ∃ k : ℕ, (σ ^ k) a = b) :
    σ ^ Fintype.card α = 1 := by
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hcard | hcard
  · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact Subsingleton.elim _ _
  · obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    have hfix : ∀ a, σ a ≠ a := by
      intro a ha
      have hcard : Fintype.card α ≤ 1 := by
        refine Fintype.card_le_one_iff.mpr fun x y => ?_
        obtain ⟨kx, hkx⟩ := htrans a x
        obtain ⟨ky, hky⟩ := htrans a y
        rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ha] at hkx hky
        rw [← hkx, ← hky]
      omega
    have hsupp : σ.support = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun a => Equiv.Perm.mem_support.mpr (hfix a)
    have hcyc : σ.IsCycle :=
      ⟨a₀, hfix a₀, fun y _ => by
        obtain ⟨k, hk⟩ := htrans a₀ y
        exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩⟩
    have hord : orderOf σ = Fintype.card α := by
      rw [hcyc.orderOf, hsupp, Finset.card_univ]
    rw [← hord, pow_orderOf_eq_one]

/-! ### The `exp` universal-cover lift -/

/-- `exp : ℂ → ℂ*` as a continuous map into the punctured plane (the universal covering map of `ℂ*`,
`isCoveringMap_exp`). -/
def Complex.expNeZero : C(ℂ, {z : ℂ // z ≠ 0}) :=
  ⟨fun z => ⟨z.exp, z.exp_ne_zero⟩, Complex.continuous_exp.subtype_mk _⟩

/-- **Universal-cover lift.** For *any* covering `p : E → ℂ*` and any lift `e₀` of `1`, the map
`exp : ℂ → ℂ*` lifts uniquely through `p` (sending `0 ↦ e₀`). Since `ℂ` is contractible — hence simply
connected and locally path-connected — the lifting criterion is vacuous and Mathlib's
`existsUnique_continuousMap_lifts` applies directly.

This is the analytic-route replacement for `π₁(ℂ*) = ℤ` (absent in Mathlib): the lift makes the
multivalued root function single-valued in the *log-coordinate* `w` (`exp w = x`), and the explicit
`2πi`-deck periodicity of `exp` then drives the `uᵐ` parametrization (C3). -/
theorem exists_exp_lift {E : Type*} [TopologicalSpace E] {p : E → {z : ℂ // z ≠ 0}}
    (cov : IsCoveringMap p) (e₀ : E) (he : p e₀ = ⟨1, one_ne_zero⟩) :
    ∃! F : C(ℂ, E), F 0 = e₀ ∧ p ∘ F = Complex.expNeZero := by
  apply cov.existsUnique_continuousMap_lifts Complex.expNeZero 0 e₀
  rw [he]; exact Subtype.ext Complex.exp_zero.symm

/-- **Periodicity propagation.** Let `r : ℂ → E` be a lift of `exp` along a covering `p : E → ℂ*`,
and let `T` be a period of `exp` (`exp T = 1`). If `r` is periodic at a *single* point (`r T = r 0`)
then it is periodic *everywhere*: `r(w + T) = r w` for all `w`.

The proof is pure lift-uniqueness: `w ↦ r(w + T)` is again a lift of `exp` (since `exp(w+T) = exp w`),
and it agrees with `r` at `0`, so by `exists_exp_lift` the two lifts coincide. With `T = 2πi·m` and
`r T = r 0` supplied by `σᵐ = id` (`Equiv.Perm.pow_card_eq_one_of_transitive`), this is the
`2πi·m`-periodicity that makes `φ(u) := root(r(m·log u))` single-valued (C3). -/
theorem exp_lift_period {E : Type*} [TopologicalSpace E] {p : E → {z : ℂ // z ≠ 0}}
    (cov : IsCoveringMap p) {r : C(ℂ, E)} (hr : (p : E → _) ∘ r = Complex.expNeZero)
    {T : ℂ} (hT : Complex.exp T = 1) (h0 : r T = r 0) :
    ∀ w, r (w + T) = r w := by
  have hpt : p (r 0) = (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
    have h := congrFun hr 0
    simp only [Function.comp_apply] at h
    rw [h]; exact Subtype.ext Complex.exp_zero
  set rT : C(ℂ, E) := r.comp ⟨(· + T), by fun_prop⟩ with hrT
  have hshift : (p : E → _) ∘ rT = Complex.expNeZero := by
    funext w
    show p (r (w + T)) = Complex.expNeZero w
    have h := congrFun hr (w + T)
    simp only [Function.comp_apply] at h
    rw [h]
    exact Subtype.ext (by simp [Complex.expNeZero, Complex.exp_add, hT])
  have hrT0 : rT 0 = r 0 := by show r (0 + T) = r 0; rw [zero_add]; exact h0
  have heq : rT = r := (exists_exp_lift cov (r 0) hpt).unique ⟨hrT0, hshift⟩ ⟨rfl, hr⟩
  intro w
  exact DFunLike.congr_fun heq w

open Real in
/-- **Transitivity in orbit form.** If `E` is path-connected, every point `e'` of the fiber over the
base point of the `exp`-lift `r` lies on `r`'s `2πi`-spaced `ℤ`-orbit: `e' = r(k · 2πi)` for some
`k : ℤ`.

Proof: lift the connecting loop `p ∘ δ` (`δ : e₀ ⤳ e'`) to `ℂ` along the `exp` universal cover; its
endpoint `η 1` satisfies `exp(η 1) = 1`, so `η 1 = k · 2πi` (`Complex.exp_eq_one_iff`); and `r ∘ η`
is a `p`-lift of `p ∘ δ` from `e₀`, hence equals `δ` by uniqueness, giving `e' = δ 1 = r(η 1)`.

This is the connectedness ⟹ transitive-monodromy content **without `π₁(ℂ*) = ℤ`** (absent in Mathlib).
Combined with the fiber being `m`-element, it yields the period `r(m · 2πi) = r 0` of `exp_lift_period`. -/
theorem exp_lift_covers_fiber {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {p : E → {z : ℂ // z ≠ 0}} (cov : IsCoveringMap p) {r : C(ℂ, E)} {e₀ : E}
    (hr0 : r 0 = e₀) (hr : (p : E → _) ∘ r = Complex.expNeZero)
    {e' : E} (he' : p e' = p e₀) :
    ∃ k : ℤ, e' = r ((k : ℂ) * (2 * (π : ℂ) * Complex.I)) := by
  have hpe₀ : p e₀ = (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
    have h := congrFun hr 0
    simp only [Function.comp_apply] at h
    rw [← hr0, h]; exact Subtype.ext Complex.exp_zero
  let δ : Path e₀ e' := PathConnectedSpace.somePath e₀ e'
  let ℓ : C(unitInterval, {z : ℂ // z ≠ 0}) := (⟨p, cov.continuous⟩ : C(E, _)).comp δ.toContinuousMap
  have hℓ0 : ℓ 0 = (fun z : ℂ => (⟨z.exp, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 := by
    show p (δ 0) = ⟨(0 : ℂ).exp, _⟩
    rw [δ.source, hpe₀]; exact Subtype.ext Complex.exp_zero.symm
  let η : C(unitInterval, ℂ) := Complex.isCoveringMap_exp.liftPath ℓ 0 hℓ0
  have hη_lifts : (fun z : ℂ => (⟨z.exp, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ η = ℓ :=
    Complex.isCoveringMap_exp.liftPath_lifts ℓ 0 hℓ0
  have hη0 : η 0 = 0 := Complex.isCoveringMap_exp.liftPath_zero ℓ 0 hℓ0
  have hexpη1 : Complex.exp (η 1) = 1 := by
    have h := congrFun hη_lifts 1
    simp only [Function.comp_apply] at h
    have hℓ1 : ℓ 1 = (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
      show p (δ 1) = _; rw [δ.target, he', hpe₀]
    rw [hℓ1] at h
    exact congrArg Subtype.val h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexpη1
  have hγ0 : ℓ 0 = p e₀ := by show p (δ 0) = p e₀; rw [δ.source]
  have hδeq : δ.toContinuousMap = cov.liftPath ℓ e₀ hγ0 :=
    (cov.eq_liftPath_iff' (Γ := δ.toContinuousMap) hγ0).mpr ⟨rfl, δ.source⟩
  have hrη_lifts : (p : E → _) ∘ (r.comp η) = ℓ := by
    funext s
    show p (r (η s)) = ℓ s
    have h := congrFun hr (η s)
    simp only [Function.comp_apply] at h
    rw [h]
    have h2 := congrFun hη_lifts s
    simp only [Function.comp_apply] at h2
    exact h2
  have hrη0 : (r.comp η) 0 = e₀ := by show r (η 0) = e₀; rw [hη0, hr0]
  have hrηeq : r.comp η = cov.liftPath ℓ e₀ hγ0 :=
    (cov.eq_liftPath_iff' (Γ := r.comp η) hγ0).mpr ⟨hrη_lifts, hrη0⟩
  refine ⟨k, ?_⟩
  have hcoincide : δ.toContinuousMap = r.comp η := hδeq.trans hrηeq.symm
  calc e' = δ.toContinuousMap 1 := δ.target.symm
    _ = (r.comp η) 1 := by rw [hcoincide]
    _ = r (η 1) := rfl
    _ = r ((k : ℂ) * (2 * (π : ℂ) * Complex.I)) := by rw [hk]

/-- **Shift lemma.** For two periods `a, b` of `exp` (`exp a = exp b = 1`) at which the `exp`-lift `r`
agrees (`r a = r b`), the whole lift agrees under the two shifts: `r(w + a) = r(w + b)` for all `w`.

Again pure lift-uniqueness (`w ↦ r(w+a)` and `w ↦ r(w+b)` are lifts of `exp` agreeing at `0`). This is
the key to converting the orbit surjectivity of `exp_lift_covers_fiber` into the *exact* period: the
set of periods `{k : r(k·2πi) = r 0}` is an `AddSubgroup` of `ℤ`, the orbit map descends to an
*injection* `ℤ ⧸ periods ↪ fiber`, and surjectivity (`exp_lift_covers_fiber`) makes it a bijection —
so the index equals the fiber size `m`, giving `m·2πi ∈ periods`, i.e. `r(m·2πi) = r 0`. -/
theorem exp_lift_shift {E : Type*} [TopologicalSpace E] {p : E → {z : ℂ // z ≠ 0}}
    (cov : IsCoveringMap p) {r : C(ℂ, E)} (hr : (p : E → _) ∘ r = Complex.expNeZero)
    {a b : ℂ} (ha : Complex.exp a = 1) (hb : Complex.exp b = 1) (hab : r a = r b) :
    ∀ w, r (w + a) = r (w + b) := by
  have hpt : p (r a) = (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
    have h := congrFun hr a
    simp only [Function.comp_apply] at h
    rw [h]; exact Subtype.ext ha
  set ra : C(ℂ, E) := r.comp ⟨(· + a), by fun_prop⟩ with hra_def
  set rb : C(ℂ, E) := r.comp ⟨(· + b), by fun_prop⟩ with hrb_def
  have hra : (p : E → _) ∘ ra = Complex.expNeZero := by
    funext w; show p (r (w + a)) = Complex.expNeZero w
    have h := congrFun hr (w + a); simp only [Function.comp_apply] at h
    rw [h]; exact Subtype.ext (by simp [Complex.expNeZero, Complex.exp_add, ha])
  have hrb : (p : E → _) ∘ rb = Complex.expNeZero := by
    funext w; show p (r (w + b)) = Complex.expNeZero w
    have h := congrFun hr (w + b); simp only [Function.comp_apply] at h
    rw [h]; exact Subtype.ext (by simp [Complex.expNeZero, Complex.exp_add, hb])
  have hra0 : ra 0 = r a := by show r (0 + a) = r a; rw [zero_add]
  have hrb0 : rb 0 = r a := by show r (0 + b) = r a; rw [zero_add]; exact hab.symm
  have heq : ra = rb := (exists_exp_lift cov (r a) hpt).unique ⟨hra0, hra⟩ ⟨hrb0, hrb⟩
  intro w
  exact DFunLike.congr_fun heq w

/-- A single period `c` of a continuous map `r : ℂ → E` extends to all integer multiples:
`r(w + n·c) = r w` for every `n : ℤ`. (Used to bound the `ℤ`-orbit by one period.) -/
theorem r_zmul_period {E : Type*} [TopologicalSpace E] (r : C(ℂ, E)) {c : ℂ}
    (hper : ∀ w, r (w + c) = r w) : ∀ (n : ℤ) (w : ℂ), r (w + (n : ℂ) * c) = r w := by
  intro n
  induction n using Int.induction_on with
  | zero => intro w; simp
  | succ k ih =>
      intro w
      have heq : w + (((k : ℤ) + 1 : ℤ) : ℂ) * c = (w + ((k : ℤ) : ℂ) * c) + c := by
        push_cast; ring
      rw [heq, hper]; exact ih w
  | pred k ih =>
      intro w
      have heq : w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * c + c = w + ((-(k : ℤ) : ℤ) : ℂ) * c := by
        push_cast; ring
      have hh := hper (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * c)
      rw [heq] at hh
      rw [← hh]; exact ih w

open Real in
/-- **The `m`-sheet period.** Let `r : ℂ → E` be a lift of `exp` along a covering `p : E → ℂ*` with
`r 0 = e₀`, `E` path-connected, and the fibre `{e // p e = p e₀}` finite of cardinality `m`. Then
`m · 2πi` is a period of `r`: `r(m · 2πi) = r 0`.

This is the period-counting heart of the convergent-Puiseux route. Combining `exp_lift_covers_fiber`
(the `ℤ`-orbit `k ↦ r(k·2πi)` *surjects* onto the fibre) with `exp_lift_shift`/`r_zmul_period` (two
orbit points coinciding yields a period that makes the orbit factor through `ℤ/d`, hence its image has
`≤ d` elements): pigeonhole on `m+1` orbit points produces a coincidence with gap `d ≤ m`, the orbit
then factors through `ℤ/d` so `m ≤ d`, forcing `d = m`. The gap `d = m` is exactly the period.

With `T = m · 2πi` and `r T = r 0`, `exp_lift_period` upgrades this to `r(w + m·2πi) = r w` for all `w`
— the `2πi·m`-periodicity that makes `φ(u) := root(r(m·log u))` single-valued (C4). -/
theorem exp_lift_period_card {E : Type*} [TopologicalSpace E] [PathConnectedSpace E]
    {p : E → {z : ℂ // z ≠ 0}} (cov : IsCoveringMap p) {r : C(ℂ, E)} {e₀ : E}
    (hr0 : r 0 = e₀) (hr : (p : E → _) ∘ r = Complex.expNeZero)
    [Fintype {e // p e = p e₀}] :
    r ((Fintype.card {e // p e = p e₀} : ℂ) * (2 * (π : ℂ) * Complex.I)) = r 0 := by
  set T₀ := (2 * (π : ℂ) * Complex.I) with hT₀
  set m := Fintype.card {e // p e = p e₀} with hm
  -- the value of `p ∘ r` and the base point
  have hval : ∀ x : ℂ, (p (r x)).val = Complex.exp x := by
    intro x
    have h := congrFun hr x
    simp only [Function.comp_apply] at h
    rw [h]; rfl
  have hpe₀ : p e₀ = (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
    apply Subtype.ext
    have h0 := hval 0
    rw [hr0, Complex.exp_zero] at h0
    exact h0
  -- every orbit point `r(k·T₀)` lies in the fibre over `e₀`
  have hmem : ∀ k : ℤ, p (r ((k : ℂ) * T₀)) = p e₀ := by
    intro k
    apply Subtype.ext
    rw [hval ((k : ℂ) * T₀), hpe₀]
    exact Complex.exp_int_mul_two_pi_mul_I k
  -- the `ℤ`-orbit, valued in the fibre
  let orbZ : ℤ → {e // p e = p e₀} := fun k => ⟨r ((k : ℂ) * T₀), hmem k⟩
  -- a coincidence `orbZ a = orbZ b` (`a < b`) yields the period `(b - a)·T₀`
  have key : ∀ a b : ℤ, a < b → orbZ a = orbZ b →
      ∀ w, r (w + ((b - a : ℤ) : ℂ) * T₀) = r w := by
    intro a b hab horb w
    have hval_eq : r ((a : ℂ) * T₀) = r ((b : ℂ) * T₀) := congrArg Subtype.val horb
    have hexpa : Complex.exp ((a : ℂ) * T₀) = 1 := Complex.exp_int_mul_two_pi_mul_I a
    have hexpb : Complex.exp ((b : ℂ) * T₀) = 1 := Complex.exp_int_mul_two_pi_mul_I b
    have hshift := exp_lift_shift cov hr hexpa hexpb hval_eq
    have hu := hshift (w - (a : ℂ) * T₀)
    have e1 : (w - (a : ℂ) * T₀) + (a : ℂ) * T₀ = w := by ring
    have e2 : (w - (a : ℂ) * T₀) + (b : ℂ) * T₀ = w + ((b - a : ℤ) : ℂ) * T₀ := by
      push_cast; ring
    rw [e1, e2] at hu
    exact hu.symm
  -- it suffices to produce a period `d·T₀` with `1 ≤ d ≤ m`
  suffices h : ∃ d : ℤ, 1 ≤ d ∧ d ≤ (m : ℤ) ∧ ∀ w, r (w + (d : ℂ) * T₀) = r w by
    obtain ⟨d, hd1, hdm, hper⟩ := h
    have hd0 : (0 : ℤ) < d := by omega
    -- the orbit is invariant under shifting the index by multiples of `d`
    have hreduce : ∀ (n k : ℤ), orbZ (k + n * d) = orbZ k := by
      intro n k
      apply Subtype.ext
      show r (((k + n * d : ℤ) : ℂ) * T₀) = r ((k : ℂ) * T₀)
      have hc : ((k + n * d : ℤ) : ℂ) * T₀ = (k : ℂ) * T₀ + (n : ℂ) * ((d : ℂ) * T₀) := by
        push_cast; ring
      rw [hc]
      exact r_zmul_period r hper n ((k : ℂ) * T₀)
    -- hence the orbit factors through `Fin d.toNat`, which still surjects onto the fibre
    have hsurj : Function.Surjective (fun a : Fin d.toNat => orbZ (a.val : ℤ)) := by
      intro y
      obtain ⟨k, hk⟩ := exp_lift_covers_fiber cov hr0 hr y.2
      have hyk : y = orbZ k := Subtype.ext hk
      have hk0nonneg : 0 ≤ k % d := Int.emod_nonneg k hd0.ne'
      have hk0lt : k % d < d := Int.emod_lt_of_pos k hd0
      have hkk0 : orbZ k = orbZ (k % d) := by
        have hsplit : k = (k % d) + (k / d) * d := by
          have h := Int.emod_add_mul_ediv k d
          rw [mul_comm d (k / d)] at h
          omega
        calc orbZ k = orbZ ((k % d) + (k / d) * d) := by rw [← hsplit]
          _ = orbZ (k % d) := hreduce (k / d) (k % d)
      refine ⟨⟨(k % d).toNat, by omega⟩, ?_⟩
      show orbZ (((k % d).toNat : ℤ)) = y
      rw [Int.toNat_of_nonneg hk0nonneg, ← hkk0]
      exact hyk.symm
    have hcard_le := Fintype.card_le_of_surjective _ hsurj
    rw [Fintype.card_fin, ← hm] at hcard_le
    have hdtoNat : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd0.le
    have hdeq : d = (m : ℤ) := by omega
    have hfin := hper 0
    rw [zero_add, hdeq, Int.cast_natCast] at hfin
    exact hfin
  -- pigeonhole on `m+1` orbit points forces a coincidence with gap `≤ m`
  obtain ⟨i, j, hij, heqij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (m + 1) => orbZ ((i : ℕ) : ℤ))
    (by rw [Fintype.card_fin]; exact Nat.lt_succ_self _)
  have hi := i.isLt
  have hj := j.isLt
  have hijval : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
  rcases lt_or_gt_of_ne hijval with hlt | hgt
  · exact ⟨((j : ℕ) : ℤ) - ((i : ℕ) : ℤ), by omega, by omega,
      key _ _ (by exact_mod_cast hlt) heqij⟩
  · exact ⟨((i : ℕ) : ℤ) - ((j : ℕ) : ℤ), by omega, by omega,
      key _ _ (by exact_mod_cast hgt) heqij.symm⟩

end
