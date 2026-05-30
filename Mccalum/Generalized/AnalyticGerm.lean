import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mccalum.Order
import Mccalum.OrderMulAnalytic

/-!
# The local ring of holomorphic germs `𝒪ₙ` (Phase B1)

`AnalyticGerm n` is the subring of germs at `0 ∈ ℂⁿ` of functions analytic at `0`. It is the
base ring `𝒪ₙ` over which the Weierstrass polynomial lives in McCallum's proof (the substrate for
`norm_identity_elim` and the discriminant-order argument). Being a `Subring` of the germ ring, it
is automatically a `CommRing`.

Germs are the right object because Weierstrass preparation produces a factorization on an
*arbitrarily small* neighborhood; germs quotient out the shrinking neighborhood.
-/

noncomputable section

open Filter Topology

variable (n : ℕ)

/-- The subring `𝒪ₙ` of germs at `0 ∈ ℂⁿ` admitting an analytic representative. -/
def AnalyticGerm : Subring (Germ (𝓝 (0 : Fin n → ℂ)) ℂ) where
  carrier := { g | ∃ f : (Fin n → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ (↑f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = g }
  zero_mem' := ⟨0, analyticAt_const, by simp⟩
  one_mem' := ⟨1, analyticAt_const, by simp⟩
  add_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
    exact ⟨f₁ + f₂, hf₁.add hf₂, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
    exact ⟨f₁ * f₂, hf₁.mul hf₂, by simp⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, by simp⟩

/-- `𝒪ₙ` is a commutative ring (inherited from the germ ring). -/
example : CommRing (AnalyticGerm n) := inferInstance

/-- A germ in `𝒪ₙ` with an analytic representative nonzero at `0` is a unit (its pointwise
inverse `g⁻¹` is analytic near `0` and provides the inverse germ). -/
theorem AnalyticGerm.isUnit_of_rep_ne_zero {n : ℕ} (b : AnalyticGerm n)
    (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0)
    (hgb : (↑g : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = b.1) : IsUnit b := by
  have hinv : AnalyticAt ℂ g⁻¹ 0 := hg.inv hg0
  have hgg : (g * g⁻¹ : (Fin n → ℂ) → ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)] 1 := by
    filter_upwards [hg.continuousAt.eventually_ne hg0] with x hx
    simp [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel₀ hx]
  have hmem : (↑g⁻¹ : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) ∈ AnalyticGerm n := ⟨g⁻¹, hinv, rfl⟩
  refine isUnit_of_mul_eq_one ⟨↑g⁻¹, hmem⟩ (Subtype.ext ?_)
  show b.1 * (↑g⁻¹ : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = 1
  rw [← hgb, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq.mpr hgg, Filter.Germ.coe_one]

/-- `𝒪ₙ` is a **local ring**: a germ is a unit iff its value at `0` is nonzero; otherwise `1 - g`
has value `1 ≠ 0` and is a unit. -/
instance (n : ℕ) : IsLocalRing (AnalyticGerm n) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨f, hf, hfa⟩ := a.2
  by_cases h0 : f 0 = 0
  · right
    refine AnalyticGerm.isUnit_of_rep_ne_zero (1 - a) (1 - f)
      (analyticAt_const.sub hf) (by simp [Pi.sub_apply, h0]) ?_
    show (↑(1 - f) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = (1 - a).1
    have hra : ((1 - a : AnalyticGerm n) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = 1 - a.1 := by
      push_cast; ring
    rw [hra, Filter.Germ.coe_sub, Filter.Germ.coe_one, hfa]
  · exact Or.inl (AnalyticGerm.isUnit_of_rep_ne_zero a f hf h0 hfa)

/-! ## B2 — the vanishing order / valuation on `𝒪ₙ` -/

/-- If all `< k` Fréchet derivatives of `f` vanish at `x`, then `k ≤ order f x` (field-generic). -/
theorem le_order_of_forall_iteratedFDeriv_eq_zero'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} {k : ℕ∞}
    (h : ∀ j : ℕ, (↑j : ℕ∞) < k → iteratedFDeriv 𝕜 j f x = 0) :
    k ≤ order 𝕜 f x := by
  by_contra hlt
  push_neg at hlt
  have hfin : order 𝕜 f x ≠ ⊤ := ne_top_of_lt hlt
  have hm : order 𝕜 f x = ↑(order 𝕜 f x).toNat := (ENat.coe_toNat hfin).symm
  rw [hm] at hlt
  exact (((order_eq_natCast_iff).mp hm).2) (h _ hlt)

/-- The vanishing `order` depends only on the germ (field-generic version of
`order_congr_of_eventuallyEq`, which is fixed to `ℝ`). -/
theorem order_congr_of_eventuallyEq'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) :
    order 𝕜 f₁ x = order 𝕜 f₂ x := by
  have key : ∀ m : ℕ, iteratedFDeriv 𝕜 m f₁ x = iteratedFDeriv 𝕜 m f₂ x :=
    fun m => (h.iteratedFDeriv 𝕜 m).eq_of_nhds
  apply le_antisymm
  · apply le_order_of_forall_iteratedFDeriv_eq_zero'
    intro j hj
    rw [← key]; exact iteratedFDeriv_eq_zero_of_lt_order hj
  · apply le_order_of_forall_iteratedFDeriv_eq_zero'
    intro j hj
    rw [key]; exact iteratedFDeriv_eq_zero_of_lt_order hj

/-- The vanishing order (valuation) of a germ in `𝒪ₙ`: the `order ℂ` of any analytic
representative at `0`. Well-defined by `order_congr_of_eventuallyEq'`. -/
noncomputable def AnalyticGerm.order (b : AnalyticGerm n) : ℕ∞ :=
  _root_.order ℂ (Classical.choose b.2) (0 : Fin n → ℂ)

/-- **Bridge B2.** The germ valuation equals the `order ℂ` of *any* analytic representative. -/
theorem AnalyticGerm.order_eq_order_rep (b : AnalyticGerm n)
    {f : (Fin n → ℂ) → ℂ} (hfb : (↑f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = b.1) :
    AnalyticGerm.order n b = _root_.order ℂ f (0 : Fin n → ℂ) := by
  have hspec := Classical.choose_spec b.2
  have heq : (↑f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ)
      = (↑(Classical.choose b.2) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) := by rw [hfb, hspec.2]
  have hee : f =ᶠ[𝓝 (0 : Fin n → ℂ)] Classical.choose b.2 := Filter.Germ.coe_eq.mp heq
  unfold AnalyticGerm.order
  exact (order_congr_of_eventuallyEq' hee).symm

/-- **The germ valuation is additive on products:** `v(a·b) = v(a) + v(b)`. This is the
defining property making `AnalyticGerm.order` a valuation on `𝒪ₙ`; it follows from
multiplicativity of the analytic vanishing order (`order_mul_analytic`). -/
theorem AnalyticGerm.order_mul (a b : AnalyticGerm n) :
    AnalyticGerm.order n (a * b)
      = AnalyticGerm.order n a + AnalyticGerm.order n b := by
  obtain ⟨fa, hfa, hfa_eq⟩ := a.2
  obtain ⟨fb, hfb, hfb_eq⟩ := b.2
  have hab : (↑(fun z => fa z * fb z) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = (a * b).1 := by
    have hval : ((a * b : AnalyticGerm n) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = a.1 * b.1 := rfl
    rw [hval]
    show (↑(fa * fb) : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = a.1 * b.1
    rw [Filter.Germ.coe_mul, hfa_eq, hfb_eq]
  rw [AnalyticGerm.order_eq_order_rep n a hfa_eq,
      AnalyticGerm.order_eq_order_rep n b hfb_eq,
      AnalyticGerm.order_eq_order_rep n (a * b) hab]
  exact order_mul_analytic fa fb 0 hfa hfb

end
