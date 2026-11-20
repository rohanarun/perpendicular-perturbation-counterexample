import Arc
import Homothets

/-! The norm axioms, failure of strict convexity, and the link from actual
distances to the scaled squared gauge used in the circumcircle argument. -/
namespace CrescentNormPlane

/-- The real norm axioms in Cartesian coordinates. -/
structure IsPlaneNorm (N : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ N x y
  definite : ∀ x y, N x y = 0 ↔ x = 0 ∧ y = 0
  homogeneous : ∀ t x y, N (t*x) (t*y) = |t| * N x y
  triangle : ∀ x y u v, N (x+u) (y+v) ≤ N x y + N u v

theorem is_norm : IsPlaneNorm CrescentArc.gauge :=
  ⟨CrescentArc.gauge_nonneg, CrescentArc.gauge_zero_iff,
   CrescentArc.gauge_scale, CrescentArc.gauge_add⟩

/-- Strict convexity of the norm expressed by the unit-sphere midpoint test. -/
def StrictUnitMidpoints (N : ℝ → ℝ → ℝ) : Prop :=
  ∀ x₁ y₁ x₂ y₂ : ℝ, N x₁ y₁ = 1 → N x₂ y₂ = 1 →
    (x₁,y₁) ≠ (x₂,y₂) → N ((x₁+x₂)/2) ((y₁+y₂)/2) < 1

theorem not_strictly_convex : ¬StrictUnitMidpoints CrescentArc.gauge := by
  intro h
  have left := CrescentArc.unit_segment (3/5) (by norm_num) (by norm_num)
  have right := CrescentArc.unit_segment (13/20) (by norm_num) (by norm_num)
  have midpoint := CrescentArc.unit_segment (5/8) (by norm_num) (by norm_num)
  have distinct : ((3/5 : ℝ),(5/4-3/5 : ℝ)) ≠ (13/20,5/4-13/20) := by
    intro eq
    have := congrArg Prod.fst eq
    norm_num at this
  have lt := h _ _ _ _ left right distinct
  norm_num at midpoint lt
  linarith

private theorem scaled_sq_max (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    25*(max x y)^2 = max (25*x^2) (25*y^2) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx h 2) (by norm_num)
  · rw [max_eq_left h, max_eq_left]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy h 2) (by norm_num)

theorem gauge_squared (x y : ℝ) :
    CrescentCircles.gauge x y = 25*(CrescentArc.gauge x y)^2 := by
  have he : 0 ≤ CrescentArc.euclid x y := Real.sqrt_nonneg _
  have hf : 0 ≤ CrescentArc.ellipse x y := Real.sqrt_nonneg _
  have hs : 0 ≤ CrescentArc.strip x y := by unfold CrescentArc.strip; positivity
  have de : 25*(CrescentArc.euclid x y)^2 = CrescentCircles.disk x y := by
    unfold CrescentArc.euclid CrescentCircles.disk
    rw [Real.sq_sqrt (by positivity)]
  have ef : 25*(CrescentArc.ellipse x y)^2 = CrescentCircles.ellipse x y := by
    unfold CrescentArc.ellipse CrescentCircles.ellipse
    rw [Real.sq_sqrt (by positivity)]; ring
  have sf : 25*(CrescentArc.strip x y)^2 = CrescentCircles.slab x y := by
    unfold CrescentArc.strip CrescentCircles.slab
    rw [mul_pow, sq_abs]; ring
  unfold CrescentArc.gauge CrescentCircles.gauge
  rw [scaled_sq_max _ _ (he.trans (le_max_left ..)) hs, scaled_sq_max _ _ he hf,
    de, ef, sf, max_assoc]

end CrescentNormPlane
