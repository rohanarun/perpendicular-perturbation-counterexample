import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Circumcenters for the ellipse norm with squared gauge (4 x² + 6 y²)/5. -/
namespace CrescentCircumcenter

def det (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) : ℝ :=
  (x₂-x₁)*(y₃-y₁) - (x₃-x₁)*(y₂-y₁)

def squared (x y u v : ℝ) : ℝ := 4*(x-u)^2 + 6*(y-v)^2

/-- Equal squared distances at a pair give a linear equation in the center. -/
theorem bisector (x₁ y₁ x₂ y₂ u v : ℝ) :
    squared x₁ y₁ u v = squared x₂ y₂ u v ↔
      8*(x₂-x₁)*u + 12*(y₂-y₁)*v =
        (4*x₂^2+6*y₂^2) - (4*x₁^2+6*y₁^2) := by
  unfold squared
  constructor <;> intro h <;> linear_combination h

/-- Independent displacement vectors determine a unique ellipse center and a
unique nonnegative radius. In this normalization the ellipse equation is
4(x-u)² + 6(y-v)² = 5R². -/
theorem exists_unique_circumcircle (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ)
    (hd : det x₁ y₁ x₂ y₂ x₃ y₃ ≠ 0) :
    ∃ u v R : ℝ, 0 ≤ R ∧ squared x₁ y₁ u v = 5*R^2 ∧
      squared x₂ y₂ u v = 5*R^2 ∧ squared x₃ y₃ u v = 5*R^2 ∧
      ∀ u' v' R' : ℝ, 0 ≤ R' → squared x₁ y₁ u' v' = 5*R'^2 →
        squared x₂ y₂ u' v' = 5*R'^2 → squared x₃ y₃ u' v' = 5*R'^2 →
        u' = u ∧ v' = v ∧ R' = R := by
  let D := det x₁ y₁ x₂ y₂ x₃ y₃
  let F := (4*x₂^2+6*y₂^2) - (4*x₁^2+6*y₁^2)
  let G := (4*x₃^2+6*y₃^2) - (4*x₁^2+6*y₁^2)
  let u := (F*(y₃-y₁)-G*(y₂-y₁))/(8*D)
  let v := ((x₂-x₁)*G-(x₃-x₁)*F)/(12*D)
  have Dnz : D ≠ 0 := hd
  have lin₂ : 8*(x₂-x₁)*u + 12*(y₂-y₁)*v = F := by
    dsimp only [u,v]
    field_simp [Dnz]
    unfold D det
    ring
  have lin₃ : 8*(x₃-x₁)*u + 12*(y₃-y₁)*v = G := by
    dsimp only [u,v]
    field_simp [Dnz]
    unfold D det
    ring
  have eq₂ := (bisector x₁ y₁ x₂ y₂ u v).mpr lin₂
  have eq₃ := (bisector x₁ y₁ x₃ y₃ u v).mpr lin₃
  let R := Real.sqrt (squared x₁ y₁ u v / 5)
  have hs : 0 ≤ squared x₁ y₁ u v / 5 := by unfold squared; positivity
  have hr : 0 ≤ R := Real.sqrt_nonneg _
  have first : squared x₁ y₁ u v = 5*R^2 := by
    dsimp only [R]
    rw [Real.sq_sqrt hs]
    ring
  refine ⟨u,v,R,hr,first,eq₂.symm.trans first,eq₃.symm.trans first,?_⟩
  intro u' v' R' hr' h₁ h₂ h₃
  have l₂ := (bisector x₁ y₁ x₂ y₂ u' v').mp (h₁.trans h₂.symm)
  have l₃ := (bisector x₁ y₁ x₃ y₃ u' v').mp (h₁.trans h₃.symm)
  change _ = F at l₂
  change _ = G at l₃
  have hu : (u'-u)*D = 0 := by
    dsimp only [D,det]
    linear_combination ((y₃-y₁)/8)*(l₂-lin₂) - ((y₂-y₁)/8)*(l₃-lin₃)
  have hv : (v'-v)*D = 0 := by
    dsimp only [D,det]
    linear_combination ((x₂-x₁)/12)*(l₃-lin₃) - ((x₃-x₁)/12)*(l₂-lin₂)
  have eu := sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right Dnz)
  have ev := sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right Dnz)
  rw [eu,ev,first] at h₁
  exact ⟨eu,ev,by nlinarith [sq_nonneg (R'-R)]⟩

end CrescentCircumcenter
