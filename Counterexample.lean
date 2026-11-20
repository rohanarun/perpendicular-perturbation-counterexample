import Configuration
import FourPoints
import NormPlane

/-! A fixed non-strictly convex plane norm refutes Conjecture 6.5 of Fish,
King, Miller, Palsson and Wahlenmayer for every cardinality at least four. -/
namespace CrescentCounterexample

open CrescentConfiguration CrescentNormPlane

/-- A nondegenerate unit segment from F to F+D. -/
def UnitSegment (N : Gauge) (F D : Plane) : Prop :=
  D ≠ 0 ∧ ∀ t : ℝ, 0≤t → t≤1 → N (F.1+t*D.1) (F.2+t*D.2) = 1

theorem flat_face : ∃ F D, UnitSegment CrescentArc.gauge F D := by
  refine ⟨(3/5,13/20),(1/20,-1/20),?_,?_⟩
  · intro e
    have h := congrArg Prod.fst e
    norm_num at h
  · intro t ht ht'
    change CrescentArc.gauge (3/5+t*(1/20)) (13/20+t*(-1/20))=1
    rw [show (13/20+t*(-1/20):ℝ)=5/4-(3/5+t*(1/20)) by ring]
    apply CrescentArc.unit_segment <;> linarith

/-- Definition 4.1 in coordinates. The target spacing V is perpendicular to a
unit-segment direction D. The matching permutation and the common displacement
direction W are unrestricted. -/
def PerpendicularPerturbation {n : ℕ} (N : Gauge) (P : Fin n → Plane) : Prop :=
  ∃ (F D Q V W : Plane), UnitSegment N F D ∧ V ≠ 0 ∧
    V.1*D.1+V.2*D.2=0 ∧ W ≠ 0 ∧ ∃ (rank : Equiv.Perm (Fin n)) (t : Fin n → ℝ),
      ∀ i, P i = (Q.1 + ((rank i).val:ℝ)*V.1 + t i*W.1,
                  Q.2 + ((rank i).val:ℝ)*V.2 + t i*W.2)

theorem perturbation_implies_parallel {n : ℕ} {N : Gauge} {P : Fin n → Plane}
    (h : PerpendicularPerturbation N P) : ParallelDisplacements P := by
  obtain ⟨_,_,Q,V,W,_,_,_,hW,r,t,hp⟩ := h
  refine ⟨Q,V,W,hW,fun i => ((r i).val:ℤ),?_,t,?_⟩
  · intro i j e
    apply r.injective
    apply Fin.ext
    change ((r i).val:ℤ) = ((r j).val:ℤ) at e
    exact_mod_cast e
  · simpa using hp

theorem no_common_circle {n : ℕ} (i j k l : Fin n) (hij : i<j) (hjk : j<k)
    (hkl : k<l) (q : Plane) (R : ℝ) :
    ¬ (distance CrescentArc.gauge q (point n i)=R ∧ distance CrescentArc.gauge q (point n j)=R ∧
       distance CrescentArc.gauge q (point n k)=R ∧ distance CrescentArc.gauge q (point n l)=R) := by
  rintro ⟨a,b,c,d⟩
  apply CrescentFourPoints.no_common_circle_sq (angle_pos i) (angle_increases hij)
    (angle_increases hjk) (angle_increases hkl) (angle_small l) q.1 q.2 (25*R^2)
  have lift (m : Fin n) (hm : distance CrescentArc.gauge q (point n m)=R) :
      CrescentCircles.gauge (CrescentArc.px (angle n m)-q.1)
        (CrescentArc.py (angle n m)-q.2) = 25*R^2 := by
    rw [gauge_squared]
    exact congrArg (fun z : ℝ => 25*z^2) hm
  exact ⟨lift _ a,lift _ b,lift _ c,lift _ d⟩

theorem line_like_crescent (n : ℕ) : LineLikeCrescent CrescentArc.gauge (point n) :=
  ⟨distinct_points,gap_pattern,noncollinear,no_common_circle⟩

theorem all_sizes {n : ℕ} (hn : 4≤n) :
    LineLikeCrescent CrescentArc.gauge (point n) ∧
      ¬ PerpendicularPerturbation CrescentArc.gauge (point n) :=
  ⟨line_like_crescent n, fun h => cannot_displace hn (perturbation_implies_parallel h)⟩

/-- The threshold conclusion in Conjecture 6.5. Configurations carry a labelling
witnessing the line-like property. Perturbations may use a separate labelling. -/
def EventuallyPerpendicular (N : Gauge) : Prop :=
  ∃ M : ℕ, ∀ n : ℕ, M≤n → ∀ P : Fin n → Plane,
    LineLikeCrescent N P → PerpendicularPerturbation N P

theorem no_threshold : ¬ EventuallyPerpendicular CrescentArc.gauge := by
  rintro ⟨M,h⟩
  obtain ⟨config,obstruction⟩ := all_sizes (le_max_right M 4)
  exact obstruction (h (max M 4) (le_max_left M 4) _ config)

/-- The quantified negation of Conjecture 6.5, with one norm for all thresholds. -/
theorem counterexample : ∃ N : Gauge, IsPlaneNorm N ∧ ¬ StrictUnitMidpoints N ∧
    (∃ F D, UnitSegment N F D) ∧ ¬ EventuallyPerpendicular N :=
  ⟨CrescentArc.gauge,is_norm,not_strictly_convex,flat_face,no_threshold⟩

#print axioms counterexample

end CrescentCounterexample
