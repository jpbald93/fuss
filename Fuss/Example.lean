import Fuss.Geometry

/-!
# Non-vacuity

In the Euclidean plane `EuclideanSpace ℝ (Fin 2)`: `Γ` with centre `(1, 0)`, radius `7`, and `ω` with
centre `0`, radius `24/5`.  Then `d = 1`, `d + r = 29/5 < 7`, and `(49 - 1)² = 2304 = 2 (24/5)² · 50`,
so Fuss's relation holds with non-concentric circles, and bicentric quadrilaterals exist (through
every point of `Γ`).
-/

open EuclideanGeometry

namespace Fuss

/-- A non-concentric configuration satisfying all hypotheses of `exists_bicentric_of_fuss`, and
the resulting bicentric quadrilateral through every point of `Γ`. -/
theorem nonvacuous :
    ∃ Γ ω : Sphere (EuclideanSpace ℝ (Fin 2)), 0 < ω.radius ∧
      dist Γ.center ω.center + ω.radius < Γ.radius ∧ Γ.center ≠ ω.center ∧
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) ∧
      ∀ A ∈ Γ, ∃ B C D, IsBicentric Γ ω A B C D := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  let Γ : Sphere (EuclideanSpace ℝ (Fin 2)) := ⟨EuclideanSpace.single 0 1, 7⟩
  let ω : Sphere (EuclideanSpace ℝ (Fin 2)) := ⟨0, 24 / 5⟩
  have hd : dist Γ.center ω.center = 1 := by
    show dist (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) 0 = 1
    rw [dist_zero_right, PiLp.norm_single, norm_one]
  have hr : (0 : ℝ) < ω.radius := by show (0 : ℝ) < 24 / 5; norm_num
  have hin : dist Γ.center ω.center + ω.radius < Γ.radius := by
    rw [hd]; show (1 : ℝ) + 24 / 5 < 7; norm_num
  have hF : (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
    rw [hd]; show ((7 : ℝ) ^ 2 - 1 ^ 2) ^ 2 = 2 * (24 / 5) ^ 2 * (7 ^ 2 + 1 ^ 2); norm_num
  refine ⟨Γ, ω, hr, hin, ?_, hF, fun A hA => exists_bicentric_of_fuss Γ ω hr hin hF hA⟩
  intro h
  rw [h, dist_self] at hd
  norm_num at hd

end Fuss
