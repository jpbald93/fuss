import Mathlib
import Fuss.Plane
import Fuss.Forward
import Fuss.Porism
import Fuss.Steps
import Fuss.Geometry
import Fuss.Example
import Fuss.L14

/-!
# Layer 15: comparison with independently written classical statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

The writer's theorem statements are packaged as `def classical_X : Prop` (binders turned into `∀`).
-/

open EuclideanGeometry

noncomputable section

namespace Fuss.Classical

/-- The Euclidean plane. -/
abbrev Pl := EuclideanSpace ℝ (Fin 2)

/-- OWN DEFINITION. The circle `C` lies in the closed disc of `Γ` and meets `Γ` exactly at
`K`: `C` touches `Γ` internally at `K`. -/
def InternallyTangentAt (C Γ : Sphere Pl) (K : Pl) : Prop :=
  Metric.sphere C.center C.radius ⊆ Metric.closedBall Γ.center Γ.radius ∧
    Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius = {K}

/-- OWN DEFINITION. The closed disc of `C` avoids the open disc of `Γ` (so `C` lies outside
`Γ`, and `Γ` is not inside `C`), and `C` meets `Γ` exactly at `K`: `C` touches `Γ` externally
at `K`. -/
def ExternallyTangentAt (C Γ : Sphere Pl) (K : Pl) : Prop :=
  Disjoint (Metric.closedBall C.center C.radius) (Metric.ball Γ.center Γ.radius) ∧
    Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius = {K}

/-- OWN DEFINITION. Two circles are tangent: they have exactly one common point
(for a point-circle this means the point lies on the other circle). -/
def CirclesTangent (C D : Sphere Pl) : Prop :=
  ∃! p : Pl, p ∈ Metric.sphere C.center C.radius ∧ p ∈ Metric.sphere D.center D.radius

/-- OWN DEFINITION. A line (affine subspace) is tangent to a circle: exactly one common
point. -/
def LineTangent (L : AffineSubspace ℝ Pl) (C : Sphere Pl) : Prop :=
  ∃! p : Pl, p ∈ L ∧ p ∈ Metric.sphere C.center C.radius

/-- OWN DEFINITION. Four points `K 0, K 1, K 2, K 3` (assumed on a common circle) occur in
this cyclic order: they are pairwise distinct and the chords `K0K2`, `K1K3` meet. -/
def CyclicOrder4 (K : Fin 4 → Pl) : Prop :=
  Function.Injective K ∧ (segment ℝ (K 0) (K 2) ∩ segment ℝ (K 1) (K 3)).Nonempty

/-- Length of the direct common tangent of two circles (formula from the problem statement). -/
def directTangent (C D : Sphere Pl) : ℝ :=
  Real.sqrt (dist C.center D.center ^ 2 - (C.radius - D.radius) ^ 2)

/-- Signed-radius tangent length `sqrt(|O_iO_j|^2 - (ρ_i - ρ_j)^2)`. -/
def signedTangent (C D : Sphere Pl) (ρC ρD : ℝ) : ℝ :=
  Real.sqrt (dist C.center D.center ^ 2 - (ρC - ρD) ^ 2)

/-- OWN DEFINITION. `ABCD` is a convex (non-degenerate) quadrilateral: the diagonals `AC`
and `BD` cross at a point strictly inside both, and no three vertices are collinear. -/
def ConvexQuad (A B C D : Pl) : Prop :=
  (∃ X : Pl, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧
    ¬ Collinear ℝ {A, B, C} ∧ ¬ Collinear ℝ {B, C, D} ∧
    ¬ Collinear ℝ {C, D, A} ∧ ¬ Collinear ℝ {D, A, B}

/-- OWN DEFINITION. The circle `ω` is tangent to the side (segment) `PQ`: the whole line
`PQ` stays at distance `≥ r` from the centre and the touching point lies on the segment. -/
def TangentToSide (ω : Sphere Pl) (P Q : Pl) : Prop :=
  (∃ T : Pl, Wbtw ℝ P T Q ∧ dist T ω.center = ω.radius) ∧
    ∀ Y ∈ line[ℝ, P, Q], ω.radius ≤ dist Y ω.center

/-- OWN DEFINITION. `ω` (radius `> 0`) is an incircle of the quadrilateral `ABCD`:
it touches all four sides. -/
def IsIncircleQuad (ω : Sphere Pl) (A B C D : Pl) : Prop :=
  0 < ω.radius ∧ TangentToSide ω A B ∧ TangentToSide ω B C ∧
    TangentToSide ω C D ∧ TangentToSide ω D A

/-- OWN DEFINITION. `ABCD` is a convex quadrilateral inscribed in `Γ` and circumscribed
about `ω` (bicentric with these circles). -/
def BicentricWith (Γ ω : Sphere Pl) (A B C D : Pl) : Prop :=
  ConvexQuad A B C D ∧ A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧ IsIncircleQuad ω A B C D

/-- OWN DEFINITION. The circle `ω` lies strictly inside the circle `Γ`
(`ω` a genuine circle, `r > 0`). -/
def StrictlyInside (ω Γ : Sphere Pl) : Prop :=
  0 < ω.radius ∧ dist ω.center Γ.center + ω.radius < Γ.radius

/-- Writer's statement `classical_CaseyFuss2_a`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss2_a : Prop :=
  ∀ (A B C D : Pl) (Γ ω : Sphere Pl)
    (h : BicentricWith Γ ω A B C D),
    let R := Γ.radius
    let r := ω.radius
    let x := dist Γ.center ω.center
    1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 ∧
      (R ^ 2 - x ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + x ^ 2) ∧
      x ^ 2 = R ^ 2 + r ^ 2 - r * Real.sqrt (4 * R ^ 2 + r ^ 2) ∧
      Real.sqrt 2 * r ≤ R ∧
      (R = Real.sqrt 2 * r ↔ x = 0) ∧
      (x = 0 ↔ (dist A B = dist B C ∧ dist B C = dist C D ∧ dist C D = dist D A ∧
        dist A C = dist B D)) 

/-- Writer's statement `classical_CaseyFuss2_b`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss2_b : Prop :=
  ∀ (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ)
    (hfuss : 1 / (Γ.radius - dist Γ.center ω.center) ^ 2 +
      1 / (Γ.radius + dist Γ.center ω.center) ^ 2 = 1 / ω.radius ^ 2),
    ∃ A B C D : Pl, BicentricWith Γ ω A B C D 

/-- Writer's statement `classical_CaseyFuss3_a`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss3_a : Prop :=
  ∀ (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ)
    (hex : ∃ A B C D : Pl, BicentricWith Γ ω A B C D),
    (∀ P ∈ Γ, ∃ B C D : Pl, BicentricWith Γ ω P B C D) ∧
      (∀ P ∈ Γ, ∀ p : ℕ → Pl, p 0 = P → (∀ n, p n ∈ Γ) → (∀ n, p n ≠ p (n + 1)) →
        (∀ n, LineTangent line[ℝ, p n, p (n + 1)] ω) → (∀ n, p (n + 2) ≠ p n) →
        p 4 = p 0 ∧ p 3 ≠ p 0 ∧
          BicentricWith Γ ω (p 0) (p 1) (p 2) (p 3)) ∧
      {q : Fin 4 → Pl | BicentricWith Γ ω (q 0) (q 1) (q 2) (q 3)}.Infinite 

/-- Writer's statement `classical_CaseyFuss3_b`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss3_b : Prop :=
  ∀ (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ),
    let R := Γ.radius
    let r := ω.radius
    let x := dist Γ.center ω.center
    ((∃ A B C D : Pl, BicentricWith Γ ω A B C D) ↔
        1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2) ∧
      (1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 →
        ∀ P ∈ Γ, ∃ B C D : Pl, BicentricWith Γ ω P B C D) 

instance factPl : Fact (Module.finrank ℝ Pl = 2) := ⟨finrank_euclideanSpace_fin⟩

/-! ## Bridge lemmas (NEW) -/

/-- The writer's side tangency gives Mathlib tangency of the side line. -/
theorem tangentAt_of_side {ω : Sphere Pl} {P Q : Pl} (h : TangentToSide ω P Q) :
    ∃ T, ω.IsTangentAt T line[ℝ, P, Q] := by
  obtain ⟨⟨T, hTw, hT⟩, hfar⟩ := h
  have hTL : T ∈ line[ℝ, P, Q] := hTw.mem_affineSpan
  refine ⟨T, ⟨EuclideanGeometry.mem_sphere.2 hT, hTL, ?_⟩⟩
  intro Y hY
  rw [Sphere.mem_orthRadius_iff_inner_left]
  have hr : 0 ≤ ω.radius := by rw [← hT]; exact dist_nonneg
  set v : Pl := Y -ᵥ T
  set w : Pl := T -ᵥ ω.center
  have hw : ‖w‖ = ω.radius := by rw [← dist_eq_norm_vsub]; exact hT
  have key : ∀ t : ℝ, 0 ≤ t ^ 2 * ‖v‖ ^ 2 + 2 * t * inner ℝ v w := by
    intro t
    have h1 := hfar _ (AffineMap.lineMap_mem t hTL hY)
    have e : dist (AffineMap.lineMap T Y t) ω.center = ‖t • v + w‖ := by
      rw [dist_eq_norm_vsub, AffineMap.lineMap_apply, vadd_vsub_assoc]
    rw [e] at h1
    have h2 : ω.radius ^ 2 ≤ ‖t • v + w‖ ^ 2 := pow_le_pow_left₀ hr h1 2
    rw [norm_add_sq_real, norm_smul, inner_smul_left, hw, mul_pow, Real.norm_eq_abs, sq_abs]
      at h2
    simp only [RCLike.conj_to_real] at h2
    linarith
  set a := inner ℝ v w
  have h3 := key (-a / (‖v‖ ^ 2 + 1))
  have hpos : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have h4 : 0 ≤ a ^ 2 * ‖v‖ ^ 2 - 2 * a ^ 2 * (‖v‖ ^ 2 + 1) := by
    have := mul_nonneg h3 (sq_nonneg (‖v‖ ^ 2 + 1))
    have e : ((-a / (‖v‖ ^ 2 + 1)) ^ 2 * ‖v‖ ^ 2 + 2 * (-a / (‖v‖ ^ 2 + 1)) * a) *
        (‖v‖ ^ 2 + 1) ^ 2 = a ^ 2 * ‖v‖ ^ 2 - 2 * a ^ 2 * (‖v‖ ^ 2 + 1) := by
      field_simp
      ring
    linarith
  nlinarith [sq_nonneg a, sq_nonneg ‖v‖, mul_nonneg (sq_nonneg a) (sq_nonneg ‖v‖)]

theorem ne_of_not_collinear {a b c : Pl} (h : ¬ Collinear ℝ ({a, b, c} : Set Pl)) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h
  · simp [collinear_pair]
  · simp [collinear_pair]
  · have e : ({a, b, a} : Set Pl) = {a, b} := by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact collinear_pair ℝ _ _

/-- The writer's (convex, incircle) bicentric quadrilateral is a repo `IsBicentric` one. -/
theorem isBicentric_of_with {Γ ω : Sphere Pl} {A B C D : Pl} (h : BicentricWith Γ ω A B C D) :
    Fuss.IsBicentric Γ ω A B C D := by
  obtain ⟨⟨-, n1, n2, n3, -⟩, hA, hB, hC, hD, -, t1, t2, t3, t4⟩ := h
  obtain ⟨hAB, hBC, hAC⟩ := ne_of_not_collinear n1
  obtain ⟨-, hCD, hBD⟩ := ne_of_not_collinear n2
  obtain ⟨-, hDA, -⟩ := ne_of_not_collinear n3
  obtain ⟨_, e1⟩ := tangentAt_of_side t1
  obtain ⟨_, e2⟩ := tangentAt_of_side t2
  obtain ⟨_, e3⟩ := tangentAt_of_side t3
  obtain ⟨_, e4⟩ := tangentAt_of_side t4
  exact ⟨hA, hB, hC, hD, hAB, hBC, hCD, hDA, hAC, hBD, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩⟩

/-- Fuss's relation for the writer's bicentric quadrilaterals, given `d ≠ R`. -/
theorem fuss_of_with {Γ ω : Sphere Pl} {A B C D : Pl} (h : BicentricWith Γ ω A B C D)
    (hd : dist Γ.center ω.center ≠ Γ.radius) :
    (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) :=
  Fuss.fuss_of_isBicentric Γ ω h.2.2.2.2.2.1 hd (isBicentric_of_with h)

/-- Algebraic consequences of Fuss's relation (for `0 ≤ x < R`, `r > 0`). -/
theorem fuss_algebra {R r x : ℝ} (hx : 0 ≤ x) (hxR : x < R) (hr : 0 < r)
    (hF : (R ^ 2 - x ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + x ^ 2)) :
    1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 ∧
      (R ^ 2 - x ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + x ^ 2) ∧
      x ^ 2 = R ^ 2 + r ^ 2 - r * Real.sqrt (4 * R ^ 2 + r ^ 2) ∧
      Real.sqrt 2 * r ≤ R ∧
      (R = Real.sqrt 2 * r ↔ x = 0) := by
  have hR : 0 < R := by linarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 4 * R ^ 2 + r ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (4 * R ^ 2 + r ^ 2)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hu : x ^ 2 < R ^ 2 := by nlinarith
  have hroot : R ^ 2 + r ^ 2 - x ^ 2 = r * Real.sqrt (4 * R ^ 2 + r ^ 2) := by
    have e : (R ^ 2 + r ^ 2 - x ^ 2) ^ 2 = (r * Real.sqrt (4 * R ^ 2 + r ^ 2)) ^ 2 := by
      rw [mul_pow, hs]; linear_combination hF
    exact (pow_left_inj₀ (by nlinarith) (by positivity) two_ne_zero).1 e
  have hsq : 2 * r ^ 2 ≤ R ^ 2 := by
    have : r * Real.sqrt (4 * R ^ 2 + r ^ 2) ≤ R ^ 2 + r ^ 2 := by nlinarith
    have h' : (r * Real.sqrt (4 * R ^ 2 + r ^ 2)) ^ 2 ≤ (R ^ 2 + r ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) this 2
    rw [mul_pow, hs] at h'
    nlinarith
  refine ⟨(Fuss.fuss_iff_reciprocal hx hxR hr.ne').1 hF, hF, by linarith, ?_, ?_⟩
  · nlinarith [sq_nonneg (Real.sqrt 2 * r - R)]
  · constructor
    · intro hRe
      have hR2 : R ^ 2 = 2 * r ^ 2 := by rw [hRe, mul_pow, h2]
      have : x ^ 2 * (x ^ 2 - 3 * R ^ 2) = 0 := by linear_combination hF - (R ^ 2 + x ^ 2) * hR2
      rcases mul_eq_zero.1 this with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
      · nlinarith
    · rintro rfl
      have hR2 : R ^ 2 = 2 * r ^ 2 := by
        have : R ^ 2 * (R ^ 2 - 2 * r ^ 2) = 0 := by linear_combination hF
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by positivity))
      have : R ^ 2 = (Real.sqrt 2 * r) ^ 2 := by rw [mul_pow, h2, hR2]
      exact (pow_left_inj₀ hR.le (by positivity) two_ne_zero).1 this

/-! ## CaseyFuss2 (a) -/

/-- (N) Everything in 2(a) except the "square" clause, assuming additionally `x < R`
(the centre of `ω` strictly inside `Γ`), which the repo's theorem needs as `d ≠ R`. -/
theorem cov_CaseyFuss2_a_part (A B C D : Pl) (Γ ω : Sphere Pl)
    (h : BicentricWith Γ ω A B C D) (hdR : dist Γ.center ω.center < Γ.radius) :
    let R := Γ.radius
    let r := ω.radius
    let x := dist Γ.center ω.center
    1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 ∧
      (R ^ 2 - x ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + x ^ 2) ∧
      x ^ 2 = R ^ 2 + r ^ 2 - r * Real.sqrt (4 * R ^ 2 + r ^ 2) ∧
      Real.sqrt 2 * r ≤ R ∧
      (R = Real.sqrt 2 * r ↔ x = 0) :=
  fuss_algebra dist_nonneg hdR h.2.2.2.2.2.1 (fuss_of_with h hdR.ne)

/-! ## CaseyFuss2 (b), 3 (b): repo version with `IsBicentric` in place of `BicentricWith` -/

theorem fuss_of_recip {Γ ω : Sphere Pl} (hin : StrictlyInside ω Γ)
    (hfuss : 1 / (Γ.radius - dist Γ.center ω.center) ^ 2 +
      1 / (Γ.radius + dist Γ.center ω.center) ^ 2 = 1 / ω.radius ^ 2) :
    (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
  obtain ⟨hr, hd⟩ := hin
  rw [dist_comm] at hd
  exact (Fuss.fuss_iff_reciprocal dist_nonneg (by linarith) hr.ne').2 hfuss

/-- (N) 2(b) with the repo's (non-convex, side-line) notion of bicentric quadrilateral. -/
theorem cov_CaseyFuss2_b_part (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ)
    (hfuss : 1 / (Γ.radius - dist Γ.center ω.center) ^ 2 +
      1 / (Γ.radius + dist Γ.center ω.center) ^ 2 = 1 / ω.radius ^ 2) :
    ∃ A B C D : Pl, Fuss.IsBicentric Γ ω A B C D := by
  have hd := hin.2; rw [dist_comm] at hd
  exact (Fuss.fuss_iff_exists Γ ω hin.1 hd).2 (fuss_of_recip hin hfuss)

/-- (N) 3(b): the forward direction exactly; backward direction and the "through every point"
clause with `IsBicentric` in place of `BicentricWith`. -/
theorem cov_CaseyFuss3_b_part (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ) :
    let R := Γ.radius
    let r := ω.radius
    let x := dist Γ.center ω.center
    ((∃ A B C D : Pl, BicentricWith Γ ω A B C D) →
        1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2) ∧
      (1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 →
        ∃ A B C D : Pl, Fuss.IsBicentric Γ ω A B C D) ∧
      (1 / (R - x) ^ 2 + 1 / (R + x) ^ 2 = 1 / r ^ 2 →
        ∀ P ∈ Γ, ∃ B C D : Pl, Fuss.IsBicentric Γ ω P B C D) := by
  intro R r x
  have hd := hin.2; rw [dist_comm] at hd
  refine ⟨?_, cov_CaseyFuss2_b_part Γ ω hin, fun hf P hP =>
    Fuss.exists_bicentric_of_fuss Γ ω hin.1 hd (fuss_of_recip hin hf) hP⟩
  rintro ⟨A, B, C, D, h⟩
  exact (Fuss.fuss_iff_reciprocal dist_nonneg (by linarith [hin.1]) hin.1.ne').1
    (fuss_of_with h (by linarith [hin.1]))

/-! ## CaseyFuss3 (a) -/

/-- A line with exactly one common point with a circle is tangent there (Mathlib sense). -/
theorem tangentAt_of_lineTangent {L : AffineSubspace ℝ Pl} {ω : Sphere Pl}
    (h : LineTangent L ω) : ∃ T, ω.IsTangentAt T L := by
  obtain ⟨T, ⟨hTL, hT⟩, hu⟩ := h
  have hT' : T ∈ ω := EuclideanGeometry.mem_sphere.2 hT
  refine ⟨T, hT', hTL, fun Y hY => ?_⟩
  rw [Sphere.mem_orthRadius_iff_inner_left]
  by_contra hne
  have hZ : ω.secondInter T (Y -ᵥ T) ∈ ω := (Sphere.secondInter_mem _).2 hT'
  have hZL : ω.secondInter T (Y -ᵥ T) ∈ L :=
    affineSpan_pair_le_of_mem_of_mem hTL hY (ω.secondInter_vsub_mem_affineSpan T Y)
  have := hu _ ⟨hZL, EuclideanGeometry.mem_sphere.1 hZ⟩
  exact hne (Sphere.secondInter_eq_self_iff.1 this)

theorem not_collinear_of_mem {Γ : Sphere Pl} {a b c : Pl} (ha : a ∈ Γ) (hb : b ∈ Γ) (hc : c ∈ Γ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ¬ Collinear ℝ ({a, b, c} : Set Pl) := by
  have hs : Cospherical ({a, b, c} : Set Pl) := by
    refine ⟨Γ.center, Γ.radius, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl) <;> assumption
  exact affineIndependent_iff_not_collinear_set.1 (hs.affineIndependent_of_ne hab hac hbc)

/-- Three distinct points of `Γ` are not all on the tangent line to `ω` at `T`. -/
theorem not_three {Γ ω : Sphere Pl} {T a b c : Pl} (hr : 0 < ω.radius) (hT : T ∈ ω)
    (ha : a ∈ Γ) (hb : b ∈ Γ) (hc : c ∈ Γ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha' : a ∈ ω.orthRadius T) (hb' : b ∈ ω.orthRadius T) (hc' : c ∈ ω.orthRadius T) :
    False := by
  have hTc : T ≠ ω.center := Fuss.ne_center hr hT
  have hle : line[ℝ, a, b] ≤ ω.orthRadius T := affineSpan_pair_le_of_mem_of_mem ha' hb'
  have hdir : (line[ℝ, a, b]).direction = (ω.orthRadius T).direction := by
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    have h1 := ω.finrank_orthRadius hTc
    have h2 : Module.finrank ℝ Pl = 2 := Fact.out
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.2 hab)]
    omega
  have heq : line[ℝ, a, b] = ω.orthRadius T :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ⟨a, left_mem_affineSpan_pair _ _ _⟩ hle
  have hcl : c ∈ line[ℝ, a, b] := by rw [heq]; exact hc'
  apply not_collinear_of_mem hc ha hb hac.symm hbc.symm hab
  exact collinear_insert_of_mem_affineSpan_pair hcl

/-- (N) 3(a), with `IsBicentric` in place of `BicentricWith` in the three conclusions
(the hypothesis `hex` is the writer's, with `BicentricWith`). -/
theorem cov_CaseyFuss3_a_part (Γ ω : Sphere Pl) (hin : StrictlyInside ω Γ)
    (hex : ∃ A B C D : Pl, BicentricWith Γ ω A B C D) :
    (∀ P ∈ Γ, ∃ B C D : Pl, Fuss.IsBicentric Γ ω P B C D) ∧
      (∀ P ∈ Γ, ∀ p : ℕ → Pl, p 0 = P → (∀ n, p n ∈ Γ) → (∀ n, p n ≠ p (n + 1)) →
        (∀ n, LineTangent line[ℝ, p n, p (n + 1)] ω) → (∀ n, p (n + 2) ≠ p n) →
        p 4 = p 0 ∧ p 3 ≠ p 0 ∧
          Fuss.IsBicentric Γ ω (p 0) (p 1) (p 2) (p 3)) ∧
      {q : Fin 4 → Pl | Fuss.IsBicentric Γ ω (q 0) (q 1) (q 2) (q 3)}.Infinite := by
  obtain ⟨hr, hd⟩ := hin
  rw [dist_comm] at hd
  obtain ⟨A, B, C, D, hw⟩ := hex
  have hF := fuss_of_with hw (by linarith)
  have hall : ∀ P ∈ Γ, ∃ B C D : Pl, Fuss.IsBicentric Γ ω P B C D :=
    fun P hP => Fuss.exists_bicentric_of_fuss Γ ω hr hd hF hP
  refine ⟨hall, ?_, ?_⟩
  · intro P hP p hp0 hpΓ hpn htan hback
    choose T hT using fun n => tangentAt_of_lineTangent (htan n)
    have o1 : ∀ n, p n ∈ ω.orthRadius (T n) := fun n =>
      (hT n).le_orthRadius (left_mem_affineSpan_pair ℝ _ _)
    have o2 : ∀ n, p (n + 1) ∈ ω.orthRadius (T n) := fun n =>
      (hT n).le_orthRadius (right_mem_affineSpan_pair ℝ _ _)
    have hTn : ∀ n, T n ≠ T (n + 1) := by
      intro n e
      have h3 := o1 (n + 1); rw [← e] at h3
      have h4 := o2 (n + 1); rw [← e] at h4
      exact not_three hr (hT n).mem_sphere (hpΓ n) (hpΓ (n + 1)) (hpΓ (n + 2)) (hpn n)
        (hback n).symm (hpn (n + 1)) (o1 n) h3 h4
    obtain ⟨e5, e4⟩ := Fuss.poncelet_chain_closes Γ ω hr (by linarith) hF
      (hpΓ 1) (hpΓ 2) (hpΓ 3) (hpΓ 4) (hpΓ 5)
      (hT 0).mem_sphere (hT 1).mem_sphere (hT 2).mem_sphere (hT 3).mem_sphere (hT 4).mem_sphere
      (o2 0) (o1 1) (o2 1) (o1 2) (o2 2) (o1 3) (o2 3) (o1 4) (o2 4)
      (hTn 0) (hTn 1) (hTn 2) (hTn 3) (hpn 1) (hpn 2) (hpn 3) (hpn 4)
    have h40 : p 4 = p 0 := by
      by_contra hne
      have a4 := o1 4; rw [e4] at a4
      have a5 := o2 4; rw [e4, e5] at a5
      exact not_three hr (hT 0).mem_sphere (hpΓ 4) (hpΓ 1) (hpΓ 0)
        (by rw [← e5]; exact hpn 4) hne (hpn 0).symm a4 a5 (o1 0)
    have h30 : p 3 ≠ p 0 := by rw [← h40]; exact hpn 3
    refine ⟨h40, h30, hpΓ 0, hpΓ 1, hpΓ 2, hpΓ 3, hpn 0, hpn 1, hpn 2, h30, (hback 0).symm,
      (hback 1).symm, ⟨_, hT 0⟩, ⟨_, hT 1⟩, ⟨_, hT 2⟩, ?_⟩
    have := hT 3; rw [show (3 + 1 : ℕ) = 4 from rfl, h40] at this
    exact ⟨_, this⟩
  · -- the circle `Γ` is infinite, and every point of it is the first vertex of a quadrilateral
    have hR : 0 < Γ.radius := by linarith [dist_nonneg (x := Γ.center) (y := ω.center)]
    have hinf : (Metric.sphere Γ.center Γ.radius).Infinite := by
      intro hfin
      have hrank : 1 < Module.rank ℝ Pl := by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
      have hconn := isConnected_sphere hrank Γ.center hR.le
      have hsub := hfin.countable.isTotallyDisconnected _ subset_rfl hconn.isPreconnected
      set e : Pl := EuclideanSpace.single 0 Γ.radius
      have he : ‖e‖ = Γ.radius := by
        rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hR]
      have m1 : Γ.center + e ∈ Metric.sphere Γ.center Γ.radius := by
        rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, he]
      have m2 : Γ.center - e ∈ Metric.sphere Γ.center Γ.radius := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_sub_cancel_left, norm_neg, he]
      have := hsub m1 m2
      have h0 : e = 0 := by
        have : (2 : ℝ) • e = 0 := by
          rw [two_smul]; linear_combination (norm := abel_nf) this
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
      rw [h0, norm_zero] at he
      linarith
    apply Set.Infinite.of_image (fun q : Fin 4 → Pl => q 0)
    apply hinf.mono
    intro P hP
    obtain ⟨B, C, D, hq⟩ := hall P (EuclideanGeometry.mem_sphere.2 hP)
    exact ⟨![P, B, C, D], hq, rfl⟩

end Fuss.Classical
