import Mathlib

/-!
# Vector lemmas in a Euclidean plane

`V` is a real inner product space of dimension 2.  Main tool: two vectors orthogonal to the same
nonzero vector are parallel (`parallel_of_inner_eq_zero`).  Consequences used for Fuss's theorem:

* `eq_or_eq_or_eq_of_inner`: a line meets a circle in at most two points;
* `vertex_smul`: the intersection `v` of the tangents to the circle `‖x‖ = r` at `x ≠ y` satisfies
  `(r² + ⟪x, y⟫) v = r² (x + y)`;
* `tangent_points`: a point lies on at most two tangents of a circle.
-/

open scoped RealInnerProductSpace

namespace Fuss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In a plane, two vectors orthogonal to the same nonzero vector are parallel. -/
lemma parallel_of_inner_eq_zero [Fact (Module.finrank ℝ V = 2)] {e a b : V} (he : e ≠ 0)
    (ha : ⟪a, e⟫ = 0) (hb : ⟪b, e⟫ = 0) : ‖a‖ ^ 2 • b = ⟪a, b⟫ • a := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let o : Orientation ℝ V (Fin 2) := (Module.finBasisOfFinrankEq ℝ V Fact.out).orientation
  have ha' : ⟪e, a⟫ = 0 := by rw [real_inner_comm]; exact ha
  have hb' : ⟪e, b⟫ = 0 := by rw [real_inner_comm]; exact hb
  have he2 : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 he)
  have h1 := o.inner_mul_areaForm_sub e a b
  rw [ha', hb', zero_mul, mul_zero, sub_zero] at h1
  have hab : o.areaForm a b = 0 := (mul_eq_zero.1 h1.symm).resolve_left he2
  set z := ‖a‖ ^ 2 • b - ⟪a, b⟫ • a with hz
  have hz1 : ⟪a, z⟫ = 0 := by
    rw [hz, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hz2 : o.areaForm a z = 0 := by
    simp only [hz, map_sub, map_smul, smul_eq_mul, hab, o.areaForm_apply_self, mul_zero,
      sub_zero]
  by_cases ha0 : a = 0
  · subst ha0; simp
  have h3 := o.inner_sq_add_areaForm_sq a z
  rw [hz1, hz2] at h3
  have hpos : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 ha0)
  have h4 : ‖a‖ ^ 2 * ‖z‖ ^ 2 = 0 := by rw [← h3]; ring
  have h5 : ‖z‖ ^ 2 = 0 := (mul_eq_zero.1 h4).resolve_left hpos
  have h6 : z = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h5)
  exact sub_eq_zero.1 h6

/-- In a plane, a line (normal `n ≠ 0`) meets a circle (centre `c`) in at most two points. -/
lemma eq_or_eq_or_eq_of_inner [Fact (Module.finrank ℝ V = 2)] {n c a b d : V} (hn : n ≠ 0)
    (hab : ⟪a - b, n⟫ = 0) (had : ⟪a - d, n⟫ = 0)
    (hb : ‖b - c‖ ^ 2 = ‖a - c‖ ^ 2) (hd : ‖d - c‖ ^ 2 = ‖a - c‖ ^ 2) :
    a = b ∨ a = d ∨ b = d := by
  have h := parallel_of_inner_eq_zero hn hab had
  have hbw : b - c = (a - c) - (a - b) := by abel
  have hdw : d - c = (a - c) - (a - d) := by abel
  rw [hbw, norm_sub_sq_real] at hb
  rw [hdw, norm_sub_sq_real] at hd
  have e1 := congrArg (fun z => ⟪a - c, z⟫) h
  have e2 := congrArg (fun z => ⟪a - d, z⟫) h
  simp only [real_inner_smul_right] at e1 e2
  rw [real_inner_self_eq_norm_sq, real_inner_comm (a - b) (a - d)] at e2
  by_cases hp0 : a - b = 0
  · exact Or.inl (sub_eq_zero.1 hp0)
  by_cases hq0 : a - d = 0
  · exact Or.inr (Or.inl (sub_eq_zero.1 hq0))
  right; right
  have hP : ‖a - b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hp0)
  have hQ : ‖a - d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hq0)
  have k1 : ‖a - b‖ ^ 2 * (‖a - d‖ ^ 2 - ⟪a - b, a - d⟫) = 0 := by
    linear_combination (‖a - b‖ ^ 2) * hd + 2 * e1 - ⟪a - b, a - d⟫ * hb
  have k1' : ‖a - d‖ ^ 2 = ⟪a - b, a - d⟫ := sub_eq_zero.1 ((mul_eq_zero.1 k1).resolve_left hP)
  have k2 : ‖a - d‖ ^ 2 * (‖a - b‖ ^ 2 - ‖a - d‖ ^ 2) = 0 := by
    linear_combination e2 - (⟪a - b, a - d⟫ + ‖a - d‖ ^ 2) * k1'
  have k2' : ‖a - b‖ ^ 2 = ‖a - d‖ ^ 2 := sub_eq_zero.1 ((mul_eq_zero.1 k2).resolve_left hQ)
  have k3 : ‖(a - b) - (a - d)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real]; linear_combination k2' + 2 * k1'
  have k4 : (a - b) - (a - d) = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 k3)
  exact sub_right_injective (sub_eq_zero.1 k4)

/-- The intersection `v` of the tangents at `x ≠ y` to the circle `‖·‖ = r` (centre `0`). -/
lemma vertex_smul [Fact (Module.finrank ℝ V = 2)] {x y v : V} {r : ℝ}
    (hx : ‖x‖ ^ 2 = r ^ 2) (hy : ‖y‖ ^ 2 = r ^ 2) (hxy : x ≠ y)
    (hvx : ⟪v, x⟫ = r ^ 2) (hvy : ⟪v, y⟫ = r ^ 2) :
    (r ^ 2 + ⟪x, y⟫) • v = r ^ 2 • (x + y) := by
  have he : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h1 : ⟪x + y, x - y⟫ = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm x y, hx, hy]
    ring
  have h2 : ⟪v, x - y⟫ = 0 := by rw [inner_sub_right, hvx, hvy, sub_self]
  have h := parallel_of_inner_eq_zero he h1 h2
  have hn : ‖x + y‖ ^ 2 = 2 * (r ^ 2 + ⟪x, y⟫) := by
    rw [norm_add_sq_real, hx, hy]; ring
  have hi : ⟪x + y, v⟫ = 2 * r ^ 2 := by
    rw [inner_add_left, real_inner_comm v x, real_inner_comm v y, hvx, hvy]; ring
  rw [hn, hi, mul_smul, mul_smul] at h
  exact smul_right_injective V two_ne_zero h

/-- The two tangents at `x ≠ y` are not parallel: `r² + ⟪x, y⟫ ≠ 0`. -/
lemma vertex_denom_ne [Fact (Module.finrank ℝ V = 2)] {x y v : V} {r : ℝ} (hr : r ≠ 0)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hy : ‖y‖ ^ 2 = r ^ 2) (hxy : x ≠ y)
    (hvx : ⟪v, x⟫ = r ^ 2) (hvy : ⟪v, y⟫ = r ^ 2) : r ^ 2 + ⟪x, y⟫ ≠ 0 := by
  intro h0
  have h := vertex_smul hx hy hxy hvx hvy
  rw [h0, zero_smul] at h
  have hxy0 : x + y = 0 := (smul_eq_zero.1 h.symm).resolve_left (pow_ne_zero 2 hr)
  have hy' : y = -x := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact hxy0)
  rw [hy', inner_neg_right, hvx] at hvy
  have : r ^ 2 = 0 := by linarith
  exact pow_ne_zero 2 hr this

/-- A point lies on at most two tangents of a circle of nonzero radius (centre `0`). -/
lemma tangent_points [Fact (Module.finrank ℝ V = 2)] {v x y z : V} {r : ℝ} (hr : r ≠ 0)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hy : ‖y‖ ^ 2 = r ^ 2) (hz : ‖z‖ ^ 2 = r ^ 2)
    (hvx : ⟪v, x⟫ = r ^ 2) (hvy : ⟪v, y⟫ = r ^ 2) (hvz : ⟪v, z⟫ = r ^ 2) :
    x = y ∨ x = z ∨ y = z := by
  have hv : v ≠ 0 := by
    rintro rfl; rw [inner_zero_left] at hvx; exact pow_ne_zero 2 hr hvx.symm
  refine eq_or_eq_or_eq_of_inner (c := 0) hv ?_ ?_ ?_ ?_
  · rw [real_inner_comm, inner_sub_right, hvx, hvy, sub_self]
  · rw [real_inner_comm, inner_sub_right, hvx, hvz, sub_self]
  · rw [sub_zero, sub_zero, hy, hx]
  · rw [sub_zero, sub_zero, hz, hx]

/-- A tangent line (at `x ≠ 0`) meets a circle (centre `c`) in at most two points. -/
lemma line_points [Fact (Module.finrank ℝ V = 2)] {c x a b d : V} {t : ℝ} (hx : x ≠ 0)
    (ha : ⟪a, x⟫ = t) (hb : ⟪b, x⟫ = t) (hd : ⟪d, x⟫ = t)
    (hb' : ‖b - c‖ ^ 2 = ‖a - c‖ ^ 2) (hd' : ‖d - c‖ ^ 2 = ‖a - c‖ ^ 2) :
    a = b ∨ a = d ∨ b = d :=
  eq_or_eq_or_eq_of_inner hx (by rw [inner_sub_left, ha, hb, sub_self])
    (by rw [inner_sub_left, ha, hd, sub_self]) hb' hd'

end Fuss
