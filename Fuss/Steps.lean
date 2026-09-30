import Fuss.Porism

/-!
# The steps of the Poncelet construction can be performed (vector form)

Vectors relative to the centre of `ω` (radius `r > 0`); `Γ` has centre `o` and radius `R`, and
`ω` lies strictly inside `Γ`: `‖o‖ + r < R`.

* `first_tangent`: from a point `a` outside `ω` there is a tangent (needs dimension 2);
* `other_tangent`: given one tangent from `a` (at `x`), the reflection of `x` in the line `0a`
  gives a second, different one;
* `second_point`: a line through `a ∈ Γ` and a point `x` strictly inside `Γ` meets `Γ` again at a
  point `b ≠ a`.
-/

open scoped RealInnerProductSpace

namespace Fuss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/-- A point of `Γ` lies outside `ω`. -/
lemma outside_of_mem {o a : V} {r R : ℝ} (hr : 0 < r) (hin : ‖o‖ + r < R)
    (ha : ‖a - o‖ ^ 2 = R ^ 2) : r ^ 2 < ‖a‖ ^ 2 := by
  have hR : 0 < R := by linarith [norm_nonneg o]
  have h1 : ‖a - o‖ = R := (pow_left_inj₀ (norm_nonneg _) hR.le two_ne_zero).1 ha
  have h2 := norm_sub_le a o
  have h3 : r < ‖a‖ := by linarith
  nlinarith

omit [InnerProductSpace ℝ V] in
/-- A point of `ω` lies strictly inside `Γ`. -/
lemma inside_of_mem {o x : V} {r R : ℝ} (hr : 0 < r) (hin : ‖o‖ + r < R)
    (hx : ‖x‖ ^ 2 = r ^ 2) : ‖x - o‖ ^ 2 < R ^ 2 := by
  have h1 : ‖x‖ = r := (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).1 hx
  have h2 := norm_sub_le x o
  have h3 : ‖x - o‖ < R := by linarith
  nlinarith [norm_nonneg (x - o)]

/-- From a point outside `ω` there is a tangent to `ω`. -/
lemma first_tangent [Fact (Module.finrank ℝ V = 2)] {a : V} {r : ℝ}
    (ha : r ^ 2 < ‖a‖ ^ 2) : ∃ x : V, ‖x‖ ^ 2 = r ^ 2 ∧ ⟪a, x⟫ = r ^ 2 := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let o : Orientation ℝ V (Fin 2) := (Module.finBasisOfFinrankEq ℝ V Fact.out).orientation
  set J := o.rightAngleRotation with hJ
  set p := ‖a‖ ^ 2 with hp
  have hp0 : 0 < p := by nlinarith [sq_nonneg r]
  set q := p⁻¹ with hqdef
  have hq : p * q = 1 := mul_inv_cancel₀ hp0.ne'
  set s := Real.sqrt (p - r ^ 2) with hsdef
  have hs : s ^ 2 = p - r ^ 2 := Real.sq_sqrt (by linarith)
  have hJa : ⟪a, J a⟫ = 0 := by rw [real_inner_comm]; exact o.inner_rightAngleRotation_self a
  have hJn : ‖J a‖ ^ 2 = p := by rw [hJ, LinearIsometryEquiv.norm_map]
  refine ⟨(r ^ 2 * q) • a + (r * s * q) • J a, ?_, ?_⟩
  · rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow,
      mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, hJa, hJn, ← hp]
    linear_combination (p * q ^ 2 * r ^ 2) * hs + (p * q * r ^ 2 + r ^ 2) * hq
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hJa,
      real_inner_self_eq_norm_sq, ← hp]
    linear_combination r ^ 2 * hq

/-- The other tangent from `a`: reflect the tangency point `x` in the line `0a`. -/
lemma other_tangent {a x : V} {r : ℝ} (hr : 0 < r) (ha : r ^ 2 < ‖a‖ ^ 2)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hax : ⟪a, x⟫ = r ^ 2) :
    ∃ x' : V, ‖x'‖ ^ 2 = r ^ 2 ∧ ⟪a, x'⟫ = r ^ 2 ∧ x ≠ x' := by
  set p := ‖a‖ ^ 2 with hp
  have hp0 : 0 < p := by nlinarith
  set q := p⁻¹ with hqdef
  have hq : p * q = 1 := mul_inv_cancel₀ hp0.ne'
  refine ⟨(2 * r ^ 2 * q) • a - x, ?_, ?_, ?_⟩
  · rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
      hax, hx, ← hp]
    linear_combination (4 * r ^ 4 * q) * hq
  · rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hax, ← hp]
    linear_combination (2 * r ^ 2) * hq
  · intro h
    have e := congrArg (fun z => ⟪x, z⟫) h
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm a x,
      hax, hx] at e
    have e2 : r ^ 2 * (p - r ^ 2) = 0 := by linear_combination (p / 2) * e + r ^ 4 * hq
    have := mul_pos (pow_pos hr 2) (sub_pos.2 ha)
    linarith

/-- The line through a point `a` of `Γ` and a point `x` strictly inside `Γ` meets `Γ` in a second
point `b ≠ a`; if `x` is a tangency point of a tangent through `a`, so is it for `b`. -/
lemma second_point {o a x : V} {r R : ℝ} (ha : ‖a - o‖ ^ 2 = R ^ 2)
    (hx : ‖x - o‖ ^ 2 < R ^ 2) (hxr : ‖x‖ ^ 2 = r ^ 2) (hax : ⟪a, x⟫ = r ^ 2) :
    ∃ b : V, ‖b - o‖ ^ 2 = R ^ 2 ∧ ⟪b, x⟫ = r ^ 2 ∧ a ≠ b := by
  set w := x - a with hw
  set g := ⟪a - o, w⟫ with hg
  have hxw : x - o = (a - o) + w := by rw [hw]; abel
  rw [hxw, norm_add_sq_real, ha, ← hg] at hx
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; rw [hg, h, inner_zero_right] at hx; linarith
  have hn0 : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hw0)
  have hg0 : g < 0 := by nlinarith [sq_nonneg ‖w‖]
  set t := -2 * g / ‖w‖ ^ 2 with ht
  have htn : t * ‖w‖ ^ 2 = -2 * g := by rw [ht]; field_simp
  refine ⟨a + t • w, ?_, ?_, ?_⟩
  · have e : a + t • w - o = (a - o) + t • w := by abel
    rw [e, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
      ha, ← hg]
    linear_combination t * htn
  · rw [inner_add_left, real_inner_smul_left, hw, inner_sub_left, real_inner_self_eq_norm_sq,
      hxr, hax]
    ring
  · intro h
    have h' : t • w = 0 := by
      have := congrArg (fun z => z - a) h
      simp only [sub_self, add_sub_cancel_left] at this
      exact this.symm
    rcases smul_eq_zero.1 h' with h0 | h0
    · rw [h0, zero_mul] at htn; linarith
    · exact hw0 h0

/-- **One step of the construction.**  At a vertex `a ∈ Γ` reached along the tangent at `x`, take
the other tangent (at `x' ≠ x`) and its second intersection `b ≠ a` with `Γ`. -/
lemma step {o a x : V} {r R : ℝ} (hr : 0 < r) (hin : ‖o‖ + r < R)
    (ha : ‖a - o‖ ^ 2 = R ^ 2) (hx : ‖x‖ ^ 2 = r ^ 2) (hax : ⟪a, x⟫ = r ^ 2) :
    ∃ x' b : V, ‖x'‖ ^ 2 = r ^ 2 ∧ ⟪a, x'⟫ = r ^ 2 ∧ x ≠ x' ∧
      ‖b - o‖ ^ 2 = R ^ 2 ∧ ⟪b, x'⟫ = r ^ 2 ∧ a ≠ b := by
  obtain ⟨x', h1, h2, h3⟩ := other_tangent hr (outside_of_mem hr hin ha) hx hax
  obtain ⟨b, h4, h5, h6⟩ := second_point ha (inside_of_mem hr hin h1) h1 h2
  exact ⟨x', b, h1, h2, h3, h4, h5, h6⟩

end Fuss
