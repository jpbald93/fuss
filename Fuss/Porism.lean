import Fuss.Forward

/-!
# Poncelet's porism for quadrilaterals (vector form)

Vectors relative to the centre of `ω` (radius `r`); `Γ` has centre `o`, radius `R`;
`k = R² - ‖o‖² ≠ 0`.  Under Fuss's relation `k² = 2 r² (R² + ‖o‖²)`, the shifted tangency points
`k x + 2 r² o` of consecutive sides are orthogonal (`Fuss.vertex_rel`), and this forces every
4-step tangent chain to close (`closes_vec`).

`step_other`, `step_second`, `first_tangent` show that when `ω` lies strictly inside `Γ`
(`‖o‖ + r < R`) each step of the construction can be performed.
-/

open scoped RealInnerProductSpace

namespace Fuss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Two points on the same two distinct tangents coincide. -/
lemma vertex_unique [Fact (Module.finrank ℝ V = 2)] {x x' a b : V} {r : ℝ} (hr : r ≠ 0)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hx' : ‖x'‖ ^ 2 = r ^ 2) (hne : x ≠ x')
    (hax : ⟪a, x⟫ = r ^ 2) (hax' : ⟪a, x'⟫ = r ^ 2) (hbx : ⟪b, x⟫ = r ^ 2)
    (hbx' : ⟪b, x'⟫ = r ^ 2) : a = b :=
  smul_right_injective V (vertex_denom_ne hr hx hx' hne hax hax')
    ((vertex_smul hx hx' hne hax hax').trans (vertex_smul hx hx' hne hbx hbx').symm)

/-- Distinctness of the vertices of a tangent chain `a₀ a₁ a₂ a₃` (no Fuss relation needed):
`a₀ ≠ a₂` and `a₁ ≠ a₃`. -/
lemma chain_distinct [Fact (Module.finrank ℝ V = 2)] {a₀ a₁ a₂ a₃ x₀ x₁ x₂ x₃ : V} {r : ℝ}
    (hr : r ≠ 0) (h₀ : ‖x₀‖ ^ 2 = r ^ 2) (h₁ : ‖x₁‖ ^ 2 = r ^ 2) (h₂ : ‖x₂‖ ^ 2 = r ^ 2)
    (h₃ : ‖x₃‖ ^ 2 = r ^ 2)
    (h00 : ⟪a₀, x₀⟫ = r ^ 2) (h01 : ⟪a₀, x₁⟫ = r ^ 2) (h11 : ⟪a₁, x₁⟫ = r ^ 2)
    (h12 : ⟪a₁, x₂⟫ = r ^ 2) (h22 : ⟪a₂, x₂⟫ = r ^ 2) (h23 : ⟪a₂, x₃⟫ = r ^ 2)
    (h33 : ⟪a₃, x₃⟫ = r ^ 2)
    (n01 : x₀ ≠ x₁) (n12 : x₁ ≠ x₂) (n23 : x₂ ≠ x₃)
    (m01 : a₀ ≠ a₁) (m12 : a₁ ≠ a₂) : a₀ ≠ a₂ ∧ a₁ ≠ a₃ := by
  constructor
  · intro h
    rw [← h] at h22 h23
    rcases tangent_points hr h₀ h₁ h₂ h00 h01 h22 with e | e | e
    · exact n01 e
    · subst e
      exact m01 (vertex_unique hr h₁ h₂ n12 h01 h00 h11 h12)
    · exact n12 e
  · intro h
    rw [← h] at h33
    rcases tangent_points hr h₁ h₂ h₃ h11 h12 h33 with e | e | e
    · exact n12 e
    · subst e
      exact m12 (vertex_unique hr h₂ h₁ n12.symm h12 h11 h22 h23)
    · exact n23 e

/-- **Poncelet's porism for quadrilaterals, vector form.**  Under Fuss's relation, any tangent
chain `a₀ → a₁ → a₂ → a₃ → a₄` (each `aᵢ` on `Γ`, consecutive sides tangent to `ω` at
`x₁, …, x₄`, always taking the *other* tangent and the *other* intersection point) closes:
`a₄ = a₀`, and the last tangent is the other tangent `x₀` from `a₀`. -/
theorem closes_vec [Fact (Module.finrank ℝ V = 2)]
    {o a₀ a₁ a₂ a₃ a₄ x₀ x₁ x₂ x₃ x₄ : V} {r R : ℝ} (hr : r ≠ 0) (hk : R ^ 2 - ‖o‖ ^ 2 ≠ 0)
    (hF : (R ^ 2 - ‖o‖ ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2))
    (ha₀ : ‖a₀ - o‖ ^ 2 = R ^ 2) (ha₁ : ‖a₁ - o‖ ^ 2 = R ^ 2) (ha₂ : ‖a₂ - o‖ ^ 2 = R ^ 2)
    (ha₃ : ‖a₃ - o‖ ^ 2 = R ^ 2) (ha₄ : ‖a₄ - o‖ ^ 2 = R ^ 2)
    (h₀ : ‖x₀‖ ^ 2 = r ^ 2) (h₁ : ‖x₁‖ ^ 2 = r ^ 2) (h₂ : ‖x₂‖ ^ 2 = r ^ 2)
    (h₃ : ‖x₃‖ ^ 2 = r ^ 2) (h₄ : ‖x₄‖ ^ 2 = r ^ 2)
    (h00 : ⟪a₀, x₀⟫ = r ^ 2) (h01 : ⟪a₀, x₁⟫ = r ^ 2) (h11 : ⟪a₁, x₁⟫ = r ^ 2)
    (h12 : ⟪a₁, x₂⟫ = r ^ 2) (h22 : ⟪a₂, x₂⟫ = r ^ 2) (h23 : ⟪a₂, x₃⟫ = r ^ 2)
    (h33 : ⟪a₃, x₃⟫ = r ^ 2) (h34 : ⟪a₃, x₄⟫ = r ^ 2) (h44 : ⟪a₄, x₄⟫ = r ^ 2)
    (n01 : x₀ ≠ x₁) (n12 : x₁ ≠ x₂) (n23 : x₂ ≠ x₃) (n34 : x₃ ≠ x₄)
    (m01 : a₀ ≠ a₁) (m12 : a₁ ≠ a₂) (m23 : a₂ ≠ a₃) (m34 : a₃ ≠ a₄) :
    a₄ = a₀ ∧ x₄ = x₀ := by
  set k := R ^ 2 - ‖o‖ ^ 2 with hkdef
  set F := k ^ 2 - 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2) with hFdef
  have hF0 : F = 0 := sub_eq_zero.2 hF
  set y₀ := k • x₀ + (2 * r ^ 2) • o
  set y₁ := k • x₁ + (2 * r ^ 2) • o
  set y₂ := k • x₂ + (2 * r ^ 2) • o
  set y₃ := k • x₃ + (2 * r ^ 2) • o
  set y₄ := k • x₄ + (2 * r ^ 2) • o
  have r01 : ⟪y₀, y₁⟫ = 0 := by
    have e : ⟪y₀, y₁⟫ = -(r ^ 2 * F) := vertex_rel hr h₀ h₁ n01 h00 h01 ha₀
    rw [e, hF0, mul_zero, neg_zero]
  have r12 : ⟪y₁, y₂⟫ = 0 := by
    have e : ⟪y₁, y₂⟫ = -(r ^ 2 * F) := vertex_rel hr h₁ h₂ n12 h11 h12 ha₁
    rw [e, hF0, mul_zero, neg_zero]
  have r23 : ⟪y₂, y₃⟫ = 0 := by
    have e : ⟪y₂, y₃⟫ = -(r ^ 2 * F) := vertex_rel hr h₂ h₃ n23 h22 h23 ha₂
    rw [e, hF0, mul_zero, neg_zero]
  have r34 : ⟪y₃, y₄⟫ = 0 := by
    have e : ⟪y₃, y₄⟫ = -(r ^ 2 * F) := vertex_rel hr h₃ h₄ n34 h33 h34 ha₃
    rw [e, hF0, mul_zero, neg_zero]
  have hyinj : ∀ {x x' : V}, k • x + (2 * r ^ 2) • o = k • x' + (2 * r ^ 2) • o → x = x' :=
    fun h => smul_right_injective V hk (add_right_cancel h)
  -- shifted points are nonzero
  have hy0 : ∀ {x : V}, ‖x‖ ^ 2 = r ^ 2 → k • x + (2 * r ^ 2) • o ≠ 0 := by
    intro x hx h
    have e : k • x = -((2 * r ^ 2) • o) := eq_neg_of_add_eq_zero_left h
    have e2 := congrArg (fun z => ‖z‖ ^ 2) e
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs, hx] at e2
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have e3 : k ^ 2 = 4 * r ^ 2 * ‖o‖ ^ 2 := by
      have : r ^ 2 * (k ^ 2 - 4 * r ^ 2 * ‖o‖ ^ 2) = 0 := by linear_combination e2
      linear_combination (mul_eq_zero.1 this).resolve_left hr2
    have e4 : r ^ 2 * k = 0 := by linear_combination (-1 / 2 : ℝ) * (hF - e3) + r ^ 2 * hkdef
    exact hk ((mul_eq_zero.1 e4).resolve_left hr2)
  have hsq : ∀ {x : V}, ‖x‖ ^ 2 = r ^ 2 →
      ‖(k • x + (2 * r ^ 2) • o) - (2 * r ^ 2) • o‖ ^ 2 = k ^ 2 * r ^ 2 := by
    intro x hx
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hx]
  -- x₀ ≠ x₂ and x₂ ≠ x₄
  have n02 : x₀ ≠ x₂ := by
    intro e; rw [e] at h00
    exact m01 (vertex_unique hr h₁ h₂ n12 h01 h00 h11 h12)
  have n24 : x₂ ≠ x₄ := by
    intro e; rw [← e] at h34
    exact m23 (vertex_unique hr h₂ h₃ n23 h22 h23 h34 h33)
  -- y₁ ∥ y₃, hence y₀ ⊥ y₃
  have hpar := parallel_of_inner_eq_zero (hy0 h₂) r12 ((real_inner_comm y₂ y₃).trans r23)
  have e03 : ⟪y₀, y₃⟫ = 0 := by
    have := congrArg (fun z => ⟪y₀, z⟫) hpar
    simp only [real_inner_smul_right] at this
    rw [r01, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.2 (hy0 h₁)))
  have s0 : ‖y₀ - (2 * r ^ 2) • o‖ ^ 2 = k ^ 2 * r ^ 2 := hsq h₀
  have s2 : ‖y₂ - (2 * r ^ 2) • o‖ ^ 2 = k ^ 2 * r ^ 2 := hsq h₂
  have s4 : ‖y₄ - (2 * r ^ 2) • o‖ ^ 2 = k ^ 2 * r ^ 2 := hsq h₄
  have hc := eq_or_eq_or_eq_of_inner (c := (2 * r ^ 2) • o) (a := y₀) (b := y₂) (d := y₄)
    (hy0 h₃) (by rw [inner_sub_left, e03, r23, sub_zero])
    (by rw [inner_sub_left, e03, real_inner_comm y₃ y₄, r34, sub_zero])
    (s2.trans s0.symm) (s4.trans s0.symm)
  have hx40 : x₄ = x₀ := by
    rcases hc with e | e | e
    · exact absurd (hyinj e) n02
    · exact (hyinj e).symm
    · exact absurd (hyinj e) n24
  refine ⟨?_, hx40⟩
  -- a₀, a₃, a₄ lie on the tangent at x₄ = x₀
  have hx4 : x₄ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h₄
    exact pow_ne_zero 2 hr (by linear_combination -h₄)
  have h04 : ⟪a₀, x₄⟫ = r ^ 2 := by rw [hx40]; exact h00
  rcases line_points (c := o) hx4 h04 h34 h44 (by rw [ha₃, ha₀]) (by rw [ha₄, ha₀]) with
    e | e | e
  · exfalso
    rw [← e] at h33
    rcases tangent_points hr h₀ h₁ h₃ h00 h01 h33 with f | f | f
    · exact n01 f
    · exact n34 (f.symm.trans hx40.symm)
    · rw [← f] at h23
      exact m12 (vertex_unique hr h₁ h₂ n12 h11 h12 h23 h22)
  · exact e.symm
  · exact absurd e m34

end Fuss
