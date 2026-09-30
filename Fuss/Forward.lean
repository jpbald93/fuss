import Fuss.Plane

/-!
# Fuss's theorem: a bicentric quadrilateral satisfies Fuss's relation

Vectors are taken relative to the centre `I` of `ω`; `o = O - I`, `k = R² - ‖o‖²`.
For tangency points `x`, `y` of `ω` whose tangents meet at a point `a` of `Γ`, the shifted vectors
`k x + 2r² o`, `k y + 2r² o` have inner product `-r² F`, where
`F = k² - 2 r² (R² + ‖o‖²)` (`vertex_rel`).  For a quadrilateral the four shifted tangency points
then have equal consecutive inner products, which in a plane forces `F = 0`.
-/

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace Fuss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The shifted tangency points of the two tangents from a point `a` of `Γ`. -/
lemma vertex_rel [Fact (Module.finrank ℝ V = 2)] {x y a o : V} {r R : ℝ} (hr : r ≠ 0)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hy : ‖y‖ ^ 2 = r ^ 2) (hxy : x ≠ y)
    (hax : ⟪a, x⟫ = r ^ 2) (hay : ⟪a, y⟫ = r ^ 2) (ha : ‖a - o‖ ^ 2 = R ^ 2) :
    ⟪(R ^ 2 - ‖o‖ ^ 2) • x + (2 * r ^ 2) • o, (R ^ 2 - ‖o‖ ^ 2) • y + (2 * r ^ 2) • o⟫ =
      -(r ^ 2 * ((R ^ 2 - ‖o‖ ^ 2) ^ 2 - 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2))) := by
  have hs0 := vertex_denom_ne hr hx hy hxy hax hay
  have hs := vertex_smul hx hy hxy hax hay
  have h1 : (r ^ 2 + ⟪x, y⟫) ^ 2 * ‖a‖ ^ 2 = 2 * r ^ 4 * (r ^ 2 + ⟪x, y⟫) := by
    have e1 : ⟪(r ^ 2 + ⟪x, y⟫) • a, (r ^ 2 + ⟪x, y⟫) • a⟫ = (r ^ 2 + ⟪x, y⟫) ^ 2 * ‖a‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    have e2 : ⟪r ^ 2 • (x + y), r ^ 2 • (x + y)⟫ = 2 * r ^ 4 * (r ^ 2 + ⟪x, y⟫) := by
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_add_sq_real,
        hx, hy]; ring
    rw [← e1, ← e2, hs]
  have h2 : (r ^ 2 + ⟪x, y⟫) * ⟪a, o⟫ = r ^ 2 * (⟪x, o⟫ + ⟪y, o⟫) := by
    have := congrArg (fun z => ⟪z, o⟫) hs
    simp only [real_inner_smul_left, inner_add_left] at this
    exact this
  rw [norm_sub_sq_real] at ha
  have hexp : ⟪(R ^ 2 - ‖o‖ ^ 2) • x + (2 * r ^ 2) • o, (R ^ 2 - ‖o‖ ^ 2) • y + (2 * r ^ 2) • o⟫ =
      (R ^ 2 - ‖o‖ ^ 2) ^ 2 * ⟪x, y⟫ + 2 * r ^ 2 * (R ^ 2 - ‖o‖ ^ 2) * (⟪x, o⟫ + ⟪y, o⟫) +
        4 * r ^ 4 * ‖o‖ ^ 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm y o]
    ring
  rw [hexp]
  have key : (r ^ 2 + ⟪x, y⟫) * ((R ^ 2 - ‖o‖ ^ 2) ^ 2 * ⟪x, y⟫ + 2 * r ^ 2 * (R ^ 2 - ‖o‖ ^ 2) * (⟪x, o⟫ + ⟪y, o⟫) +
        4 * r ^ 4 * ‖o‖ ^ 2 + r ^ 2 * ((R ^ 2 - ‖o‖ ^ 2) ^ 2 - 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2))) = 0 := by
    linear_combination (R ^ 2 - ‖o‖ ^ 2) * h1 - 2 * (R ^ 2 - ‖o‖ ^ 2) * (r ^ 2 + ⟪x, y⟫) * h2 -
      (R ^ 2 - ‖o‖ ^ 2) * (r ^ 2 + ⟪x, y⟫) ^ 2 * ha
  have := (mul_eq_zero.1 key).resolve_left hs0
  linear_combination this

/-- Three distinct points of a circle cannot lie on one tangent line `⟪·, x⟫ = r²`. -/
lemma not_three_on_line [Fact (Module.finrank ℝ V = 2)] {x o p q u : V} {r R : ℝ} (hr : r ≠ 0)
    (hx : ‖x‖ ^ 2 = r ^ 2) (hp : ⟪p, x⟫ = r ^ 2) (hq : ⟪q, x⟫ = r ^ 2) (hu : ⟪u, x⟫ = r ^ 2)
    (hp' : ‖p - o‖ ^ 2 = R ^ 2) (hq' : ‖q - o‖ ^ 2 = R ^ 2) (hu' : ‖u - o‖ ^ 2 = R ^ 2)
    (hpq : p ≠ q) (hpu : p ≠ u) (hqu : q ≠ u) : False := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hx
    exact pow_ne_zero 2 hr (by linear_combination -hx)
  rcases line_points (c := o) hx0 hp hq hu (by rw [hq', hp']) (by rw [hu', hp']) with h | h | h
  exacts [hpq h, hpu h, hqu h]

/-- **Fuss's relation, vector form.**  Four pairwise distinct points `a, b, c, e` of the circle
`‖· - o‖ = R`, with the four side lines `ab, bc, ce, ea` tangent to the circle `‖·‖ = r` at
`x₁, x₂, x₃, x₄`, and `R² ≠ ‖o‖²`: then `(R² - ‖o‖²)² = 2 r² (R² + ‖o‖²)`. -/
theorem fuss_vec [Fact (Module.finrank ℝ V = 2)] {a b c e o x₁ x₂ x₃ x₄ : V} {r R : ℝ}
    (hr : r ≠ 0) (hk : R ^ 2 - ‖o‖ ^ 2 ≠ 0)
    (ha : ‖a - o‖ ^ 2 = R ^ 2) (hb : ‖b - o‖ ^ 2 = R ^ 2) (hc : ‖c - o‖ ^ 2 = R ^ 2)
    (he : ‖e - o‖ ^ 2 = R ^ 2)
    (hab : a ≠ b) (hbc : b ≠ c) (hce : c ≠ e) (hea : e ≠ a) (hac : a ≠ c) (hbe : b ≠ e)
    (h₁ : ‖x₁‖ ^ 2 = r ^ 2) (h₂ : ‖x₂‖ ^ 2 = r ^ 2) (h₃ : ‖x₃‖ ^ 2 = r ^ 2) (h₄ : ‖x₄‖ ^ 2 = r ^ 2)
    (ha₁ : ⟪a, x₁⟫ = r ^ 2) (hb₁ : ⟪b, x₁⟫ = r ^ 2) (hb₂ : ⟪b, x₂⟫ = r ^ 2)
    (hc₂ : ⟪c, x₂⟫ = r ^ 2) (hc₃ : ⟪c, x₃⟫ = r ^ 2) (he₃ : ⟪e, x₃⟫ = r ^ 2)
    (he₄ : ⟪e, x₄⟫ = r ^ 2) (ha₄ : ⟪a, x₄⟫ = r ^ 2) :
    (R ^ 2 - ‖o‖ ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2) := by
  -- the tangency points are distinct where needed
  have n12 : x₁ ≠ x₂ := fun h => not_three_on_line hr h₁ ha₁ hb₁ (by rw [h]; exact hc₂) ha hb hc hab hac hbc
  have n23 : x₂ ≠ x₃ := fun h => not_three_on_line hr h₂ hb₂ hc₂ (by rw [h]; exact he₃) hb hc he hbc hbe hce
  have n34 : x₃ ≠ x₄ := fun h => not_three_on_line hr h₃ hc₃ he₃ (by rw [h]; exact ha₄) hc he ha hce hac.symm hea
  have n41 : x₄ ≠ x₁ := fun h => not_three_on_line hr h₄ he₄ ha₄ (by rw [h]; exact hb₁) he ha hb hea hbe.symm hab
  have n13 : x₁ ≠ x₃ := fun h => not_three_on_line hr h₁ ha₁ hb₁ (by rw [h]; exact hc₃) ha hb hc hab hac hbc
  have n24 : x₂ ≠ x₄ := fun h => not_three_on_line hr h₂ hb₂ hc₂ (by rw [h]; exact ha₄) hb hc ha hbc hab.symm hac.symm
  set k := R ^ 2 - ‖o‖ ^ 2 with hkdef
  set F := k ^ 2 - 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2) with hF
  set y₁ := k • x₁ + (2 * r ^ 2) • o
  set y₂ := k • x₂ + (2 * r ^ 2) • o
  set y₃ := k • x₃ + (2 * r ^ 2) • o
  set y₄ := k • x₄ + (2 * r ^ 2) • o
  have r41 : ⟪y₄, y₁⟫ = -(r ^ 2 * F) := vertex_rel hr h₄ h₁ n41 ha₄ ha₁ ha
  have r12 : ⟪y₁, y₂⟫ = -(r ^ 2 * F) := vertex_rel hr h₁ h₂ n12 hb₁ hb₂ hb
  have r23 : ⟪y₂, y₃⟫ = -(r ^ 2 * F) := vertex_rel hr h₂ h₃ n23 hc₂ hc₃ hc
  have r34 : ⟪y₃, y₄⟫ = -(r ^ 2 * F) := vertex_rel hr h₃ h₄ n34 he₃ he₄ he
  have hyinj : ∀ {x x' : V}, k • x + (2 * r ^ 2) • o = k • x' + (2 * r ^ 2) • o → x = x' :=
    fun h => smul_right_injective V hk (add_right_cancel h)
  by_contra hF0
  have hμ : -(r ^ 2 * F) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (pow_ne_zero 2 hr) (sub_ne_zero.2 hF0))
  have h13 : y₁ - y₃ ≠ 0 := fun h => n13 (hyinj (sub_eq_zero.1 h))
  have o2 : ⟪y₂, y₁ - y₃⟫ = 0 := by
    rw [inner_sub_right, real_inner_comm y₁ y₂, r12, r23, sub_self]
  have o4 : ⟪y₄, y₁ - y₃⟫ = 0 := by
    rw [inner_sub_right, r41, real_inner_comm y₃ y₄, r34, sub_self]
  have hpar := parallel_of_inner_eq_zero h13 o4 o2
  have h3 := congrArg (fun z => ⟪z, y₃⟫) hpar
  simp only [real_inner_smul_left] at h3
  rw [r23, real_inner_comm y₃ y₄, r34] at h3
  have hn : ‖y₄‖ ^ 2 = ⟪y₄, y₂⟫ := mul_right_cancel₀ hμ h3
  rw [← hn] at hpar
  have hy4 : y₄ ≠ 0 := by
    intro h; rw [h, inner_zero_right] at r34; exact hμ r34.symm
  have hn0 : ‖y₄‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy4)
  exact n24 (hyinj (smul_right_injective V hn0 hpar))

end Fuss
