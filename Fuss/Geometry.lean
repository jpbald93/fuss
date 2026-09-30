import Fuss.Steps

/-!
# Fuss's theorem and Poncelet's porism for quadrilaterals: Euclidean-plane statements

`V` is a 2-dimensional real inner product space, `P` a Euclidean affine plane over `V`,
`Γ` (centre `O`, radius `R`) and `ω` (centre `I`, radius `r`) circles, `d = dist O I`.

* `fuss_of_isBicentric` (**Fuss's theorem**): four pairwise distinct points of `Γ` whose four side
  lines `AB, BC, CD, DA` are tangent to `ω` satisfy `(R² - d²)² = 2 r² (R² + d²)`, provided
  `0 < r` and `d ≠ R`.
* `poncelet_chain_closes` (**closure**): under Fuss's relation, every 4-step chain of the tangent
  construction on `Γ` closes.
* `exists_bicentric_of_fuss` (**existence / porism**): under Fuss's relation and `d + r < R`,
  every point of `Γ` is a vertex of such a quadrilateral.
* `fuss_iff_forall`, `fuss_iff_exists`, `exists_iff_forall` (**all-or-nothing**).
* `fuss_iff_reciprocal`: the form `1/(R-d)² + 1/(R+d)² = 1/r²`.

`isTangent_of_mem_orthRadius` and `exists_mem_sphere` are copied (renamed namespace only) from the
Poncelet-triangle project `poncelet3` (`Poncelet3/Porism.lean`, `Poncelet3/Closure.lean`).
-/

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace Fuss

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- (Copied from `poncelet3`.) In a plane, a line through two distinct points of the tangent line
`s.orthRadius T` at a point `T` of the circle `s` is tangent to `s`. -/
lemma isTangent_of_mem_orthRadius [Fact (Module.finrank ℝ V = 2)] {s : Sphere P} {T A B : P}
    (hT : T ∈ s) (hTc : T ≠ s.center) (hA : A ∈ s.orthRadius T) (hB : B ∈ s.orthRadius T)
    (hAB : A ≠ B) : s.IsTangent line[ℝ, A, B] := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have hle : line[ℝ, A, B] ≤ s.orthRadius T := affineSpan_pair_le_of_mem_of_mem hA hB
  have hdir : (line[ℝ, A, B]).direction = (s.orthRadius T).direction := by
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    have h1 := s.finrank_orthRadius hTc
    have h2 : Module.finrank ℝ V = 2 := Fact.out
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.2 hAB)]
    omega
  have heq : line[ℝ, A, B] = s.orthRadius T :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ⟨A, left_mem_affineSpan_pair _ _ _⟩ hle
  rw [heq]
  exact ⟨T, Sphere.isTangentAt_orthRadius_iff_mem.2 hT⟩

/-- (Copied from `poncelet3`.) A circle of positive radius in a nontrivial space has a point. -/
lemma exists_mem_sphere [Nontrivial V] (Γ : Sphere P) (hR : 0 < Γ.radius) : ∃ A, A ∈ Γ := by
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  refine ⟨(Γ.radius / ‖w‖) • w +ᵥ Γ.center, ?_⟩
  rw [EuclideanGeometry.mem_sphere, dist_vadd_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hR hw'), div_mul_cancel₀ _ hw'.ne']

/-! ### Translation between points and vectors based at `I` -/

omit [InnerProductSpace ℝ V] in
lemma vec_of_mem {Γ : Sphere P} {I A : P} (hA : A ∈ Γ) :
    ‖(A -ᵥ I) - (Γ.center -ᵥ I)‖ ^ 2 = Γ.radius ^ 2 := by
  rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, EuclideanGeometry.mem_sphere.1 hA]

omit [InnerProductSpace ℝ V] in
lemma mem_of_vec {Γ : Sphere P} {I A : P} (hR : 0 ≤ Γ.radius)
    (h : ‖(A -ᵥ I) - (Γ.center -ᵥ I)‖ ^ 2 = Γ.radius ^ 2) : A ∈ Γ := by
  rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V] at h
  exact EuclideanGeometry.mem_sphere.2 ((pow_left_inj₀ dist_nonneg hR two_ne_zero).1 h)

omit [InnerProductSpace ℝ V] in
lemma vec_of_mem_center {ω : Sphere P} {T : P} (hT : T ∈ ω) :
    ‖T -ᵥ ω.center‖ ^ 2 = ω.radius ^ 2 := by
  rw [← dist_eq_norm_vsub V, EuclideanGeometry.mem_sphere.1 hT]

lemma mem_orthRadius_iff {ω : Sphere P} {T A : P} (hT : T ∈ ω) :
    A ∈ ω.orthRadius T ↔ ⟪A -ᵥ ω.center, T -ᵥ ω.center⟫ = ω.radius ^ 2 := by
  rw [Sphere.mem_orthRadius_iff_inner_left, ← vsub_sub_vsub_cancel_right A T ω.center,
    inner_sub_left, real_inner_self_eq_norm_sq, vec_of_mem_center hT, sub_eq_zero]

lemma ne_center {ω : Sphere P} {T : P} (hr : 0 < ω.radius) (hT : T ∈ ω) : T ≠ ω.center := by
  intro h
  have := EuclideanGeometry.mem_sphere.1 hT
  rw [h, dist_self] at this
  linarith

omit [InnerProductSpace ℝ V] in
lemma vsub_ne {A B I : P} (h : A ≠ B) : A -ᵥ I ≠ B -ᵥ I := fun e => h (vsub_left_cancel e)

omit [InnerProductSpace ℝ V] in
lemma norm_center (Γ ω : Sphere P) : ‖Γ.center -ᵥ ω.center‖ = dist Γ.center ω.center :=
  (dist_eq_norm_vsub V _ _).symm

/-- A (possibly non-convex) **bicentric quadrilateral** `ABCD`: four pairwise distinct points of
`Γ` such that the four side lines `AB`, `BC`, `CD`, `DA` are tangent to `ω`. -/
def IsBicentric (Γ ω : Sphere P) (A B C D : P) : Prop :=
  A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
    A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
    ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
    ω.IsTangent line[ℝ, D, A]

/-- **Fuss's theorem.**  If `ABCD` is a bicentric quadrilateral for `Γ` (radius `R`) and `ω`
(radius `r > 0`), and the distance `d` of the centres is not `R`, then
`(R² - d²)² = 2 r² (R² + d²)`. -/
theorem fuss_of_isBicentric [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P) {A B C D : P}
    (hr : 0 < ω.radius) (hd : dist Γ.center ω.center ≠ Γ.radius)
    (h : IsBicentric Γ ω A B C D) :
    (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
  obtain ⟨hA, hB, hC, hD, hAB, hBC, hCD, hDA, hAC, hBD, tAB, tBC, tCD, tDA⟩ := h
  obtain ⟨T₁, hT₁⟩ := tAB
  obtain ⟨T₂, hT₂⟩ := tBC
  obtain ⟨T₃, hT₃⟩ := tCD
  obtain ⟨T₄, hT₄⟩ := tDA
  have hR : 0 ≤ Γ.radius := by rw [← EuclideanGeometry.mem_sphere.1 hA]; exact dist_nonneg
  have hk : Γ.radius ^ 2 - ‖Γ.center -ᵥ ω.center‖ ^ 2 ≠ 0 := by
    rw [norm_center]
    intro h0
    exact hd ((pow_left_inj₀ dist_nonneg hR two_ne_zero).1 (by linarith))
  have key := fuss_vec (a := A -ᵥ ω.center) (b := B -ᵥ ω.center) (c := C -ᵥ ω.center)
    (e := D -ᵥ ω.center) (o := Γ.center -ᵥ ω.center) (x₁ := T₁ -ᵥ ω.center)
    (x₂ := T₂ -ᵥ ω.center) (x₃ := T₃ -ᵥ ω.center) (x₄ := T₄ -ᵥ ω.center) hr.ne' hk
    (vec_of_mem hA) (vec_of_mem hB) (vec_of_mem hC) (vec_of_mem hD)
    (vsub_ne hAB) (vsub_ne hBC) (vsub_ne hCD) (vsub_ne hDA) (vsub_ne hAC) (vsub_ne hBD)
    (vec_of_mem_center hT₁.mem_sphere) (vec_of_mem_center hT₂.mem_sphere)
    (vec_of_mem_center hT₃.mem_sphere) (vec_of_mem_center hT₄.mem_sphere)
    ((mem_orthRadius_iff hT₁.mem_sphere).1 (hT₁.le_orthRadius (left_mem_affineSpan_pair ℝ A B)))
    ((mem_orthRadius_iff hT₁.mem_sphere).1 (hT₁.le_orthRadius (right_mem_affineSpan_pair ℝ A B)))
    ((mem_orthRadius_iff hT₂.mem_sphere).1 (hT₂.le_orthRadius (left_mem_affineSpan_pair ℝ B C)))
    ((mem_orthRadius_iff hT₂.mem_sphere).1 (hT₂.le_orthRadius (right_mem_affineSpan_pair ℝ B C)))
    ((mem_orthRadius_iff hT₃.mem_sphere).1 (hT₃.le_orthRadius (left_mem_affineSpan_pair ℝ C D)))
    ((mem_orthRadius_iff hT₃.mem_sphere).1 (hT₃.le_orthRadius (right_mem_affineSpan_pair ℝ C D)))
    ((mem_orthRadius_iff hT₄.mem_sphere).1 (hT₄.le_orthRadius (left_mem_affineSpan_pair ℝ D A)))
    ((mem_orthRadius_iff hT₄.mem_sphere).1 (hT₄.le_orthRadius (right_mem_affineSpan_pair ℝ D A)))
  rwa [norm_center] at key

/-- **Poncelet's closure for quadrilaterals.**  Assume Fuss's relation, `0 < r` and `d ≠ R`.
Start at `A₀ ∈ Γ` on the tangent to `ω` at `T₀`; take the other tangent from `A₀` (at `T₁ ≠ T₀`)
and its other intersection `A₁ ≠ A₀` with `Γ`; repeat.  (`X ∈ ω.orthRadius T` says that `X` lies on
the tangent line at `T ∈ ω`.)  Then after four steps the construction is back: `A₄ = A₀` and
`T₄ = T₀`. -/
theorem poncelet_chain_closes [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hd : dist Γ.center ω.center ≠ Γ.radius)
    (hF : (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2))
    {A₀ A₁ A₂ A₃ A₄ T₀ T₁ T₂ T₃ T₄ : P}
    (hA₀ : A₀ ∈ Γ) (hA₁ : A₁ ∈ Γ) (hA₂ : A₂ ∈ Γ) (hA₃ : A₃ ∈ Γ) (hA₄ : A₄ ∈ Γ)
    (hT₀ : T₀ ∈ ω) (hT₁ : T₁ ∈ ω) (hT₂ : T₂ ∈ ω) (hT₃ : T₃ ∈ ω) (hT₄ : T₄ ∈ ω)
    (h00 : A₀ ∈ ω.orthRadius T₀) (h01 : A₀ ∈ ω.orthRadius T₁) (h11 : A₁ ∈ ω.orthRadius T₁)
    (h12 : A₁ ∈ ω.orthRadius T₂) (h22 : A₂ ∈ ω.orthRadius T₂) (h23 : A₂ ∈ ω.orthRadius T₃)
    (h33 : A₃ ∈ ω.orthRadius T₃) (h34 : A₃ ∈ ω.orthRadius T₄) (h44 : A₄ ∈ ω.orthRadius T₄)
    (n01 : T₀ ≠ T₁) (n12 : T₁ ≠ T₂) (n23 : T₂ ≠ T₃) (n34 : T₃ ≠ T₄)
    (m01 : A₀ ≠ A₁) (m12 : A₁ ≠ A₂) (m23 : A₂ ≠ A₃) (m34 : A₃ ≠ A₄) :
    A₄ = A₀ ∧ T₄ = T₀ := by
  have hR : 0 ≤ Γ.radius := by rw [← EuclideanGeometry.mem_sphere.1 hA₀]; exact dist_nonneg
  have hk : Γ.radius ^ 2 - ‖Γ.center -ᵥ ω.center‖ ^ 2 ≠ 0 := by
    rw [norm_center]
    intro h0
    exact hd ((pow_left_inj₀ dist_nonneg hR two_ne_zero).1 (by linarith))
  rw [← norm_center] at hF
  obtain ⟨e1, e2⟩ := closes_vec (o := Γ.center -ᵥ ω.center) hr.ne' hk hF
    (vec_of_mem hA₀) (vec_of_mem hA₁) (vec_of_mem hA₂) (vec_of_mem hA₃) (vec_of_mem hA₄)
    (vec_of_mem_center hT₀) (vec_of_mem_center hT₁) (vec_of_mem_center hT₂)
    (vec_of_mem_center hT₃) (vec_of_mem_center hT₄)
    ((mem_orthRadius_iff hT₀).1 h00) ((mem_orthRadius_iff hT₁).1 h01)
    ((mem_orthRadius_iff hT₁).1 h11) ((mem_orthRadius_iff hT₂).1 h12)
    ((mem_orthRadius_iff hT₂).1 h22) ((mem_orthRadius_iff hT₃).1 h23)
    ((mem_orthRadius_iff hT₃).1 h33) ((mem_orthRadius_iff hT₄).1 h34)
    ((mem_orthRadius_iff hT₄).1 h44)
    (vsub_ne n01) (vsub_ne n12) (vsub_ne n23) (vsub_ne n34)
    (vsub_ne m01) (vsub_ne m12) (vsub_ne m23) (vsub_ne m34)
  exact ⟨vsub_left_cancel e1, vsub_left_cancel e2⟩

/-- Vector form of the existence statement. -/
lemma exists_quad_vec [Fact (Module.finrank ℝ V = 2)] {o a : V} {r R : ℝ} (hr : 0 < r)
    (hin : ‖o‖ + r < R) (hF : (R ^ 2 - ‖o‖ ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + ‖o‖ ^ 2))
    (ha : ‖a - o‖ ^ 2 = R ^ 2) :
    ∃ b c e x₁ x₂ x₃ x₄ : V, ‖b - o‖ ^ 2 = R ^ 2 ∧ ‖c - o‖ ^ 2 = R ^ 2 ∧ ‖e - o‖ ^ 2 = R ^ 2 ∧
      a ≠ b ∧ b ≠ c ∧ c ≠ e ∧ e ≠ a ∧ a ≠ c ∧ b ≠ e ∧
      ‖x₁‖ ^ 2 = r ^ 2 ∧ ‖x₂‖ ^ 2 = r ^ 2 ∧ ‖x₃‖ ^ 2 = r ^ 2 ∧ ‖x₄‖ ^ 2 = r ^ 2 ∧
      ⟪a, x₁⟫ = r ^ 2 ∧ ⟪b, x₁⟫ = r ^ 2 ∧ ⟪b, x₂⟫ = r ^ 2 ∧ ⟪c, x₂⟫ = r ^ 2 ∧
      ⟪c, x₃⟫ = r ^ 2 ∧ ⟪e, x₃⟫ = r ^ 2 ∧ ⟪e, x₄⟫ = r ^ 2 ∧ ⟪a, x₄⟫ = r ^ 2 := by
  have hR : 0 < R := by linarith [norm_nonneg o]
  have hk : R ^ 2 - ‖o‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg o]
  obtain ⟨x₀, h₀, h00⟩ := first_tangent (outside_of_mem hr hin ha)
  obtain ⟨x₁, a₁, h₁, h01, n01, ha₁, h11, m01⟩ := step hr hin ha h₀ h00
  obtain ⟨x₂, a₂, h₂, h12, n12, ha₂, h22, m12⟩ := step hr hin ha₁ h₁ h11
  obtain ⟨x₃, a₃, h₃, h23, n23, ha₃, h33, m23⟩ := step hr hin ha₂ h₂ h22
  obtain ⟨x₄, a₄, h₄, h34, n34, ha₄, h44, m34⟩ := step hr hin ha₃ h₃ h33
  obtain ⟨e1, e2⟩ := closes_vec hr.ne' hk hF ha ha₁ ha₂ ha₃ ha₄ h₀ h₁ h₂ h₃ h₄
    h00 h01 h11 h12 h22 h23 h33 h34 h44 n01 n12 n23 n34 m01 m12 m23 m34
  obtain ⟨d02, d13⟩ := chain_distinct hr.ne' h₀ h₁ h₂ h₃ h00 h01 h11 h12 h22 h23 h33
    n01 n12 n23 m01 m12
  refine ⟨a₁, a₂, a₃, x₁, x₂, x₃, x₄, ha₁, ha₂, ha₃, m01, m12, m23, ?_, d02, d13,
    h₁, h₂, h₃, h₄, h01, h11, h12, h22, h23, h33, h34, ?_⟩
  · rw [← e1]; exact m34
  · rw [e2]; exact h00

/-- **Poncelet's porism for quadrilaterals (existence).**  If `0 < r`, `ω` lies inside `Γ`
(`d + r < R`) and Fuss's relation holds, then every point `A` of `Γ` is a vertex of a bicentric
quadrilateral `ABCD`. -/
theorem exists_bicentric_of_fuss [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius)
    (hF : (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2))
    {A : P} (hA : A ∈ Γ) : ∃ B C D : P, IsBicentric Γ ω A B C D := by
  set I := ω.center
  have hR : 0 ≤ Γ.radius := by linarith [dist_nonneg (x := Γ.center) (y := I)]
  rw [← norm_center] at hF hin
  obtain ⟨b, c, e, x₁, x₂, x₃, x₄, hb, hc, he, hab, hbc, hce, hea, hac, hbe, h₁, h₂, h₃, h₄,
    ha₁, hb₁, hb₂, hc₂, hc₃, he₃, he₄, ha₄⟩ := exists_quad_vec hr hin hF (vec_of_mem hA)
  have pt : ∀ v : V, (v +ᵥ I) -ᵥ I = v := fun v => vadd_vsub v I
  have mω : ∀ x : V, ‖x‖ ^ 2 = ω.radius ^ 2 → x +ᵥ I ∈ ω := by
    intro x hx
    rw [EuclideanGeometry.mem_sphere, dist_vadd_left]
    exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).1 hx
  have mΓ : ∀ v : V, ‖v - (Γ.center -ᵥ I)‖ ^ 2 = Γ.radius ^ 2 → v +ᵥ I ∈ Γ := by
    intro v hv
    apply mem_of_vec (I := I) hR
    rw [pt]; exact hv
  have orth : ∀ v x : V, ‖x‖ ^ 2 = ω.radius ^ 2 → ⟪v, x⟫ = ω.radius ^ 2 →
      v +ᵥ I ∈ ω.orthRadius (x +ᵥ I) := by
    intro v x hx hvx
    rw [mem_orthRadius_iff (mω x hx), pt, pt]; exact hvx
  have tan : ∀ v w x : V, ‖x‖ ^ 2 = ω.radius ^ 2 → ⟪v, x⟫ = ω.radius ^ 2 →
      ⟪w, x⟫ = ω.radius ^ 2 → v ≠ w → ω.IsTangent line[ℝ, v +ᵥ I, w +ᵥ I] := by
    intro v w x hx hv hw hvw
    exact isTangent_of_mem_orthRadius (mω x hx) (ne_center hr (mω x hx)) (orth v x hx hv)
      (orth w x hx hw) (fun h => hvw (vadd_right_cancel I h))
  have ne : ∀ v w : V, v ≠ w → v +ᵥ I ≠ w +ᵥ I := fun v w h e => h (vadd_right_cancel I e)
  have hA' : (A -ᵥ I) +ᵥ I = A := vsub_vadd A I
  refine ⟨b +ᵥ I, c +ᵥ I, e +ᵥ I, ?_⟩
  have key : IsBicentric Γ ω ((A -ᵥ I) +ᵥ I) (b +ᵥ I) (c +ᵥ I) (e +ᵥ I) :=
    ⟨by rw [hA']; exact hA, mΓ b hb, mΓ c hc, mΓ e he, ne _ _ hab, ne _ _ hbc, ne _ _ hce,
      ne _ _ hea, ne _ _ hac, ne _ _ hbe, tan _ _ _ h₁ ha₁ hb₁ hab, tan _ _ _ h₂ hb₂ hc₂ hbc,
      tan _ _ _ h₃ hc₃ he₃ hce, tan _ _ _ h₄ he₄ ha₄ hea⟩
  rwa [hA'] at key

/-- **All or nothing.**  For `0 < r` and `ω` inside `Γ`: a bicentric quadrilateral exists iff
Fuss's relation holds. -/
theorem fuss_iff_exists [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∃ A B C D : P, IsBicentric Γ ω A B C D) ↔
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
  constructor
  · rintro ⟨A, B, C, D, h⟩
    exact fuss_of_isBicentric Γ ω hr (by linarith) h
  · intro hF
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = 2)
    obtain ⟨A, hA⟩ := exists_mem_sphere Γ (by linarith [dist_nonneg (x := Γ.center) (y := ω.center)])
    obtain ⟨B, C, D, h⟩ := exists_bicentric_of_fuss Γ ω hr hin hF hA
    exact ⟨A, B, C, D, h⟩

/-- **All or nothing, pointwise form.**  For `0 < r` and `ω` inside `Γ`: every point of `Γ` is a
vertex of a bicentric quadrilateral iff Fuss's relation holds. -/
theorem fuss_iff_forall [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∀ A ∈ Γ, ∃ B C D : P, IsBicentric Γ ω A B C D) ↔
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
  constructor
  · intro h
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = 2)
    obtain ⟨A, hA⟩ := exists_mem_sphere Γ (by linarith [dist_nonneg (x := Γ.center) (y := ω.center)])
    obtain ⟨B, C, D, hq⟩ := h A hA
    exact fuss_of_isBicentric Γ ω hr (by linarith) hq
  · intro hF A hA
    exact exists_bicentric_of_fuss Γ ω hr hin hF hA

/-- **Porism.**  If one bicentric quadrilateral exists, then every point of `Γ` is a vertex of
one. -/
theorem exists_iff_forall [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∃ A B C D : P, IsBicentric Γ ω A B C D) ↔ ∀ A ∈ Γ, ∃ B C D : P, IsBicentric Γ ω A B C D :=
  (fuss_iff_exists Γ ω hr hin).trans (fuss_iff_forall Γ ω hr hin).symm

/-- Fuss's relation in the reciprocal form `1/(R-d)² + 1/(R+d)² = 1/r²` (for `0 ≤ d < R`,
`r ≠ 0`). -/
theorem fuss_iff_reciprocal {R d r : ℝ} (hd : 0 ≤ d) (hdR : d < R) (hr : r ≠ 0) :
    (R ^ 2 - d ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + d ^ 2) ↔
      1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2 := by
  have h1 : R - d ≠ 0 := by linarith
  have h2 : R + d ≠ 0 := by linarith
  rw [div_add_div _ _ (pow_ne_zero 2 h1) (pow_ne_zero 2 h2),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2)) (pow_ne_zero 2 hr)]
  constructor <;> intro h <;> linear_combination (-1 : ℝ) * h

end Fuss
