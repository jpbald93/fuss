import Fuss.Geometry
import Fuss.Example

/-!
# Layer 14: Mathlib-only restatements and witnesses

The statements `l14_*` restate the main theorems with `Fuss.IsBicentric` unfolded into Mathlib
notions (`Sphere` membership, `Sphere.IsTangent` of `line[ℝ, _, _]`, `Sphere.orthRadius`); their
types mention no definition of this repository.

The witnesses `l14w_*` work in `ℂ` with `Γ` of centre `1` and radius `7` and `ω` of centre `0` and
radius `24/5` (the circles of `Fuss.nonvacuous`). The explicit kite
`A = 8`, `B = -24/25 + 168/25 i`, `C = -6`, `D = -24/25 - 168/25 i` is bicentric, with tangency
points `72/25 + 96/25 i` (on `AB`), `-96/25 + 72/25 i` (`BC`), `-96/25 - 72/25 i` (`CD`) and
`72/25 - 96/25 i` (`DA`), all pairwise distinct. For the negative direction of the equivalences, the
circle `ω'` of centre `0` and radius `1` violates Fuss's relation, so no bicentric quadrilateral
exists for `Γ, ω'`.
-/

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace Fuss

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Bridge: `IsBicentric` is the stated conjunction of Mathlib notions. -/
lemma l14_isBicentric_iff (Γ ω : Sphere P) (A B C D : P) :
    IsBicentric Γ ω A B C D ↔
      (A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) :=
  Iff.rfl

/-- **Fuss's theorem, Mathlib-only form.** -/
theorem l14_fuss [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P) {A B C D : P}
    (hr : 0 < ω.radius) (hd : dist Γ.center ω.center ≠ Γ.radius)
    (hA : A ∈ Γ) (hB : B ∈ Γ) (hC : C ∈ Γ) (hD : D ∈ Γ)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDA : D ≠ A) (hAC : A ≠ C) (hBD : B ≠ D)
    (tAB : ω.IsTangent line[ℝ, A, B]) (tBC : ω.IsTangent line[ℝ, B, C])
    (tCD : ω.IsTangent line[ℝ, C, D]) (tDA : ω.IsTangent line[ℝ, D, A]) :
    (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) :=
  fuss_of_isBicentric Γ ω hr hd
    ⟨hA, hB, hC, hD, hAB, hBC, hCD, hDA, hAC, hBD, tAB, tBC, tCD, tDA⟩

/-- **Poncelet closure for quadrilaterals, Mathlib-only form.** This is
`poncelet_chain_closes`, whose type already mentions only Mathlib notions. -/
theorem l14_poncelet_chain_closes [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
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
    A₄ = A₀ ∧ T₄ = T₀ :=
  poncelet_chain_closes Γ ω hr hd hF hA₀ hA₁ hA₂ hA₃ hA₄ hT₀ hT₁ hT₂ hT₃ hT₄ h00 h01 h11 h12
    h22 h23 h33 h34 h44 n01 n12 n23 n34 m01 m12 m23 m34

/-- **Poncelet's porism for quadrilaterals (existence), Mathlib-only form.** -/
theorem l14_exists_bicentric [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius)
    (hF : (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
      2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2))
    {A : P} (hA : A ∈ Γ) :
    ∃ B C D : P, B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
      ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
      ω.IsTangent line[ℝ, D, A] := by
  obtain ⟨B, C, D, -, h⟩ := exists_bicentric_of_fuss Γ ω hr hin hF hA
  exact ⟨B, C, D, h⟩

/-- **All or nothing (existence form), Mathlib-only.** -/
theorem l14_fuss_iff_exists [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∃ A B C D : P, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) ↔
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) :=
  fuss_iff_exists Γ ω hr hin

/-- **All or nothing (pointwise form), Mathlib-only.** -/
theorem l14_fuss_iff_forall [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∀ A ∈ Γ, ∃ B C D : P, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) ↔
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) :=
  fuss_iff_forall Γ ω hr hin

/-- **Porism, Mathlib-only form**: one bicentric quadrilateral gives one through every point. -/
theorem l14_exists_iff_forall [Fact (Module.finrank ℝ V = 2)] (Γ ω : Sphere P)
    (hr : 0 < ω.radius) (hin : dist Γ.center ω.center + ω.radius < Γ.radius) :
    (∃ A B C D : P, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) ↔
      (∀ A ∈ Γ, ∃ B C D : P, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) :=
  exists_iff_forall Γ ω hr hin

/-- **Reciprocal form, Mathlib-only** (the type is pure real arithmetic). -/
theorem l14_fuss_iff_reciprocal {R d r : ℝ} (hd : 0 ≤ d) (hdR : d < R) (hr : r ≠ 0) :
    (R ^ 2 - d ^ 2) ^ 2 = 2 * r ^ 2 * (R ^ 2 + d ^ 2) ↔
      1 / (R - d) ^ 2 + 1 / (R + d) ^ 2 = 1 / r ^ 2 :=
  fuss_iff_reciprocal hd hdR hr

/-! ### Witnesses in `ℂ` -/

lemma l14_dist_eq {z w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = r ^ 2) : dist z w = r := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hr]

lemma l14_inner (w z : ℂ) : ⟪w, z⟫ = w.re * z.re + w.im * z.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma l14_mem_orthRadius {ω : Sphere ℂ} {T A : ℂ} (hT : T ∈ ω)
    (h : (A.re - ω.center.re) * (T.re - ω.center.re) + (A.im - ω.center.im) * (T.im - ω.center.im)
      = ω.radius ^ 2) : A ∈ ω.orthRadius T := by
  rw [mem_orthRadius_iff hT, vsub_eq_sub, vsub_eq_sub, l14_inner]
  simpa using h

/-- `Γ`: centre `1`, radius `7`. -/
noncomputable def l14Γ : Sphere ℂ := ⟨1, 7⟩
/-- `ω`: centre `0`, radius `24/5`. -/
noncomputable def l14ω : Sphere ℂ := ⟨0, 24 / 5⟩

lemma l14_mem_Γ {z : ℂ} (h : (z.re - 1) ^ 2 + z.im ^ 2 = 49) : z ∈ l14Γ :=
  EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num [l14Γ]) (by simp [l14Γ]; linarith))

lemma l14_mem_ω {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 = (24 / 5) ^ 2) : z ∈ l14ω :=
  EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num [l14ω]) (by simp [l14ω]; linarith))

lemma l14_orth_ω {T A : ℂ} (hT : T ∈ l14ω) (h : A.re * T.re + A.im * T.im = (24 / 5) ^ 2) :
    A ∈ l14ω.orthRadius T :=
  l14_mem_orthRadius hT (by simp [l14ω]; linarith)

lemma l14_dist_Γω : dist l14Γ.center l14ω.center = 1 :=
  l14_dist_eq (by norm_num) (by simp [l14Γ, l14ω])

lemma l14_fuss_rel : (l14Γ.radius ^ 2 - dist l14Γ.center l14ω.center ^ 2) ^ 2 =
    2 * l14ω.radius ^ 2 * (l14Γ.radius ^ 2 + dist l14Γ.center l14ω.center ^ 2) := by
  rw [l14_dist_Γω]; simp [l14Γ, l14ω]; norm_num

lemma l14_inside : dist l14Γ.center l14ω.center + l14ω.radius < l14Γ.radius := by
  rw [l14_dist_Γω]; simp [l14Γ, l14ω]; norm_num

/-- The kite vertices and tangency points. -/
noncomputable def l14A : ℂ := ⟨8, 0⟩
noncomputable def l14B : ℂ := ⟨-24 / 25, 168 / 25⟩
noncomputable def l14C : ℂ := ⟨-6, 0⟩
noncomputable def l14D : ℂ := ⟨-24 / 25, -168 / 25⟩
noncomputable def l14TAB : ℂ := ⟨72 / 25, 96 / 25⟩
noncomputable def l14TBC : ℂ := ⟨-96 / 25, 72 / 25⟩
noncomputable def l14TCD : ℂ := ⟨-96 / 25, -72 / 25⟩
noncomputable def l14TDA : ℂ := ⟨72 / 25, -96 / 25⟩

lemma l14_ne {z w : ℂ} (h : z.re ≠ w.re ∨ z.im ≠ w.im) : z ≠ w := by
  rintro rfl; simp at h

/-- All the incidences of the explicit kite. -/
lemma l14_kite :
    l14A ∈ l14Γ ∧ l14B ∈ l14Γ ∧ l14C ∈ l14Γ ∧ l14D ∈ l14Γ ∧
    l14TAB ∈ l14ω ∧ l14TBC ∈ l14ω ∧ l14TCD ∈ l14ω ∧ l14TDA ∈ l14ω ∧
    l14A ∈ l14ω.orthRadius l14TAB ∧ l14B ∈ l14ω.orthRadius l14TAB ∧
    l14B ∈ l14ω.orthRadius l14TBC ∧ l14C ∈ l14ω.orthRadius l14TBC ∧
    l14C ∈ l14ω.orthRadius l14TCD ∧ l14D ∈ l14ω.orthRadius l14TCD ∧
    l14D ∈ l14ω.orthRadius l14TDA ∧ l14A ∈ l14ω.orthRadius l14TDA := by
  have m1 : l14TAB ∈ l14ω := l14_mem_ω (by simp [l14TAB]; norm_num)
  have m2 : l14TBC ∈ l14ω := l14_mem_ω (by simp [l14TBC]; norm_num)
  have m3 : l14TCD ∈ l14ω := l14_mem_ω (by simp [l14TCD]; norm_num)
  have m4 : l14TDA ∈ l14ω := l14_mem_ω (by simp [l14TDA]; norm_num)
  exact ⟨l14_mem_Γ (by simp [l14A]; norm_num), l14_mem_Γ (by simp [l14B]; norm_num),
    l14_mem_Γ (by simp [l14C]; norm_num), l14_mem_Γ (by simp [l14D]; norm_num), m1, m2, m3, m4,
    l14_orth_ω m1 (by simp [l14A, l14TAB]; norm_num),
    l14_orth_ω m1 (by simp [l14B, l14TAB]; norm_num),
    l14_orth_ω m2 (by simp [l14B, l14TBC]; norm_num),
    l14_orth_ω m2 (by simp [l14C, l14TBC]; norm_num),
    l14_orth_ω m3 (by simp [l14C, l14TCD]; norm_num),
    l14_orth_ω m3 (by simp [l14D, l14TCD]; norm_num),
    l14_orth_ω m4 (by simp [l14D, l14TDA]; norm_num),
    l14_orth_ω m4 (by simp [l14A, l14TDA]; norm_num)⟩

lemma l14_kite_ne :
    l14A ≠ l14B ∧ l14B ≠ l14C ∧ l14C ≠ l14D ∧ l14D ≠ l14A ∧ l14A ≠ l14C ∧ l14B ≠ l14D ∧
    l14TAB ≠ l14TBC ∧ l14TBC ≠ l14TCD ∧ l14TCD ≠ l14TDA ∧ l14TDA ≠ l14TAB ∧
    l14TAB ≠ l14TCD ∧ l14TBC ≠ l14TDA := by
  refine ⟨l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_,
    l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_, l14_ne ?_⟩ <;>
    simp [l14A, l14B, l14C, l14D, l14TAB, l14TBC, l14TCD, l14TDA] <;> norm_num

lemma l14_kite_tangent :
    l14ω.IsTangent line[ℝ, l14A, l14B] ∧ l14ω.IsTangent line[ℝ, l14B, l14C] ∧
    l14ω.IsTangent line[ℝ, l14C, l14D] ∧ l14ω.IsTangent line[ℝ, l14D, l14A] := by
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨-, -, -, -, m1, m2, m3, m4, o1, o2, o3, o4, o5, o6, o7, o8⟩ := l14_kite
  obtain ⟨n1, n2, n3, n4, -⟩ := l14_kite_ne
  have hr : (0 : ℝ) < l14ω.radius := by norm_num [l14ω]
  exact ⟨isTangent_of_mem_orthRadius m1 (ne_center hr m1) o1 o2 n1,
    isTangent_of_mem_orthRadius m2 (ne_center hr m2) o3 o4 n2,
    isTangent_of_mem_orthRadius m3 (ne_center hr m3) o5 o6 n3,
    isTangent_of_mem_orthRadius m4 (ne_center hr m4) o7 o8 n4⟩

/-- Witness for `l14_fuss`: all hypotheses hold for the explicit kite, the circles are not
concentric, and the conclusion holds. -/
theorem l14w_fuss :
    ∃ (Γ ω : Sphere ℂ) (A B C D : ℂ), 0 < ω.radius ∧ dist Γ.center ω.center ≠ Γ.radius ∧
      A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
      ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
      ω.IsTangent line[ℝ, D, A] ∧ Γ.center ≠ ω.center ∧ Γ ≠ ω ∧
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) := by
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨hA, hB, hC, hD, -⟩ := l14_kite
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := l14_kite_ne
  obtain ⟨t1, t2, t3, t4⟩ := l14_kite_tangent
  have hr : (0 : ℝ) < l14ω.radius := by norm_num [l14ω]
  have hd : dist l14Γ.center l14ω.center ≠ l14Γ.radius := by
    rw [l14_dist_Γω]; norm_num [l14Γ]
  have hc : l14Γ.center ≠ l14ω.center := l14_ne (by simp [l14Γ, l14ω])
  refine ⟨l14Γ, l14ω, l14A, l14B, l14C, l14D, hr, hd, hA, hB, hC, hD, n1, n2, n3, n4, n5, n6,
    t1, t2, t3, t4, hc, fun h => hc (h ▸ rfl), ?_⟩
  exact l14_fuss l14Γ l14ω hr hd hA hB hC hD n1 n2 n3 n4 n5 n6 t1 t2 t3 t4

/-- Witness for `l14_poncelet_chain_closes`: the chain `A, B, C, D, A` with tangency points
`T_DA, T_AB, T_BC, T_CD, T_DA` satisfies every hypothesis (with consecutive points distinct), and
the circles are not concentric. -/
theorem l14w_poncelet_chain_closes :
    ∃ (Γ ω : Sphere ℂ) (A₀ A₁ A₂ A₃ A₄ T₀ T₁ T₂ T₃ T₄ : ℂ),
      0 < ω.radius ∧ dist Γ.center ω.center ≠ Γ.radius ∧
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) ∧
      A₀ ∈ Γ ∧ A₁ ∈ Γ ∧ A₂ ∈ Γ ∧ A₃ ∈ Γ ∧ A₄ ∈ Γ ∧
      T₀ ∈ ω ∧ T₁ ∈ ω ∧ T₂ ∈ ω ∧ T₃ ∈ ω ∧ T₄ ∈ ω ∧
      A₀ ∈ ω.orthRadius T₀ ∧ A₀ ∈ ω.orthRadius T₁ ∧ A₁ ∈ ω.orthRadius T₁ ∧
      A₁ ∈ ω.orthRadius T₂ ∧ A₂ ∈ ω.orthRadius T₂ ∧ A₂ ∈ ω.orthRadius T₃ ∧
      A₃ ∈ ω.orthRadius T₃ ∧ A₃ ∈ ω.orthRadius T₄ ∧ A₄ ∈ ω.orthRadius T₄ ∧
      T₀ ≠ T₁ ∧ T₁ ≠ T₂ ∧ T₂ ≠ T₃ ∧ T₃ ≠ T₄ ∧
      A₀ ≠ A₁ ∧ A₁ ≠ A₂ ∧ A₂ ≠ A₃ ∧ A₃ ≠ A₄ ∧
      A₀ ≠ A₂ ∧ A₁ ≠ A₃ ∧ T₀ ≠ T₂ ∧ T₁ ≠ T₃ ∧ Γ.center ≠ ω.center ∧
      A₄ = A₀ ∧ T₄ = T₀ := by
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨hA, hB, hC, hD, m1, m2, m3, m4, o1, o2, o3, o4, o5, o6, o7, o8⟩ := l14_kite
  obtain ⟨n1, n2, n3, n4, n5, n6, k1, k2, k3, k4, k5, k6⟩ := l14_kite_ne
  have hr : (0 : ℝ) < l14ω.radius := by norm_num [l14ω]
  have hd : dist l14Γ.center l14ω.center ≠ l14Γ.radius := by
    rw [l14_dist_Γω]; norm_num [l14Γ]
  have hc : l14Γ.center ≠ l14ω.center := l14_ne (by simp [l14Γ, l14ω])
  have cl := l14_poncelet_chain_closes l14Γ l14ω hr hd l14_fuss_rel hA hB hC hD hA m4 m1 m2 m3 m4
    o8 o1 o2 o3 o4 o5 o6 o7 o8 k4 k1 k2 k3 n1 n2 n3 n4
  exact ⟨l14Γ, l14ω, l14A, l14B, l14C, l14D, l14A, l14TDA, l14TAB, l14TBC, l14TCD, l14TDA,
    hr, hd, l14_fuss_rel, hA, hB, hC, hD, hA, m4, m1, m2, m3, m4, o8, o1, o2, o3, o4, o5, o6, o7,
    o8, k4, k1, k2, k3, n1, n2, n3, n4, n5, n6, k6.symm, k5, hc, cl⟩

/-- Witness for `l14_exists_bicentric` (and the positive side of the equivalences): the
hypotheses hold for non-concentric circles, the theorem produces a quadrilateral through `A = 8`,
and an explicit bicentric quadrilateral exists. -/
theorem l14w_exists_bicentric :
    ∃ (Γ ω : Sphere ℂ) (A : ℂ), 0 < ω.radius ∧
      dist Γ.center ω.center + ω.radius < Γ.radius ∧ Γ.center ≠ ω.center ∧
      (Γ.radius ^ 2 - dist Γ.center ω.center ^ 2) ^ 2 =
        2 * ω.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω.center ^ 2) ∧ A ∈ Γ ∧
      (∃ B C D : ℂ, B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧ ω.IsTangent line[ℝ, C, D] ∧
        ω.IsTangent line[ℝ, D, A]) := by
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨hA, -⟩ := l14_kite
  have hr : (0 : ℝ) < l14ω.radius := by norm_num [l14ω]
  have hc : l14Γ.center ≠ l14ω.center := l14_ne (by simp [l14Γ, l14ω])
  exact ⟨l14Γ, l14ω, l14A, hr, l14_inside, hc, l14_fuss_rel, hA,
    l14_exists_bicentric l14Γ l14ω hr l14_inside l14_fuss_rel hA⟩

/-- `ω'`: centre `0`, radius `1`; it lies inside `Γ` but violates Fuss's relation. -/
noncomputable def l14ω' : Sphere ℂ := ⟨0, 1⟩

/-- Witness for the three equivalences: for `Γ, ω` both sides hold (an explicit kite exists);
for `Γ, ω'` (also inside `Γ`) Fuss's relation fails, so by `l14_fuss_iff_exists` no bicentric
quadrilateral exists. Hence neither side of the equivalences is constant. -/
theorem l14w_fuss_iff :
    ∃ Γ ω ω' : Sphere ℂ, Γ.center ≠ ω.center ∧ ω ≠ ω' ∧
    (0 < ω.radius ∧ dist Γ.center ω.center + ω.radius < Γ.radius ∧
      (∃ A B C D : ℂ, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧
        ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A]) ∧
      (∀ A ∈ Γ, ∃ B C D : ℂ, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω.IsTangent line[ℝ, A, B] ∧ ω.IsTangent line[ℝ, B, C] ∧
        ω.IsTangent line[ℝ, C, D] ∧ ω.IsTangent line[ℝ, D, A])) ∧
    (0 < ω'.radius ∧ dist Γ.center ω'.center + ω'.radius < Γ.radius ∧
      (Γ.radius ^ 2 - dist Γ.center ω'.center ^ 2) ^ 2 ≠
        2 * ω'.radius ^ 2 * (Γ.radius ^ 2 + dist Γ.center ω'.center ^ 2) ∧
      ¬ ∃ A B C D : ℂ, A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧
        A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
        ω'.IsTangent line[ℝ, A, B] ∧ ω'.IsTangent line[ℝ, B, C] ∧
        ω'.IsTangent line[ℝ, C, D] ∧ ω'.IsTangent line[ℝ, D, A]) := by
  have : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨hA, hB, hC, hD, -⟩ := l14_kite
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := l14_kite_ne
  obtain ⟨t1, t2, t3, t4⟩ := l14_kite_tangent
  have hr : (0 : ℝ) < l14ω.radius := by norm_num [l14ω]
  have hex : ∃ A B C D : ℂ, A ∈ l14Γ ∧ B ∈ l14Γ ∧ C ∈ l14Γ ∧ D ∈ l14Γ ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D ∧
      l14ω.IsTangent line[ℝ, A, B] ∧ l14ω.IsTangent line[ℝ, B, C] ∧
      l14ω.IsTangent line[ℝ, C, D] ∧ l14ω.IsTangent line[ℝ, D, A] :=
    ⟨l14A, l14B, l14C, l14D, hA, hB, hC, hD, n1, n2, n3, n4, n5, n6, t1, t2, t3, t4⟩
  have hd' : dist l14Γ.center l14ω'.center = 1 :=
    l14_dist_eq (by norm_num) (by simp [l14Γ, l14ω'])
  have hr' : (0 : ℝ) < l14ω'.radius := by norm_num [l14ω']
  have hin' : dist l14Γ.center l14ω'.center + l14ω'.radius < l14Γ.radius := by
    rw [hd']; norm_num [l14Γ, l14ω']
  have hF' : (l14Γ.radius ^ 2 - dist l14Γ.center l14ω'.center ^ 2) ^ 2 ≠
      2 * l14ω'.radius ^ 2 * (l14Γ.radius ^ 2 + dist l14Γ.center l14ω'.center ^ 2) := by
    rw [hd']; norm_num [l14Γ, l14ω']
  have hc : l14Γ.center ≠ l14ω.center := l14_ne (by simp [l14Γ, l14ω])
  have hωω : l14ω ≠ l14ω' := fun h => by
    have := congrArg Sphere.radius h; norm_num [l14ω, l14ω'] at this
  refine ⟨l14Γ, l14ω, l14ω', hc, hωω,
    ⟨hr, l14_inside, hex, (l14_exists_iff_forall l14Γ l14ω hr l14_inside).1 hex⟩,
    hr', hin', hF', fun h => hF' ((l14_fuss_iff_exists l14Γ l14ω' hr' hin').1 h)⟩

/-- Witness for `l14_fuss_iff_reciprocal`: `R = 7, d = 1, r = 24/5` satisfies both sides
(`1/36 + 1/64 = 25/576`), and `r = 1` satisfies neither. -/
theorem l14w_fuss_iff_reciprocal :
    ((7 : ℝ) ^ 2 - 1 ^ 2) ^ 2 = 2 * (24 / 5) ^ 2 * (7 ^ 2 + 1 ^ 2) ∧
      1 / ((7 : ℝ) - 1) ^ 2 + 1 / (7 + 1) ^ 2 = 1 / (24 / 5) ^ 2 ∧
      ((7 : ℝ) ^ 2 - 1 ^ 2) ^ 2 ≠ 2 * 1 ^ 2 * (7 ^ 2 + 1 ^ 2) ∧
      1 / ((7 : ℝ) - 1) ^ 2 + 1 / (7 + 1) ^ 2 ≠ 1 / 1 ^ 2 := by
  have h := l14_fuss_iff_reciprocal (R := 7) (d := 1) (r := 24 / 5) (by norm_num) (by norm_num)
    (by norm_num)
  have h' := l14_fuss_iff_reciprocal (R := 7) (d := 1) (r := 1) (by norm_num) (by norm_num)
    (by norm_num)
  have e : ((7 : ℝ) ^ 2 - 1 ^ 2) ^ 2 = 2 * (24 / 5) ^ 2 * (7 ^ 2 + 1 ^ 2) := by norm_num
  have e' : ((7 : ℝ) ^ 2 - 1 ^ 2) ^ 2 ≠ 2 * 1 ^ 2 * (7 ^ 2 + 1 ^ 2) := by norm_num
  exact ⟨e, h.1 e, e', fun x => e' (h'.2 x)⟩

end Fuss
