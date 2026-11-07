/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Analytic
import LocallyConvexManifolds.BundleConnection
import LocallyConvexManifolds.Metric.Bilinear
import LocallyConvexManifolds.Symplectic

/-!
# Almost complex structures, complex manifolds and Kähler structures

* **Almost complex structures** (`AlmostComplexStructure`): a field `Jₓ` of real linear maps of
  the tangent spaces with `Jₓ² = −1`, with smooth local representatives
  `(y, v) ↦ J_i(y) v` (`jLocalRep`), stored, as metrics and forms, in the coordinates of the
  preferred chart at each point.
* **The Nijenhuis tensor** in local coordinates (`nijenhuisLoc`):
  `N(u, v) = (∂_{Ju} J) v − (∂_{Jv} J) u − J((∂_u J) v − (∂_v J) u)`. For local vector fields
  `[JX, JY] − J[JX, Y] − J[X, JY] − [X, Y] = N(X, Y)` (`localBracket_nijenhuis`): all the
  derivatives of `X` and `Y` cancel. `J` is **integrable** if `N` vanishes in every chart.
* **Complex manifolds**: on a complex analytic manifold (`ComplexAnalyticManifold`, in
  `LocallyConvexManifolds.Analytic`) multiplication by `i` in the charts is an almost complex
  structure (`canonicalJ`), because the derivatives of the transition maps are complex linear;
  it is integrable (`canonicalJ_isIntegrable`), since its local representatives are constant.
* **Kähler structures** (`KaehlerStructure`): an integrable `J` and a `J`-invariant, weakly
  nondegenerate symmetric bilinear field `g` whose **fundamental form**
  `ω(u, v) = g(J u, v)` (`fundamentalForm`) is closed. Then `ω` is a (weak) symplectic form
  (`KaehlerStructure.symplecticForm`).

**Infinite-dimensional subtleties.**
* `g` is only required to be weakly nondegenerate (`g(v, ·) = 0 ⇒ v = 0`), and it is not
  required to be positive: pseudo-Kähler metrics are included. Accordingly, `ω` is in general
  only a *weak* symplectic form.
* We do not formalize the converse of the integrability of complex structures. In finite
  dimensions it is the Newlander–Nirenberg theorem: an integrable almost complex structure comes
  from holomorphic charts. In infinite dimensions it fails: Lempert [Lem98, §2, pp. 489–490]
  points out loop spaces, modeled on Fréchet spaces, that carry integrable almost complex
  structures but are not locally biholomorphic to locally convex spaces, and he raises the case
  of Banach and Hilbert models as an open question there.

[Lem98]: L. Lempert, *The Dolbeault complex in infinite dimensions I*, J. Amer. Math. Soc. 11
(1998), 485–520.

No completeness of the model space is assumed.
-/

open Set Function Filter
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

/-! ### The Nijenhuis tensor in local coordinates -/

section Local

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The derivative of a field of endomorphisms in the base point: `(∂_w J)(y) ξ`. -/
def endD (J : E → E → E) (y w ξ : E) : E :=
  dMB (fun z ↦ J z ξ) (y, w)

/-- **The Nijenhuis tensor** of a field of endomorphisms in local coordinates:
`N(y)(u, v) = (∂_{Ju} J) v − (∂_{Jv} J) u − J((∂_u J) v − (∂_v J) u)`. -/
def nijenhuisLoc (J : E → E → E) (y u v : E) : E :=
  endD J y (J y u) v - endD J y (J y v) u - J y (endD J y u v - endD J y v u)

/-- The field `z ↦ J(z) X(z)`. -/
def endApply (J : E → E → E) (X : E → E) (z : E) : E :=
  J z (X z)

/-- **The Nijenhuis tensor and brackets**: for a field `J` of endomorphisms with `J² = −1` on an
open set `U` and `C¹` local fields `X`, `Y`,
`[JX, JY] − J[JX, Y] − J[X, JY] − [X, Y] = N(X, Y)`. All the derivatives of `X` and `Y` cancel,
so the left side is tensorial. -/
theorem localBracket_nijenhuis {J : E → E → E} {U : Set E} (hU : IsOpen U)
    (hJ : ContDiffMBOn 1 (fun p : E × E ↦ J p.1 p.2) (U ×ˢ univ))
    (hadd : ∀ y ∈ U, ∀ ξ η, J y (ξ + η) = J y ξ + J y η)
    (hsmul : ∀ y ∈ U, ∀ (c : ℝ) ξ, J y (c • ξ) = c • J y ξ)
    (hsq : ∀ y ∈ U, ∀ ξ, J y (J y ξ) = -ξ) {X Y : E → E} (hX : ContDiffMBOn 1 X U)
    (hY : ContDiffMBOn 1 Y U) {y : E} (hy : y ∈ U) :
    localBracket (endApply J X) (endApply J Y) y - J y (localBracket (endApply J X) Y y) -
        J y (localBracket X (endApply J Y) y) - localBracket X Y y =
      nijenhuisLoc J y (X y) (Y y) := by
  -- the product rule for `JX` and `JY`
  have hd : ∀ {A : E → E}, ContDiffMBOn 1 A U → ∀ w,
      dMB (endApply J A) (y, w) = endD J y w (A y) + J y (dMB A (y, w)) := fun hA w ↦
    dMB_fiber_comp hU hU subset_rfl hJ hadd hsmul hA hy w
  set L : E →ₗ[ℝ] E := ⟨⟨J y, hadd y hy⟩, hsmul y hy⟩
  have hL : ∀ ξ, J y ξ = L ξ := fun _ ↦ rfl
  have hLL : ∀ ξ, L (L ξ) = -ξ := hsq y hy
  simp only [localBracket, hd hX, hd hY, endApply, nijenhuisLoc, hL, map_sub, map_add, hLL]
  abel

end Local

/-! ### Almost complex structures -/

section Almost

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The local representative of a field `J` of endomorphisms of the tangent spaces in the chart
`i`: `(y, v) ↦ J_i(y) v`, with `x = i⁻¹ y` and `v` read in the chart `i`. -/
def jLocalRep (J : M → E → E) (i : atlas E M) (p : E × E) : E :=
  tangentCoordChange (prefChart (i.1.symm p.1)) i (i.1.symm p.1)
    (J (i.1.symm p.1) (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) p.2))

variable (E M) in
/-- An **almost complex structure**: a field of real linear maps `Jₓ` of the tangent spaces
with `Jₓ² = −1`, whose local representatives are smooth. -/
structure AlmostComplexStructure where
  /-- The map `Jₓ` on `T_x M`, in the coordinates of the preferred chart at `x`. -/
  toFun : M → E →ₗ[ℝ] E
  sq' : ∀ x v, toFun x (toFun x v) = -v
  smooth' : ∀ i : atlas E M, SmoothMBOn (jLocalRep (fun x ↦ toFun x) i) (i.1.target ×ˢ univ)

namespace AlmostComplexStructure

variable (J : AlmostComplexStructure E M)

/-- The local representative `J_i : (y, v) ↦ J_i(y) v` in the chart `i`. -/
def loc (i : atlas E M) (y v : E) : E :=
  jLocalRep (fun x ↦ J.toFun x) i (y, v)

theorem loc_eq (i : atlas E M) {y : E} (hy : y ∈ i.1.target) :
    ∃ T S : E →ₗ[ℝ] E, (∀ v, J.loc i y v = S (J.toFun (i.1.symm y) (T v))) ∧
      (∀ v, T (S v) = v) ∧ (∀ v, S (T v) = v) ∧
      ∀ v, tangentCoordChange i (prefChart (i.1.symm y)) (i.1.symm y) v = T v := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source := i.1.map_target hy
  have hxp : x ∈ (prefChart (E := E) x).1.source := mem_chart_source E x
  obtain ⟨T, hT⟩ := exists_linear_tangentCoordChange i (prefChart x) ⟨hx, hxp⟩
  obtain ⟨S, hS⟩ := exists_linear_tangentCoordChange (prefChart x) i ⟨hxp, hx⟩
  refine ⟨T, S, fun v ↦ by simp only [loc, jLocalRep, hT, hS, x], fun v ↦ ?_, fun v ↦ ?_, hT⟩
  · rw [← hS, ← hT, tangentCoordChange_comp _ _ _ ⟨⟨hxp, hx⟩, hxp⟩,
      tangentCoordChange_self _ hxp]
  · rw [← hS, ← hT, tangentCoordChange_comp _ _ _ ⟨⟨hx, hxp⟩, hx⟩,
      tangentCoordChange_self _ hx]

theorem loc_add (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (ξ η : E) :
    J.loc i y (ξ + η) = J.loc i y ξ + J.loc i y η := by
  obtain ⟨T, S, h, -, -, -⟩ := J.loc_eq i hy
  simp only [h, map_add]

theorem loc_smul (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (c : ℝ) (ξ : E) :
    J.loc i y (c • ξ) = c • J.loc i y ξ := by
  obtain ⟨T, S, h, -, -, -⟩ := J.loc_eq i hy
  simp only [h, map_smul]

theorem loc_sq (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (ξ : E) :
    J.loc i y (J.loc i y ξ) = -ξ := by
  obtain ⟨T, S, h, hTS, hST, -⟩ := J.loc_eq i hy
  rw [h, h, hTS, J.sq', map_neg, hST]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The local representatives are smooth. -/
theorem smoothMBOn_loc (i : atlas E M) :
    SmoothMBOn (fun p : E × E ↦ J.loc i p.1 p.2) (i.1.target ×ˢ univ) :=
  J.smooth' i

/-- `J` is **integrable** if its Nijenhuis tensor vanishes in every chart. -/
def IsIntegrable : Prop :=
  ∀ (i : atlas E M), ∀ y ∈ i.1.target, ∀ u v, nijenhuisLoc (J.loc i) y u v = 0

end AlmostComplexStructure

end Almost

/-! ### The almost complex structure of a complex manifold -/

section ComplexManifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E]

attribute [local instance] continuousSMul_real_of_complex

variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  [ComplexAnalyticManifold E M]

omit [MBManifold E M] in
/-- **The tangent maps of a complex manifold are complex linear**: the derivatives of the
transition maps, which are complex analytic, commute with multiplication by complex scalars. -/
theorem tangentCoordChange_complex_smul (i j : atlas E M) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source) (c : ℂ) (v : E) :
    tangentCoordChange i j x (c • v) = c • tangentCoordChange i j x v := by
  have hT := complexAnalyticOn_transition
    (StructureGroupoid.subset_maximalAtlas (complexAnalyticGroupoid E) i.2)
    (StructureGroupoid.subset_maximalAtlas (complexAnalyticGroupoid E) j.2)
  have hol := (complexAnalyticOn_iff_holomorphicOn (isOpen_transition_domain i j)).1 hT
  exact hol.2 (i.1 x) ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ c v

variable (E) in
/-- Multiplication by `i`, as a real continuous linear map. -/
def mulI : E →L[ℝ] E where
  toFun v := (Complex.I : ℂ) • v
  map_add' := smul_add _
  map_smul' c v := by
    simp only [RingHom.id_apply]
    exact smul_comm _ _ _
  cont := continuous_const_smul _

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem mulI_apply (v : E) : mulI E v = (Complex.I : ℂ) • v :=
  rfl

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem mulI_mulI (v : E) : mulI E (mulI E v) = -v := by
  simp only [mulI_apply, smul_smul, Complex.I_mul_I, neg_smul, one_smul]

variable (E M) in
/-- **The almost complex structure of a complex manifold**: multiplication by `i` in the charts.
It is well defined because the tangent maps of the transition maps are complex linear. -/
def canonicalJ : AlmostComplexStructure E M where
  toFun _ := (mulI E : E →L[ℝ] E).toLinearMap
  sq' _ v := mulI_mulI v
  smooth' i k := by
    refine ContDiffMBOn.congr_of_isOpen (i.1.open_target.prod isOpen_univ) (fun p hp ↦ ?_)
      (((mulI E).comp (ContinuousLinearMap.snd ℝ E E)).contDiffMBOn k _)
    set x := i.1.symm p.1
    have hx : x ∈ i.1.source := i.1.map_target hp.1
    have hxp : x ∈ (prefChart (E := E) x).1.source := mem_chart_source E x
    change mulI E p.2 = tangentCoordChange (prefChart x) i x
      (mulI E (tangentCoordChange i (prefChart x) x p.2))
    rw [mulI_apply, mulI_apply, tangentCoordChange_complex_smul _ _ ⟨hxp, hx⟩,
      tangentCoordChange_comp _ _ _ ⟨⟨hx, hxp⟩, hx⟩, tangentCoordChange_self _ hx]

/-- In every chart, the local representative of the canonical almost complex structure is
multiplication by `i`. -/
theorem canonicalJ_loc (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : E) :
    (canonicalJ E M).loc i y v = mulI E v := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source := i.1.map_target hy
  have hxp : x ∈ (prefChart (E := E) x).1.source := mem_chart_source E x
  change tangentCoordChange (prefChart x) i x (mulI E (tangentCoordChange i (prefChart x) x v)) =
    mulI E v
  rw [mulI_apply, mulI_apply, tangentCoordChange_complex_smul _ _ ⟨hxp, hx⟩,
    tangentCoordChange_comp _ _ _ ⟨⟨hx, hxp⟩, hx⟩, tangentCoordChange_self _ hx]

/-- **The almost complex structure of a complex manifold is integrable**: its local
representatives are constant, so its Nijenhuis tensor vanishes. -/
theorem canonicalJ_isIntegrable : (canonicalJ E M).IsIntegrable := by
  intro i y hy u v
  have hD : ∀ w ξ, endD ((canonicalJ E M).loc i) y w ξ = 0 := fun w ξ ↦ by
    have hev : (fun z ↦ (canonicalJ E M).loc i z ξ) =ᶠ[𝓝 y] fun _ ↦ mulI E ξ :=
      eventuallyEq_of_mem (i.1.open_target.mem_nhds hy) fun z hz ↦ canonicalJ_loc i hz ξ
    have hc0 : HasDirDerivAt (fun _ : E ↦ mulI E ξ) y w 0 :=
      tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)
    rw [endD, dMB_congr_of_eventuallyEq hev, hc0.dMB_eq]
  simp only [nijenhuisLoc, hD, sub_self, canonicalJ_loc i hy, map_zero]

end ComplexManifold

/-! ### Hermitian and Kähler structures -/

section Kaehler

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The alternating `2`-linear map `(v₀, v₁) ↦ B(v₀, v₁)` of a bilinear map vanishing on the
diagonal. -/
def altOfBilin (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ v, B v v = 0) : E [⋀^Fin 2]→ₗ[ℝ] ℝ where
  toFun v := B (v 0) (v 1)
  map_update_add' v i a b := by
    rename_i inst
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp
  map_update_smul' v i c a := by
    rename_i inst
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at hv ⊢
      rw [← hv]
      exact hB _
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta] at hv ⊢
      rw [hv]
      exact hB _
    · exact absurd rfl hij

variable (E M) in
/-- A **Hermitian structure** (possibly indefinite): an almost complex structure `J` and a smooth
field `g` of symmetric bilinear forms with `g(J u, J v) = g(u, v)`. -/
structure HermitianStructure where
  /-- The almost complex structure. -/
  J : AlmostComplexStructure E M
  /-- The `J`-invariant symmetric bilinear field. -/
  g : SymmBilinField E M
  compat : ∀ x v w, g.toFun x (J.toFun x v) (J.toFun x w) = g.toFun x v w

namespace HermitianStructure

variable (h : HermitianStructure E M)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- `g(J v, v) = 0`. -/
theorem g_J_self (x : M) (v : E) : h.g.toFun x (h.J.toFun x v) v = 0 := by
  have h1 := h.compat x (h.J.toFun x v) v
  rw [h.J.sq', LinearMap.map_neg, LinearMap.neg_apply, h.g.symm' x v] at h1
  linarith

/-- **The fundamental form** `ω(u, v) = g(J u, v)`. -/
def fundamentalForm : DifferentialForm E M ℝ 2 where
  toFun x v := h.g.toFun x (h.J.toFun x (v 0)) (v 1)
  alternating' x :=
    ⟨altOfBilin (LinearMap.comp (h.g.toFun x) (h.J.toFun x)) (h.g_J_self x), fun _ ↦ rfl⟩
  smooth' i k := by
    have hUU : IsOpen (i.1.target ×ˢ (univ : Set (Fin 2 → E))) :=
      i.1.open_target.prod isOpen_univ
    have hfst : ContDiffMBOn k (fun p : E × (Fin 2 → E) ↦ p.1) (i.1.target ×ˢ univ) :=
      (ContinuousLinearMap.fst ℝ E (Fin 2 → E)).contDiffMBOn k _
    have hv : ∀ m : Fin 2, ContDiffMBOn k (fun p : E × (Fin 2 → E) ↦ p.2 m)
        (i.1.target ×ˢ univ) := fun m ↦
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) m).comp
        (ContinuousLinearMap.snd ℝ E (Fin 2 → E))).contDiffMBOn k _
    have hJ : ContDiffMBOn k (fun p : E × (Fin 2 → E) ↦ h.J.loc i p.1 (p.2 0))
        (i.1.target ×ˢ univ) :=
      ContDiffMBOn.comp (g := fun q : E × E ↦ h.J.loc i q.1 q.2)
        (f := fun p : E × (Fin 2 → E) ↦ (p.1, p.2 0)) hUU (i.1.open_target.prod isOpen_univ)
        (h.J.smoothMBOn_loc i k) (hfst.prodMk hUU (hv 0)) fun p hp ↦ ⟨hp.1, mem_univ _⟩
    have hg := ContDiffMBOn.comp (g := bilinLocalRep h.g.toFun i)
      (f := fun p : E × (Fin 2 → E) ↦ (p.1, h.J.loc i p.1 (p.2 0), p.2 1)) hUU
      (i.1.open_target.prod isOpen_univ) (h.g.smooth' i k)
      (hfst.prodMk hUU (hJ.prodMk hUU (hv 1))) fun p hp ↦ ⟨hp.1, mem_univ _⟩
    refine ContDiffMBOn.congr_of_isOpen hUU (fun p hp ↦ ?_) hg
    obtain ⟨T, S, hloc, hTS, -, hT⟩ := h.J.loc_eq i hp.1
    change h.g.toFun (i.1.symm p.1)
        (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) (h.J.loc i p.1 (p.2 0)))
        (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) (p.2 1)) =
      h.g.toFun (i.1.symm p.1)
        (h.J.toFun (i.1.symm p.1)
          (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) (p.2 0)))
        (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) (p.2 1))
    rw [hT, hT, hT, hloc, hTS]

theorem fundamentalForm_apply (x : M) (u v : E) :
    h.fundamentalForm x ![u, v] = h.g.toFun x (h.J.toFun x u) v :=
  rfl

end HermitianStructure

variable (E M) in
/-- A **Kähler structure** (possibly indefinite): a Hermitian structure whose almost complex
structure is integrable, whose metric is weakly nondegenerate, and whose fundamental form is
closed. -/
structure KaehlerStructure extends HermitianStructure E M where
  integrable : J.IsIntegrable
  nondegenerate : g.IsWeaklyNondegenerate
  closed : toHermitianStructure.fundamentalForm.IsClosed

/-- **The fundamental form of a Kähler structure is a (weak) symplectic form.** Integrability is
not needed: almost Kähler structures are already symplectic. -/
def KaehlerStructure.symplecticForm (K : KaehlerStructure E M) : SymplecticForm E M where
  form := K.fundamentalForm
  isClosed := K.closed
  nondegenerate x v hv := by
    have hJv : K.J.toFun x v = 0 := K.nondegenerate x _ fun w ↦ hv w
    rw [← neg_neg v, ← K.J.sq' x v, hJv, map_zero, neg_zero]

end Kaehler

end LocallyConvex.Manifolds
