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
# Nijenhuis operators, almost complex structures, complex manifolds and Kähler structures

* **Fields of endomorphisms** (`EndomorphismField`): a field `Nₓ` of real linear maps of the
  tangent spaces with smooth local representatives `(y, v) ↦ N_i(y) v` (`jLocalRep`), stored, as
  metrics and forms, in the coordinates of the preferred chart at each point.
* **The Nijenhuis torsion**, with the convention of Goliński–Larotonda–Tumpach [GLT, Definition
  3.1]: `Ω_N(X, Y) = N[NX, Y] + N[X, NY] − [NX, NY] − N²[X, Y]`. In local coordinates
  (`nijenhuisLoc`) it is
  `Ω_N(u, v) = N((∂_u N) v − (∂_v N) u) + (∂_{Nv} N) u − (∂_{Nu} N) v`
  (`localBracket_nijenhuis`, [GLT, Theorem 3.2]): all the derivatives of the fields cancel.
  Globally, `EndomorphismField.lieBracket_nijenhuis`: the torsion of two vector fields at `x`
  only depends on their values at `x`.
* **Almost complex structures** (`AlmostComplexStructure`): `Jₓ² = −1`. `J` is **integrable**
  if its Nijenhuis torsion vanishes. On a complex analytic manifold (`ComplexAnalyticManifold`,
  in `LocallyConvexManifolds.Analytic`) multiplication by `i` in the charts is an almost complex
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
* We do not formalize the converse of the integrability of complex structures, which in finite
  dimensions is the Newlander–Nirenberg theorem (Ann. of Math. 65 (1957), 391–404). In infinite dimensions:
  - it holds for real analytic almost complex structures on real analytic Banach manifolds
    (Beltiță [Bel05, Theorem 7]);
  - it fails for smooth structures on some Banach manifolds (Patyi [Pat99, Theorem 3.1, p. 401]);
  - it fails on some Fréchet manifolds: Lempert [Lem98, §2, pp. 489–490] points out loop spaces
    with integrable almost complex structures that are not locally biholomorphic to locally
    convex spaces.

[GLT]: T. Goliński, G. Larotonda, A. B. Tumpach, *Nijenhuis operators on Banach homogeneous
spaces*, Rend. Lincei Mat. Appl. (online first), doi:10.4171/RLM/1057; arXiv:2410.13557.
[Bel05]: D. Beltiță, *Integrability of analytic almost complex structures on Banach manifolds*,
Ann. Global Anal. Geom. 28 (2005), 59–73.
[Pat99]: I. Patyi, *On the ∂̄-equation in a Banach space*, Bull. Soc. Math. France 128 (2000),
391–406.
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

/-! ### The Nijenhuis torsion in local coordinates -/

section Local

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The derivative of a field of endomorphisms in the base point: `(∂_w N)(y) ξ`. -/
def endD (N : E → E → E) (y w ξ : E) : E :=
  dMB (fun z ↦ N z ξ) (y, w)

/-- **The Nijenhuis torsion** of a field of endomorphisms in local coordinates, with the
convention of [GLT, Theorem 3.2]:
`Ω_N(y)(u, v) = N((∂_u N) v − (∂_v N) u) + (∂_{Nv} N) u − (∂_{Nu} N) v`. -/
def nijenhuisLoc (N : E → E → E) (y u v : E) : E :=
  N y (endD N y u v - endD N y v u) + endD N y (N y v) u - endD N y (N y u) v

/-- The field `z ↦ N(z) X(z)`. -/
def endApply (N : E → E → E) (X : E → E) (z : E) : E :=
  N z (X z)

/-- **The Nijenhuis torsion and brackets** [GLT, Theorem 3.2]: for a smooth field `N` of
endomorphisms on an open set `U` and `C¹` local fields `X`, `Y`,
`N[NX, Y] + N[X, NY] − [NX, NY] − N²[X, Y] = Ω_N(X, Y)`. All the derivatives of `X` and `Y`
cancel, so the left side is tensorial. -/
theorem localBracket_nijenhuis {N : E → E → E} {U : Set E} (hU : IsOpen U)
    (hN : ContDiffMBOn 1 (fun p : E × E ↦ N p.1 p.2) (U ×ˢ univ))
    (hadd : ∀ y ∈ U, ∀ ξ η, N y (ξ + η) = N y ξ + N y η)
    (hsmul : ∀ y ∈ U, ∀ (c : ℝ) ξ, N y (c • ξ) = c • N y ξ) {X Y : E → E}
    (hX : ContDiffMBOn 1 X U) (hY : ContDiffMBOn 1 Y U) {y : E} (hy : y ∈ U) :
    N y (localBracket (endApply N X) Y y) + N y (localBracket X (endApply N Y) y) -
        localBracket (endApply N X) (endApply N Y) y - N y (N y (localBracket X Y y)) =
      nijenhuisLoc N y (X y) (Y y) := by
  -- the product rule for `NX` and `NY`
  have hd : ∀ {A : E → E}, ContDiffMBOn 1 A U → ∀ w,
      dMB (endApply N A) (y, w) = endD N y w (A y) + N y (dMB A (y, w)) := fun hA w ↦
    dMB_fiber_comp hU hU subset_rfl hN hadd hsmul hA hy w
  set L : E →ₗ[ℝ] E := ⟨⟨N y, hadd y hy⟩, hsmul y hy⟩
  have hL : ∀ ξ, N y ξ = L ξ := fun _ ↦ rfl
  simp only [localBracket, hd hX, hd hY, endApply, nijenhuisLoc, hL, map_sub, map_add]
  abel

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Local brackets only depend on the germs of the fields. -/
theorem localBracket_congr {A A' B B' : E → E} {y : E} (hA : A =ᶠ[𝓝 y] A')
    (hB : B =ᶠ[𝓝 y] B') : localBracket A B y = localBracket A' B' y := by
  rw [localBracket, localBracket, dMB_congr_of_eventuallyEq hB, dMB_congr_of_eventuallyEq hA,
    hA.eq_of_nhds, hB.eq_of_nhds]

end Local

/-! ### Fields of endomorphisms and almost complex structures -/

section Almost

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The local representative of a field `N` of endomorphisms of the tangent spaces in the chart
`i`: `(y, v) ↦ N_i(y) v`, with `x = i⁻¹ y` and `v` read in the chart `i`. -/
def jLocalRep (N : M → E → E) (i : atlas E M) (p : E × E) : E :=
  tangentCoordChange (prefChart (i.1.symm p.1)) i (i.1.symm p.1)
    (N (i.1.symm p.1) (tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) p.2))

variable (E M) in
/-- A **smooth field of endomorphisms** of the tangent bundle: real linear maps `Nₓ` of the
tangent spaces whose local representatives are smooth. -/
structure EndomorphismField where
  /-- The map `Nₓ` on `T_x M`, in the coordinates of the preferred chart at `x`. -/
  toFun : M → E →ₗ[ℝ] E
  smooth' : ∀ i : atlas E M, SmoothMBOn (jLocalRep (fun x ↦ toFun x) i) (i.1.target ×ˢ univ)

namespace EndomorphismField

variable (N : EndomorphismField E M)

/-- The local representative `N_i : (y, v) ↦ N_i(y) v` in the chart `i`. -/
def loc (i : atlas E M) (y v : E) : E :=
  jLocalRep (fun x ↦ N.toFun x) i (y, v)

theorem loc_eq (i : atlas E M) {y : E} (hy : y ∈ i.1.target) :
    ∃ T S : E →ₗ[ℝ] E, (∀ v, N.loc i y v = S (N.toFun (i.1.symm y) (T v))) ∧
      (∀ v, T (S v) = v) ∧ (∀ v, S (T v) = v) ∧
      (∀ v, tangentCoordChange i (prefChart (i.1.symm y)) (i.1.symm y) v = T v) ∧
      ∀ v, tangentCoordChange (prefChart (i.1.symm y)) i (i.1.symm y) v = S v := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source := i.1.map_target hy
  have hxp : x ∈ (prefChart (E := E) x).1.source := mem_chart_source E x
  obtain ⟨T, hT⟩ := exists_linear_tangentCoordChange i (prefChart x) ⟨hx, hxp⟩
  obtain ⟨S, hS⟩ := exists_linear_tangentCoordChange (prefChart x) i ⟨hxp, hx⟩
  refine ⟨T, S, fun v ↦ by simp only [loc, jLocalRep, hT, hS, x], fun v ↦ ?_, fun v ↦ ?_, hT,
    hS⟩
  · rw [← hS, ← hT, tangentCoordChange_comp _ _ _ ⟨⟨hxp, hx⟩, hxp⟩,
      tangentCoordChange_self _ hxp]
  · rw [← hS, ← hT, tangentCoordChange_comp _ _ _ ⟨⟨hx, hxp⟩, hx⟩,
      tangentCoordChange_self _ hx]

theorem loc_add (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (ξ η : E) :
    N.loc i y (ξ + η) = N.loc i y ξ + N.loc i y η := by
  obtain ⟨T, S, h, -, -, -, -⟩ := N.loc_eq i hy
  simp only [h, map_add]

theorem loc_smul (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (c : ℝ) (ξ : E) :
    N.loc i y (c • ξ) = c • N.loc i y ξ := by
  obtain ⟨T, S, h, -, -, -, -⟩ := N.loc_eq i hy
  simp only [h, map_smul]

omit [LocallyConvexSpace ℝ E] [MBManifold E M] in
/-- In the preferred chart at `x`, the local representative at `x` is `Nₓ` itself. -/
theorem loc_pref (x : M) (v : E) : N.loc (prefChart x) (chartAt E x x) v = N.toFun x v := by
  have hx : (chartAt E x).symm (chartAt E x x) = x := (chartAt E x).left_inv (mem_chart_source E x)
  simp only [loc, jLocalRep, hx]
  rw [tangentCoordChange_self _ (mem_chart_source E x),
    tangentCoordChange_self _ (mem_chart_source E x)]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The local representatives are smooth. -/
theorem smoothMBOn_loc (i : atlas E M) :
    SmoothMBOn (fun p : E × E ↦ N.loc i p.1 p.2) (i.1.target ×ˢ univ) :=
  N.smooth' i

/-- The Nijenhuis torsion `Ω_N` at `x`, on vectors of `T_x M`, computed in the preferred chart. -/
def nijenhuisAt (x : M) (u v : E) : E :=
  nijenhuisLoc (N.loc (prefChart x)) (chartAt E x x) u v

/-- The field `x ↦ Nₓ X(x)`. -/
def applyField (X : M → TangentBundle E M) (x : M) : TangentBundle E M :=
  ⟨x, N.toFun x (X x).2⟩

theorem isVectorField_applyField (X : M → TangentBundle E M) : IsVectorField (N.applyField X) :=
  fun _ ↦ rfl

/-- The local representative of `NX` is `N_i X_i`. -/
theorem localRep_applyField {X : M → TangentBundle E M} (hXv : IsVectorField X) (i : atlas E M)
    {y : E} (hy : y ∈ i.1.target) :
    localRep i (N.applyField X) y = N.loc i y (localRep i X y) := by
  obtain ⟨T, S, h, hTS, -, -, hS⟩ := N.loc_eq i hy
  have e1 : localRep i X y =
      tangentCoordChange (prefChart (i.1.symm y)) i (i.1.symm y) (X (i.1.symm y)).2 := by
    unfold localRep
    rw [tangentChart_apply]
    have hp : (X (i.1.symm y)).proj = i.1.symm y := hXv _
    generalize X (i.1.symm y) = p at hp ⊢
    obtain ⟨xp, w⟩ := p
    change xp = i.1.symm y at hp
    subst hp
    rfl
  have e2 : localRep i (N.applyField X) y =
      tangentCoordChange (prefChart (i.1.symm y)) i (i.1.symm y)
        (N.toFun (i.1.symm y) (X (i.1.symm y)).2) :=
    rfl
  have e1' : localRep i X y = S (X (i.1.symm y)).2 := e1.trans (hS _)
  rw [e2, e1', h, hTS (X (i.1.symm y)).2]
  exact hS _

/-- **The Nijenhuis torsion is a tensor** [GLT, Theorem 3.2]: for `C¹` vector fields,
`N[NX, Y] + N[X, NY] − [NX, NY] − N²[X, Y]` at `x` is `Ω_N(X(x), Y(x))`. -/
theorem lieBracket_nijenhuis {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hX : ContMDiffMB E (E × E) 1 X) (hY : ContMDiffMB E (E × E) 1 Y)
    (x : M) :
    N.toFun x (show E from (lieBracket (N.applyField X) Y x).2) +
        N.toFun x (show E from (lieBracket X (N.applyField Y) x).2) -
        (show E from (lieBracket (N.applyField X) (N.applyField Y) x).2) -
        N.toFun x (N.toFun x (show E from (lieBracket X Y x).2)) =
      N.nijenhuisAt x (X x).2 (Y x).2 := by
  have hy0 : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  have hev : ∀ {A : M → TangentBundle E M}, IsVectorField A →
      localRep (prefChart x) (N.applyField A) =ᶠ[𝓝 (chartAt E x x)]
        endApply (N.loc (prefChart x)) (localRep (prefChart x) A) := fun hAv ↦
    eventuallyEq_of_mem ((prefChart (E := E) x).1.open_target.mem_nhds hy0) fun z hz ↦
      N.localRep_applyField hAv _ hz
  have hbr : ∀ A B : M → TangentBundle E M, (show E from (lieBracket A B x).2) =
      localBracket (localRep (prefChart x) A) (localRep (prefChart x) B) (chartAt E x x) :=
    fun _ _ ↦ rfl
  simp only [hbr, ← N.loc_pref x]
  rw [localBracket_congr (hev hXv) EventuallyEq.rfl, localBracket_congr EventuallyEq.rfl (hev hYv),
    localBracket_congr (hev hXv) (hev hYv)]
  have h := localBracket_nijenhuis (prefChart (E := E) x).1.open_target (N.smoothMBOn_loc _ 1)
    (fun _ hz ↦ N.loc_add _ hz) (fun _ hz ↦ N.loc_smul _ hz) (contDiffMBOn_localRep hXv hX _)
    (contDiffMBOn_localRep hYv hY _) hy0
  rw [localRep_chartAt hXv x, localRep_chartAt hYv x] at h
  exact h

end EndomorphismField

variable (E M) in
/-- An **almost complex structure**: a smooth field of endomorphisms with `Jₓ² = −1`. -/
structure AlmostComplexStructure extends EndomorphismField E M where
  sq' : ∀ x v, toFun x (toFun x v) = -v

namespace AlmostComplexStructure

variable (J : AlmostComplexStructure E M)

theorem loc_sq (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (ξ : E) :
    J.loc i y (J.loc i y ξ) = -ξ := by
  obtain ⟨T, S, h, hTS, hST, -, -⟩ := J.loc_eq i hy
  rw [h, h, hTS, J.sq', map_neg, hST]

/-- `J` is **integrable** if its Nijenhuis torsion vanishes in every chart. -/
def IsIntegrable : Prop :=
  ∀ (i : atlas E M), ∀ y ∈ i.1.target, ∀ u v, nijenhuisLoc (J.loc i) y u v = 0

/-- For an integrable almost complex structure,
`J[JX, Y] + J[X, JY] − [JX, JY] + [X, Y] = 0` for all `C¹` vector fields. -/
theorem IsIntegrable.lieBracket {J : AlmostComplexStructure E M} (hJ : J.IsIntegrable)
    {X Y : M → TangentBundle E M} (hXv : IsVectorField X) (hYv : IsVectorField Y)
    (hX : ContMDiffMB E (E × E) 1 X) (hY : ContMDiffMB E (E × E) 1 Y) (x : M) :
    J.toFun x (show E from (lieBracket (J.applyField X) Y x).2) +
        J.toFun x (show E from (lieBracket X (J.applyField Y) x).2) -
        (show E from (lieBracket (J.applyField X) (J.applyField Y) x).2) +
        (show E from (lieBracket X Y x).2) = 0 := by
  have h := J.lieBracket_nijenhuis hXv hYv hX hY x
  rw [J.sq', sub_neg_eq_add] at h
  rw [h]
  exact hJ _ _ ((chartAt E x).map_source (mem_chart_source E x)) _ _

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
  simp only [nijenhuisLoc, hD, sub_self, canonicalJ_loc i hy, map_zero, add_zero]

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
    obtain ⟨T, S, hloc, hTS, -, hT, -⟩ := h.J.loc_eq i hp.1
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

/-! ### Example: the flat Kähler structure of a complex inner product space -/

section Flat

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (E) in
/-- The real part of the inner product, `g(v, w) = Re ⟨v, w⟩`, as a real bilinear form. -/
def reInner : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w ↦ (inner ℂ v w).re)
    (fun v v' w ↦ by simp) (fun c v w ↦ by simp) (fun v w w' ↦ by simp)
    (fun c v w ↦ by simp)

theorem reInner_apply (v w : E) : reInner E v w = (inner ℂ v w).re :=
  rfl

theorem continuous_reInner : Continuous fun p : E × E ↦ reInner E p.1 p.2 :=
  Complex.continuous_re.comp (continuous_fst.inner continuous_snd)

variable (E) in
/-- The flat metric `Re ⟨·, ·⟩` on the model space. -/
def flatMetric : SymmBilinField E E where
  toFun _ := reInner E
  symm' _ v w := by
    simp only [reInner_apply]
    rw [← inner_conj_symm, Complex.conj_re]
  smooth' i k := by
    have hU : IsOpen (i.1.target ×ˢ (univ : Set (E × E))) := i.1.open_target.prod isOpen_univ
    refine ContDiffMBOn.congr_of_isOpen hU (fun q _ ↦ ?_)
      (ContDiffMBOn.bilin (reInner E) continuous_reInner hU
        (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).contDiffMBOn
          k _)
        (((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).contDiffMBOn
          k _))
    have hi : i.1.symm q.1 ∈ i.1.source := by rw [atlas_self i]; trivial
    simp only [bilinLocalRep, prefAtlas]
    change reInner E q.2.1 q.2.2 = reInner E
      (tangentCoordChange i (prefChart (E := E) (i.1.symm q.1)) (i.1.symm q.1) q.2.1)
      (tangentCoordChange i (prefChart (E := E) (i.1.symm q.1)) (i.1.symm q.1) q.2.2)
    rw [prefChart_self i, tangentCoordChange_self i hi, tangentCoordChange_self i hi]

variable (E) in
/-- The flat Hermitian structure `(J, g) = (i, Re ⟨·, ·⟩)` on the model space. -/
def flatHermitian : HermitianStructure E E where
  J := canonicalJ E E
  g := flatMetric E
  compat _ v w := by
    change (inner ℂ ((Complex.I : ℂ) • v) ((Complex.I : ℂ) • w)).re = (inner ℂ v w).re
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_I, neg_mul, Complex.I_mul_I,
      neg_neg, one_mul]

/-- The fundamental form of the flat Hermitian structure is closed: its local representative
does not depend on the base point. -/
theorem flatHermitian_isClosed : (flatHermitian E).fundamentalForm.IsClosed := by
  intro x w
  have hloc : ∀ (z : E) (u : Fin 2 → E), (flatHermitian E).fundamentalForm.localRep
      (prefChart x) (z, u) = (inner ℂ ((Complex.I : ℂ) • u 0) (u 1)).re := fun z u ↦ by
    rw [DifferentialForm.localRep, formLocalRep_self]
    rfl
  change dLoc ((flatHermitian E).fundamentalForm.localRep (prefChart x)) (chartAt E x x, w) = 0
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hc0 : HasDirDerivAt
      (fun z : E ↦ (flatHermitian E).fundamentalForm.localRep (prefChart x) (z, k.removeNth w))
      (chartAt E x x) (w k) 0 :=
    tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp [hloc])
  rw [hc0.dMB_eq, smul_zero]

variable (E) in
/-- **The flat Kähler structure** of a complex inner product space: `J = i`,
`g = Re ⟨·, ·⟩`, and fundamental form `ω(u, v) = Im ⟨u, v⟩` (`flatKaehler_form_apply`). No
completeness is needed. -/
def flatKaehler : KaehlerStructure E E where
  toHermitianStructure := flatHermitian E
  integrable := canonicalJ_isIntegrable
  nondegenerate _ v hv := by
    have h := hv v
    change (inner ℂ v v).re = 0 at h
    have h' : ‖v‖ ^ 2 = 0 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact h
    rwa [sq_eq_zero_iff, norm_eq_zero] at h'
  closed := flatHermitian_isClosed

/-- The fundamental form of the flat Kähler structure is `ω(u, v) = Im ⟨u, v⟩`. -/
theorem flatKaehler_form_apply (x u v : E) :
    (flatKaehler E).symplecticForm.form x ![u, v] = (inner ℂ u v).im := by
  change (inner ℂ ((Complex.I : ℂ) • u) v).re = (inner ℂ u v).im
  rw [inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

end Flat

end LocallyConvex.Manifolds
