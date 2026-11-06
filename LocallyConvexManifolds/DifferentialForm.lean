/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.LocalForm
import LocallyConvexManifolds.TangentMap

/-!
# Differential forms and the exterior derivative

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, §3.6.

Let `M` be a manifold modeled on a locally convex space `E`, and `F` a locally convex space.
An `F`-valued `n`-form `ω` on `M` assigns to each `x ∈ M` an alternating `n`-linear map
`ωₓ : (TₓM)ⁿ → F`, such that in every chart `φ` the map `(y, v₁, …, vₙ) ↦ ω_{φ⁻¹ y}(Tφ⁻¹ v₁, …)`
is smooth (Glöckner–Neeb, Definition 3.6.1). There are no partitions of unity, and in general no
coordinate description of forms by components; the definition only uses the local
representatives.

A tangent vector at `x` is given by its coordinates in the preferred chart `chartAt E x`, as in
`LocallyConvexManifolds.TangentBundle`; so `ωₓ` is an alternating map `Eⁿ → F`.

## Main definitions and results

* `DifferentialForm E M F n`: the space `Ωⁿ(M, F)` of smooth `F`-valued `n`-forms;
* `DifferentialForm.localRep`: the local representative of a form in a chart of the atlas; on
  chart overlaps the representatives are related by pullback along the transition map
  (`localRep_eq_pullbackLoc`);
* `DifferentialForm.d`: the exterior derivative, computed in the preferred chart at each point by
  the local formula `dω(y)(v₀, …, vₙ) = ∑ᵢ (-1)ⁱ ∂_{vᵢ} ω(y)(v₀, …, v̂ᵢ, …, vₙ)` (Glöckner–Neeb,
  (3.33)). Its local representative in *every* chart is given by the same formula
  (`localRep_d`), because the local exterior derivative commutes with changes of variables
  (`IsLocalForm.dLoc_pullbackLoc`); this is what makes `dω` a smooth form (Glöckner–Neeb,
  Proposition 3.6.7);
* `DifferentialForm.d_d`: `d ∘ d = 0` (Glöckner–Neeb, Proposition 3.6.9);
* the vector space structure of `Ωⁿ(M, F)`, with `d` linear (`dLinear`);
* `DifferentialForm.pullback`, `d_pullback`: pullbacks and the naturality of `d`
  (Glöckner–Neeb, Lemma 3.6.13), with `pullback_id` and `pullback_pullback` (Glöckner–Neeb,
  (3.27));
* `DifferentialForm.compCLM`, `d_compCLM`: composition with a continuous linear map commutes with
  `d` (Glöckner–Neeb, Exercise 3.6.4).

Glöckner–Neeb define `dω` through the Lie algebra differential on vector fields, (3.29), and
show that it is given in charts by (3.33). We take (3.33) as the definition and prove directly
that it does not depend on the chart: the terms with second derivatives of the transition maps
cancel because these are symmetric. Their Remark 3.6.10 indicates the same kind of computation
for `d ∘ d = 0`.

No completeness of `E` or `F` is assumed.
-/

open Set Function
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

/-! ### Coordinate changes of tangent vectors -/

/-- The preferred chart at `x`, as an element of the atlas: the chart in which tangent vectors
at `x` are given. -/
abbrev prefChart (x : M) : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The coordinate change of tangent vectors is the derivative of the transition map. -/
theorem tangentCoordChange_eq_dMB (i j : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : E) :
    tangentCoordChange i j (i.1.symm y) v = dMB (j.1 ∘ i.1.symm) (y, v) := by
  rw [tangentCoordChange, i.1.right_inv hy]

/-- The coordinate change of tangent vectors is linear. -/
theorem exists_linear_tangentCoordChange (i j : atlas E M) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source) :
    ∃ T : E →ₗ[ℝ] E, ∀ v, tangentCoordChange i j x v = T v := by
  have hy : i.1 x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source :=
    ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩
  exact ⟨dMBLinear (smoothMBOn_transition' i j 1) (isOpen_transition_domain i j) hy,
    fun v ↦ rfl⟩

/-! ### Differential forms -/

variable (n) in
/-- The local representative of a family `ω` of `n`-linear maps on the tangent spaces in the
chart `i`: `(y, v) ↦ ω_{i⁻¹ y}(v)`, the vectors `v` given in the chart `i` (Glöckner–Neeb,
(3.26)). -/
def formLocalRep (i : atlas E M) (ω : M → (Fin n → E) → F) (p : E × (Fin n → E)) : F :=
  ω (i.1.symm p.1) fun k ↦ tangentCoordChange i (prefChart (i.1.symm p.1)) (i.1.symm p.1) (p.2 k)

variable (E M F n) in
/-- Smooth `F`-valued differential `n`-forms on `M` (Glöckner–Neeb, Definition 3.6.1): an
alternating `n`-linear map `ωₓ` on each tangent space, with smooth local representatives. -/
structure DifferentialForm : Type (max u v) where
  /-- The form at `x`, on vectors given in the preferred chart at `x`. -/
  toFun : M → (Fin n → E) → F
  alternating' : ∀ x, ∃ A : E [⋀^Fin n]→ₗ[ℝ] F, ∀ v, toFun x v = A v
  smooth' : ∀ i : atlas E M, SmoothMBOn (formLocalRep n i toFun) (i.1.target ×ˢ univ)

namespace DifferentialForm

instance : CoeFun (DifferentialForm E M F n) fun _ ↦ M → (Fin n → E) → F := ⟨toFun⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
@[ext]
theorem ext {ω η : DifferentialForm E M F n} (h : ∀ x v, ω x v = η x v) : ω = η := by
  obtain ⟨f, _, _⟩ := ω
  obtain ⟨g, _, _⟩ := η
  congr
  funext x v
  exact h x v

/-- The local representative of `ω` in the chart `i`. -/
def localRep (ω : DifferentialForm E M F n) (i : atlas E M) : E × (Fin n → E) → F :=
  formLocalRep n i ω

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local representatives of a form are local forms. -/
theorem isLocalForm_localRep (ω : DifferentialForm E M F n) (i : atlas E M) :
    IsLocalForm n (ω.localRep i) i.1.target := by
  refine ⟨ω.smooth' i, fun y hy ↦ ?_⟩
  set x := i.1.symm y
  obtain ⟨A, hA⟩ := ω.alternating' x
  obtain ⟨T, hT⟩ := exists_linear_tangentCoordChange i (prefChart x)
    ⟨i.1.map_target hy, mem_chart_source E x⟩
  exact ⟨A.compLinearMap T, fun v ↦ by simp [localRep, formLocalRep, x, hT, hA]⟩

omit [LocallyConvexSpace ℝ E] [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- In the preferred chart at `x`, the local representative at `x` is `ωₓ` itself. -/
theorem localRep_prefChart (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    ω.localRep (prefChart x) (chartAt E x x, v) = ω x v := by
  simp only [localRep, formLocalRep, prefChart]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  congr 1
  funext k
  exact tangentCoordChange_self _ (mem_chart_source E x) _

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- On chart overlaps, the local representatives are related by pullback along the transition
map: `ωᵢ = τ*ωⱼ` for `τ = j ∘ i⁻¹`. -/
theorem localRep_eq_pullbackLoc (ω : DifferentialForm E M F n) (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v : Fin n → E) :
    ω.localRep i (y, v) = pullbackLoc (j.1 ∘ i.1.symm) (ω.localRep j) (y, v) := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source := i.1.map_target hy.1
  have hjx : j.1.symm (j.1 x) = x := j.1.left_inv hy.2
  simp only [localRep, formLocalRep, pullbackLoc, comp_apply]
  rw [hjx]
  congr 1
  funext k
  rw [← tangentCoordChange_eq_dMB i j hy.1, tangentCoordChange_comp i j (prefChart x)
    ⟨⟨hx, hy.2⟩, mem_chart_source E x⟩]

/-! ### The exterior derivative -/

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local exterior derivative at `y` only depends on the form near `y`. -/
theorem dLoc_congr {ω₁ ω₂ : E × (Fin n → E) → F} {W : Set E} (hW : IsOpen W)
    (h : EqOn ω₁ ω₂ (W ×ˢ univ)) {y : E} (hy : y ∈ W) (v : Fin (n + 1) → E) :
    dLoc ω₁ (y, v) = dLoc ω₂ (y, v) := by
  simp only [IsLocalForm.dLoc_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dMB_congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hW.mem_nhds hy)
    fun z hz ↦ h ⟨hz, mem_univ _⟩)]

/-- Change of charts for the local exterior derivative. -/
theorem localRep_d_aux (ω : DifferentialForm E M F n) (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v : Fin (n + 1) → E) :
    dLoc (ω.localRep i) (y, v) =
      dLoc (ω.localRep j) (j.1 (i.1.symm y),
        fun k ↦ tangentCoordChange i j (i.1.symm y) (v k)) := by
  set W := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hW : IsOpen W := isOpen_transition_domain i j
  have hτ : SmoothMBOn (j.1 ∘ i.1.symm) W := smoothMBOn_transition' i j
  have hWV : MapsTo (j.1 ∘ i.1.symm) W j.1.target := fun z hz ↦ j.1.map_source hz.2
  have hrep : IsLocalForm n (ω.localRep j) j.1.target := ω.isLocalForm_localRep j
  rw [dLoc_congr hW (fun p hp ↦ ω.localRep_eq_pullbackLoc i j hp.1 p.2) hy,
    hrep.dLoc_pullbackLoc hW j.1.open_target hτ hWV hy]
  simp only [pullbackLoc, comp_apply, tangentCoordChange_eq_dMB i j hy.1]

/-- The exterior derivative `dω`, computed in the preferred chart at each point by the local
formula (Glöckner–Neeb, (3.33)). -/
def dFun (ω : DifferentialForm E M F n) (x : M) (v : Fin (n + 1) → E) : F :=
  dLoc (ω.localRep (prefChart x)) (chartAt E x x, v)

/-- The local representative of `dω` in any chart is the local exterior derivative of the local
representative of `ω`: the definition of `dω` does not depend on the charts. -/
theorem formLocalRep_dFun (ω : DifferentialForm E M F n) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (v : Fin (n + 1) → E) :
    formLocalRep (n + 1) i ω.dFun (y, v) = dLoc (ω.localRep i) (y, v) := by
  set x := i.1.symm y
  have hy' : y ∈ i.1.target ∩ i.1.symm ⁻¹' (prefChart (E := E) x).1.source :=
    ⟨hy, mem_chart_source E x⟩
  rw [ω.localRep_d_aux i (prefChart x) hy' v]
  rfl

/-- The exterior derivative of a smooth form is a smooth form (Glöckner–Neeb,
Proposition 3.6.7). -/
def d (ω : DifferentialForm E M F n) : DifferentialForm E M F (n + 1) where
  toFun := ω.dFun
  alternating' x :=
    (ω.isLocalForm_localRep (prefChart x)).dLoc (prefChart x).1.open_target |>.alternating _
      ((chartAt E x).map_source (mem_chart_source E x))
  smooth' i k :=
    ContDiffMBOn.congr_of_isOpen (i.1.open_target.prod isOpen_univ)
      (fun p hp ↦ (ω.formLocalRep_dFun i hp.1 p.2).symm)
      (((ω.isLocalForm_localRep i).dLoc i.1.open_target).smooth k)

theorem d_apply (ω : DifferentialForm E M F n) (x : M) (v : Fin (n + 1) → E) :
    ω.d x v = dLoc (ω.localRep (prefChart x)) (chartAt E x x, v) :=
  rfl

/-- **Local formula for the exterior derivative** (Glöckner–Neeb, (3.33)): in every chart, the
local representative of `dω` is `(y, v) ↦ ∑ᵢ (-1)ⁱ ∂_{vᵢ} ωᵢ(y)(v₀, …, v̂ᵢ, …, vₙ)`. -/
theorem localRep_d (ω : DifferentialForm E M F n) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (v : Fin (n + 1) → E) :
    ω.d.localRep i (y, v) = dLoc (ω.localRep i) (y, v) :=
  ω.formLocalRep_dFun i hy v

/-- **`d ∘ d = 0`** (Glöckner–Neeb, Proposition 3.6.9). -/
theorem d_d (ω : DifferentialForm E M F n) (x : M) (v : Fin (n + 2) → E) : ω.d.d x v = 0 := by
  have hW := (prefChart (E := E) x).1.open_target
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  rw [d_apply, dLoc_congr hW (fun p hp ↦ ω.localRep_d (prefChart x) hp.1 p.2) hy]
  exact (ω.isLocalForm_localRep _).dLoc_dLoc hW hy v

/-! ### The vector space structure -/

section Linear

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem coe_injective : Injective (fun ω : DifferentialForm E M F n ↦ (ω : M → (Fin n → E) → F)) :=
  fun _ _ h ↦ ext fun x v ↦ congrFun (congrFun h x) v

instance : Zero (DifferentialForm E M F n) :=
  ⟨⟨0, fun _ ↦ ⟨0, fun _ ↦ rfl⟩, fun _ k ↦ contDiffMBOn_const k (0 : F) _⟩⟩

instance : Add (DifferentialForm E M F n) where
  add ω η :=
    ⟨ω + η, fun x ↦ by
      obtain ⟨A, hA⟩ := ω.alternating' x
      obtain ⟨B, hB⟩ := η.alternating' x
      exact ⟨A + B, fun v ↦ by simp [hA, hB]⟩,
    fun i k ↦ (ω.smooth' i k).add (i.1.open_target.prod isOpen_univ) (η.smooth' i k)⟩

instance : SMul ℝ (DifferentialForm E M F n) where
  smul c ω :=
    ⟨c • ω, fun x ↦ by
      obtain ⟨A, hA⟩ := ω.alternating' x
      exact ⟨c • A, fun v ↦ by simp [hA]⟩,
    fun i k ↦ ContDiffMBOn.const_smul (i.1.open_target.prod isOpen_univ) (ω.smooth' i k) c⟩

instance : Neg (DifferentialForm E M F n) where
  neg ω :=
    ⟨-ω, fun x ↦ by
      obtain ⟨A, hA⟩ := ω.alternating' x
      exact ⟨-A, fun v ↦ by simp [hA]⟩,
    fun i k ↦ by
      have h := ContDiffMBOn.const_smul (i.1.open_target.prod isOpen_univ) (ω.smooth' i k) (-1)
      simp only [neg_one_smul] at h
      exact h⟩

instance : Sub (DifferentialForm E M F n) where
  sub ω η :=
    ⟨ω - η, fun x ↦ by
      obtain ⟨A, hA⟩ := ω.alternating' x
      obtain ⟨B, hB⟩ := η.alternating' x
      exact ⟨A - B, fun v ↦ by simp [hA, hB]⟩,
    fun i k ↦ by
      have h := (ω + -η).smooth' i k
      simp only [sub_eq_add_neg]
      exact h⟩

instance : SMul ℕ (DifferentialForm E M F n) := ⟨fun m ω ↦ (m : ℝ) • ω⟩

instance : SMul ℤ (DifferentialForm E M F n) := ⟨fun m ω ↦ (m : ℝ) • ω⟩

omit [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
@[simp] theorem zero_apply (x : M) (v : Fin n → E) : (0 : DifferentialForm E M F n) x v = 0 :=
  rfl

omit [MBManifold E M] in
@[simp] theorem add_apply (ω η : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    (ω + η) x v = ω x v + η x v :=
  rfl

omit [MBManifold E M] in
@[simp] theorem smul_apply (c : ℝ) (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    (c • ω) x v = c • ω x v :=
  rfl

omit [MBManifold E M] in
@[simp] theorem neg_apply (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    (-ω) x v = -ω x v :=
  rfl

omit [MBManifold E M] in
@[simp] theorem sub_apply (ω η : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    (ω - η) x v = ω x v - η x v :=
  rfl

instance : AddCommGroup (DifferentialForm E M F n) :=
  coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun ω m ↦ by funext x v; exact Nat.cast_smul_eq_nsmul ℝ m (ω x v))
    (fun ω m ↦ by funext x v; exact Int.cast_smul_eq_zsmul ℝ m (ω x v))

/-- The coercion to functions, as an additive homomorphism. -/
def coeAddHom : DifferentialForm E M F n →+ (M → (Fin n → E) → F) where
  toFun ω := ω
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `Ωⁿ(M, F)` is a real vector space. -/
instance instModule : Module ℝ (DifferentialForm E M F n) :=
  coe_injective.module ℝ coeAddHom fun _ _ ↦ rfl

/-- `d` is additive. -/
theorem d_add (ω η : DifferentialForm E M F n) : (ω + η).d = ω.d + η.d := by
  ext x v
  exact (ω.isLocalForm_localRep _).dLoc_add (η.isLocalForm_localRep _)
    (prefChart (E := E) x).1.open_target ((chartAt E x).map_source (mem_chart_source E x)) v

/-- `d` is homogeneous. -/
theorem d_smul (c : ℝ) (ω : DifferentialForm E M F n) : (c • ω).d = c • ω.d := by
  ext x v
  exact (ω.isLocalForm_localRep _).dLoc_smul (prefChart (E := E) x).1.open_target
    ((chartAt E x).map_source (mem_chart_source E x)) c v

variable (E M F n) in
/-- The exterior derivative as a linear map `Ωⁿ(M, F) → Ωⁿ⁺¹(M, F)`. -/
def dLinear : DifferentialForm E M F n →ₗ[ℝ] DifferentialForm E M F (n + 1) where
  toFun := d
  map_add' := d_add
  map_smul' := d_smul

@[simp] theorem dLinear_apply (ω : DifferentialForm E M F n) : dLinear E M F n ω = ω.d :=
  rfl

theorem d_zero : (0 : DifferentialForm E M F n).d = 0 :=
  (dLinear E M F n).map_zero

theorem d_neg (ω : DifferentialForm E M F n) : (-ω).d = -ω.d :=
  (dLinear E M F n).map_neg ω

theorem d_sub (ω η : DifferentialForm E M F n) : (ω - η).d = ω.d - η.d :=
  (dLinear E M F n).map_sub ω η

/-- `d ∘ d = 0`, as an identity of forms. -/
theorem d_d_eq_zero (ω : DifferentialForm E M F n) : ω.d.d = 0 :=
  ext fun x v ↦ ω.d_d x v

end Linear


/-! ### Composition with continuous linear maps (Glöckner–Neeb, Exercise 3.6.4) -/

section CompCLM

variable {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- The form `α_* ω = α ∘ ω` for a continuous linear map `α : F → G` (Glöckner–Neeb,
Exercise 3.6.4). -/
def compCLM (α : F →L[ℝ] G) (ω : DifferentialForm E M F n) : DifferentialForm E M G n where
  toFun x v := α (ω x v)
  alternating' x := by
    obtain ⟨A, hA⟩ := ω.alternating' x
    exact ⟨(α : F →ₗ[ℝ] G).compAlternatingMap A, fun v ↦ by simp [hA]⟩
  smooth' i k :=
    ContDiffMBOn.comp (i.1.open_target.prod isOpen_univ) isOpen_univ (α.contDiffMBOn k univ)
      (ω.smooth' i k) (mapsTo_univ _ _)

omit [MBManifold E M] in
theorem compCLM_apply (α : F →L[ℝ] G) (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    ω.compCLM α x v = α (ω x v) :=
  rfl

/-- `α_*(dω) = d(α_* ω)` (Glöckner–Neeb, Exercise 3.6.4). -/
theorem d_compCLM (α : F →L[ℝ] G) (ω : DifferentialForm E M F n) :
    (ω.compCLM α).d = ω.d.compCLM α := by
  ext x v
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  rw [d_apply, compCLM_apply, d_apply, IsLocalForm.dLoc_apply, IsLocalForm.dLoc_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]
  congr 1
  have hs := (ω.isLocalForm_localRep (prefChart x)).smooth_slice
    (prefChart (E := E) x).1.open_target (i.removeNth v) 1
  have h := ContDiffMBOn.dMB_comp isOpen_univ (α.contDiffMBOn 1 univ) hs (mapsTo_univ _ _) hy (v i)
  rw [(α.hasDirDerivAt _ _).dMB_eq] at h
  exact h

end CompCLM

/-! ### Functions as `0`-forms, closed and exact forms -/

/-- A smooth function `f : M → F` as an `F`-valued `0`-form (Glöckner–Neeb, Definition 3.6.1:
`Ω⁰(M, F) = C^∞(M, F)`). -/
def ofFunction (f : M → F) (hf : SmoothMBM E F f) : DifferentialForm E M F 0 where
  toFun x _ := f x
  alternating' x := ⟨AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f x), fun _ ↦ rfl⟩
  smooth' i k := by
    have h := (hf k).contDiffMBOn_chart isOpen_univ i.2 (chart_mem_atlas F (f (i.1.symm 0)))
    have hD : chartDomain f univ i.1 (chartAt F (f (i.1.symm 0))) = i.1.target := by
      simp [chartDomain]
    rw [hD] at h
    have h' := h.comp_clm (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) i.1.open_target
    rw [show (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) ⁻¹' i.1.target = i.1.target ×ˢ univ by
      ext; simp] at h'
    exact h'

/-- The exterior derivative of a function is its differential (Glöckner–Neeb,
Remark 3.6.12 (a)): `(df)ₓ(v) = d(f ∘ φ⁻¹)(φ x) v` in the preferred chart `φ` at `x`. -/
theorem d_ofFunction_apply (f : M → F) (hf : SmoothMBM E F f) (x : M) (v : Fin 1 → E) :
    (ofFunction f hf).d x v = dMB (f ∘ (chartAt E x).symm) (chartAt E x x, v 0) := by
  rw [d_apply, IsLocalForm.dLoc_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rfl

/-- Closed forms: `dω = 0` (Glöckner–Neeb, Definition 3.6.11). -/
def IsClosed (ω : DifferentialForm E M F n) : Prop := ∀ x v, ω.d x v = 0

/-- Exact forms: `ω = dη` (Glöckner–Neeb, Definition 3.6.11). -/
def IsExact (ω : DifferentialForm E M F (n + 1)) : Prop := ∃ η : DifferentialForm E M F n, η.d = ω

/-- Exact forms are closed. -/
theorem IsExact.isClosed {ω : DifferentialForm E M F (n + 1)} (hω : ω.IsExact) : ω.IsClosed := by
  obtain ⟨η, rfl⟩ := hω
  exact η.d_d

/-! ### Pullbacks -/

section Pullback

variable {E₀ : Type u} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N] {φ : N → M}

/-- The pullback `(φ*ω)ₓ(v₁, …, vₙ) = ω_{φ x}(Tₓφ v₁, …, Tₓφ vₙ)` (Glöckner–Neeb,
Definition 3.6.6), with `Tₓφ` written in the preferred charts at `x` and `φ x`. -/
def pullbackFun (φ : N → M) (ω : DifferentialForm E M F n) (x : N) (v : Fin n → E₀) : F :=
  ω (φ x) fun k ↦ dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm) (chartAt E₀ x x, v k)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- In charts `i` of `N` and `j` of `M`, the local representative of `φ*ω` is the local pullback
of the local representative of `ω` along the local representative `j ∘ φ ∘ i⁻¹` of `φ`. -/
theorem formLocalRep_pullbackFun (hφ : ContMDiffMB E₀ E 1 φ) (ω : DifferentialForm E M F n)
    (i : atlas E₀ N) (j : atlas E M) {x : N} (hx : x ∈ i.1.source) (hφx : φ x ∈ j.1.source)
    (v : Fin n → E₀) :
    formLocalRep n i (pullbackFun φ ω) (i.1 x, v) =
      pullbackLoc (j.1 ∘ φ ∘ i.1.symm) (ω.localRep j) (i.1 x, v) := by
  simp only [formLocalRep, pullbackFun, pullbackLoc, localRep, comp_apply, i.1.left_inv hx,
    j.1.left_inv hφx]
  congr 1
  funext k
  simp only [tangentCoordChange]
  rw [dMB_chart_comp hφ i.2 (chart_mem_atlas E₀ x) (chart_mem_atlas E (φ x)) hx
      (mem_chart_source E₀ x) (mem_chart_source E (φ x)),
    dMB_comp_chart hφ i.2 j.2 (chart_mem_atlas E (φ x)) hx hφx (mem_chart_source E (φ x))]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem formLocalRep_pullbackFun' (hφ : ContMDiffMB E₀ E 1 φ) (ω : DifferentialForm E M F n)
    (i : atlas E₀ N) (j : atlas E M) {y : E₀} (hy : y ∈ chartDomain φ univ i.1 j.1)
    (v : Fin n → E₀) :
    formLocalRep n i (pullbackFun φ ω) (y, v) =
      pullbackLoc (j.1 ∘ φ ∘ i.1.symm) (ω.localRep j) (y, v) := by
  have h := formLocalRep_pullbackFun hφ ω i j (i.1.map_target hy.1) hy.2.2 v
  rwa [i.1.right_inv hy.1] at h

/-- The pullback of a smooth form along a smooth map is a smooth form. -/
def pullback (hφ : SmoothMBM E₀ E φ) (ω : DifferentialForm E M F n) :
    DifferentialForm E₀ N F n where
  toFun := pullbackFun φ ω
  alternating' x := by
    obtain ⟨A, hA⟩ := ω.alternating' (φ x)
    set c := chartAt E₀ x
    set c' := chartAt E (φ x)
    have hD : IsOpen (chartDomain φ univ c c') :=
      isOpen_chartDomain isOpen_univ (hφ 1).1 c c'
    have hcx : c x ∈ chartDomain φ univ c c' :=
      ⟨c.map_source (mem_chart_source E₀ x), mem_univ _, by
        simp [c, c', (chartAt E₀ x).left_inv (mem_chart_source E₀ x)]⟩
    exact ⟨A.compLinearMap (dMBLinear ((hφ 1).contDiffMBOn_chart isOpen_univ
      (chart_mem_atlas E₀ x) (chart_mem_atlas E (φ x))) hD hcx), fun v ↦ hA _⟩
  smooth' i k := by
    have hT : IsOpen (i.1.target ×ˢ (univ : Set (Fin n → E₀))) :=
      i.1.open_target.prod isOpen_univ
    refine ContDiffMBOn.of_local hT fun p hp ↦ ?_
    set j : atlas E M := prefChart (φ (i.1.symm p.1))
    set W := chartDomain φ univ i.1 j.1
    have hW : IsOpen W := isOpen_chartDomain isOpen_univ (hφ 1).1 i.1 j.1
    have hτ : SmoothMBOn (j.1 ∘ φ ∘ i.1.symm) W := fun k ↦
      (hφ k).contDiffMBOn_chart isOpen_univ i.2 j.2
    have hWj : MapsTo (j.1 ∘ φ ∘ i.1.symm) W j.1.target := fun z hz ↦ j.1.map_source hz.2.2
    have hpW : p.1 ∈ W := ⟨hp.1, mem_univ _, mem_chart_source E _⟩
    refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨hpW, mem_univ _⟩, ?_⟩
    have hsub : (i.1.target ×ˢ univ) ∩ (W ×ˢ univ) = W ×ˢ (univ : Set (Fin n → E₀)) := by
      rw [Set.prod_inter_prod, inter_univ, inter_eq_right.mpr (fun z (hz : z ∈ W) ↦ hz.1)]
    rw [hsub]
    exact ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ)
      (fun q hq ↦ (formLocalRep_pullbackFun' (hφ 1) ω i j hq.1 q.2).symm)
      (smoothMBOn_pullbackLoc (ω.isLocalForm_localRep j) hW j.1.open_target hτ hWj k)

theorem pullback_apply (hφ : SmoothMBM E₀ E φ) (ω : DifferentialForm E M F n) (x : N)
    (v : Fin n → E₀) :
    ω.pullback hφ x v =
      ω (φ x) fun k ↦ dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm) (chartAt E₀ x x, v k) :=
  rfl

/-- **Naturality of the exterior derivative** (Glöckner–Neeb, Lemma 3.6.13):
`d(φ*ω) = φ*(dω)` for smooth maps `φ`. -/
theorem d_pullback (hφ : SmoothMBM E₀ E φ) (ω : DifferentialForm E M F n) :
    (ω.pullback hφ).d = ω.d.pullback hφ := by
  ext x v
  set c : atlas E₀ N := prefChart x
  set j : atlas E M := prefChart (φ x)
  set W := chartDomain φ univ c.1 j.1
  have hW : IsOpen W := isOpen_chartDomain isOpen_univ (hφ 1).1 c.1 j.1
  have hτ : SmoothMBOn (j.1 ∘ φ ∘ c.1.symm) W := fun k ↦
    (hφ k).contDiffMBOn_chart isOpen_univ c.2 j.2
  have hWj : MapsTo (j.1 ∘ φ ∘ c.1.symm) W j.1.target := fun z hz ↦ j.1.map_source hz.2.2
  have hx : x ∈ c.1.source := mem_chart_source E₀ x
  have hcx : c.1 x ∈ W := ⟨c.1.map_source hx, mem_univ _, by
    simp [j, c, (chartAt E₀ x).left_inv hx]⟩
  rw [d_apply, dLoc_congr (ω₁ := (ω.pullback hφ).localRep c)
      (ω₂ := pullbackLoc (j.1 ∘ φ ∘ c.1.symm) (ω.localRep j)) hW
      (fun q hq ↦ formLocalRep_pullbackFun' (hφ 1) ω c j hq.1 q.2) hcx,
    (ω.isLocalForm_localRep j).dLoc_pullbackLoc hW j.1.open_target hτ hWj hcx]
  simp only [pullbackLoc, comp_apply, c.1.left_inv hx]
  rfl

theorem pullback_add (hφ : SmoothMBM E₀ E φ) (ω η : DifferentialForm E M F n) :
    (ω + η).pullback hφ = ω.pullback hφ + η.pullback hφ :=
  rfl

theorem pullback_smul (hφ : SmoothMBM E₀ E φ) (c : ℝ) (ω : DifferentialForm E M F n) :
    (c • ω).pullback hφ = c • ω.pullback hφ :=
  rfl

variable (n) in
/-- The pullback as a linear map `Ωⁿ(M, F) → Ωⁿ(N, F)`. -/
def pullbackLinear (hφ : SmoothMBM E₀ E φ) :
    DifferentialForm E M F n →ₗ[ℝ] DifferentialForm E₀ N F n where
  toFun ω := ω.pullback hφ
  map_add' ω η := pullback_add hφ ω η
  map_smul' c ω := pullback_smul hφ c ω

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- In the preferred charts, the vectors in `pullbackFun` are the images under the tangent
map. -/
theorem pullbackFun_eq_tangentMap (φ : N → M) (ω : DifferentialForm E M F n) (x : N)
    (v : Fin n → E₀) :
    pullbackFun φ ω x v = ω (φ x) fun k ↦ ((tangentMap E₀ E φ ⟨x, v k⟩).2 : E) :=
  rfl

end Pullback

section Functoriality

/-- `id* ω = ω` (Glöckner–Neeb, (3.27)). -/
theorem pullback_id (ω : DifferentialForm E M F n) :
    ω.pullback (fun k ↦ smoothMBMOn_id (E := E) (M := M) isOpen_univ k) = ω := by
  ext x v
  change pullbackFun id ω x v = ω x v
  rw [pullbackFun_eq_tangentMap]
  congr 1
  funext k
  exact congrArg (fun p : TangentBundle E M ↦ (p.2 : E)) (tangentMap_id ⟨x, v k⟩)

variable {E₀ E₁ : Type u}
  [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀] [IsTopologicalAddGroup E₀]
  [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E₁ P] [MBManifold E₁ P]

/-- `ψ* (φ* ω) = (φ ∘ ψ)* ω` (Glöckner–Neeb, (3.27)). -/
theorem pullback_pullback {φ : N → M} {ψ : P → N} (hφ : SmoothMBM E₀ E φ)
    (hψ : SmoothMBM E₁ E₀ ψ) (ω : DifferentialForm E M F n) :
    (ω.pullback hφ).pullback hψ = ω.pullback (hφ.comp hψ) := by
  ext x v
  change pullbackFun ψ (ω.pullback hφ) x v = pullbackFun (φ ∘ ψ) ω x v
  rw [pullbackFun_eq_tangentMap, pullbackFun_eq_tangentMap]
  exact congrArg (ω.toFun (φ (ψ x))) (funext fun k ↦
    congrArg (fun p : TangentBundle E M ↦ (p.2 : E)) (tangentMap_comp (hφ 1) (hψ 1) ⟨x, v k⟩))

end Functoriality

end DifferentialForm

end LocallyConvex.Manifolds
