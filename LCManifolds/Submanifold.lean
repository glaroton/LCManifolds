/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.ContMDiff

/-!
# Embedded submanifolds

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 2
(subvariedad embebida); H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3.

A subset `N` of a manifold `M` modeled on `E` is an embedded submanifold modeled on a closed
subspace `S ⊆ E` if every point of `N` lies in a chart `φ` of the atlas with
`φ(U ∩ N) = φ(U) ∩ S`. No complement of `S` is required, so this notion is meaningful for
locally convex (and Banach) models where closed subspaces need not be complemented. The usual
criteria (regular values, split immersions) need inverse or implicit function theorems, and are
not available for general locally convex models.

The calculus fact behind the construction is `ContDiffMBOn.codRestrict`: a `C^k` map with values
in a closed subspace `T` is `C^k` as a map into `T`, since difference quotients, and hence
derivatives, stay in `T`.
-/

open Set Filter
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u v

section Calculus

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- A `C^k` map with values in a closed subspace `T` is `C^k` as a map into `T`. -/
theorem ContDiffMBOn.codRestrict {T : Submodule ℝ F} (hT : IsClosed (T : Set F)) :
    ∀ {k : ℕ} {D : Type u} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
      [IsTopologicalAddGroup D] [ContinuousSMul ℝ D] [LocallyConvexSpace ℝ D] [T2Space D]
      {h : D → F} {h' : D → T} {V : Set D}, IsOpen V → ContDiffMBOn k h V →
      (∀ x ∈ V, (h' x : F) = h x) → ContDiffMBOn k h' V := by
  intro k
  induction k with
  | zero =>
    intro D _ _ _ _ _ _ _ h h' V hV hh he
    exact (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr
      ((hh : ContinuousOn h V).congr fun x hx ↦ he x hx)
  | succ k ih =>
    intro D _ _ _ _ _ _ _ h h' V hV hh he
    -- the derivative of `h` stays in `T`
    have hmem : ∀ x ∈ V, ∀ w, dMB h (x, w) ∈ T := by
      intro x hx w
      refine hT.mem_of_tendsto (hh.hasDirDerivAt hx w) ?_
      have hl : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝[≠] 0) (𝓝 x) := by
        have : Continuous fun t : ℝ ↦ x + t • w := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      filter_upwards [hl (hV.mem_nhds hx)] with t ht
      rw [← he _ ht, ← he x hx]
      exact T.smul_mem _ (T.sub_mem (h' _).2 (h' x).2)
    -- the derivative of `h'`
    have hd : ∀ x (hx : x ∈ V) w, HasDirDerivAt h' x w ⟨dMB h (x, w), hmem x hx w⟩ := by
      intro x hx w
      have hl : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝[≠] 0) (𝓝 x) := by
        have : Continuous fun t : ℝ ↦ x + t • w := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      refine (Topology.IsInducing.subtypeVal.tendsto_nhds_iff).mpr ?_
      refine (hh.hasDirDerivAt hx w).congr' ?_
      filter_upwards [hl (hV.mem_nhds hx)] with t ht
      simp only [Function.comp_apply, Submodule.coe_smul, Submodule.coe_sub, he _ ht, he x hx]
    have hdeq : ∀ p ∈ V ×ˢ (univ : Set D), ((dMB h' p : T) : F) = dMB h p := by
      rintro ⟨x, w⟩ ⟨hx, -⟩
      rw [(hd x hx w).dMB_eq]
    refine ⟨(Topology.IsInducing.subtypeVal.continuousOn_iff).mpr
        (hh.continuousOn.congr fun x hx ↦ he x hx),
      fun x hx w ↦ ?_, ih (hV.prod isOpen_univ) hh.2.2 hdeq⟩
    rw [(hd x hx w).dMB_eq]
    exact hd x hx w

end Calculus

section Submanifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  (N : Set M) (S : Submodule ℝ E)

/-- `φ` is a slice chart for `N` with model `S`: a chart of the atlas with
`φ(U ∩ N) = φ(U) ∩ S`. -/
def IsSliceChart (φ : OpenPartialHomeomorph M E) : Prop :=
  φ ∈ atlas E M ∧ ∀ q ∈ φ.source, (q ∈ N ↔ φ q ∈ S)

/-- `N` is an embedded submanifold of `M` modeled on the closed subspace `S` of `E`: every point
of `N` lies in a slice chart. -/
structure IsEmbeddedSubmanifold : Prop where
  isClosed : IsClosed (S : Set E)
  exists_sliceChart : ∀ p ∈ N, ∃ φ, IsSliceChart N S φ ∧ p ∈ φ.source

variable {N S}

open scoped Classical in
/-- The chart of `N` induced by a slice chart `φ`: the restriction `U ∩ N → φ(U) ∩ S`. The
point `p₀` is only used as a junk value outside the target. -/
def sliceChart {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (p₀ : N) :
    OpenPartialHomeomorph N S where
  toFun q := if h : φ q ∈ S then ⟨φ q, h⟩ else 0
  invFun y := if h : φ.symm y ∈ N then ⟨φ.symm y, h⟩ else p₀
  source := Subtype.val ⁻¹' φ.source
  target := Subtype.val ⁻¹' φ.target
  map_source' q hq := by
    rw [dite_eq_left ((hφ.2 q hq).mp q.2)]
    exact φ.map_source hq
  map_target' y hy := by
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    rw [dite_eq_left hN]
    exact φ.map_target hy
  left_inv' q hq := by
    have hS : φ q ∈ S := (hφ.2 q hq).mp q.2
    have hN : φ.symm (φ q) ∈ N := by rw [φ.left_inv hq]; exact q.2
    simp only [dite_eq_left hS]
    rw [dite_eq_left hN]
    exact Subtype.ext (φ.left_inv hq)
  right_inv' y hy := by
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    have hS : φ (φ.symm y) ∈ S := by rw [φ.right_inv hy]; exact y.2
    simp only [dite_eq_left hN]
    rw [dite_eq_left hS]
    exact Subtype.ext (φ.right_inv hy)
  open_source := φ.open_source.preimage continuous_subtype_val
  open_target := φ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr ?_
    refine (φ.continuousOn.comp continuous_subtype_val.continuousOn fun q hq ↦ hq).congr ?_
    intro q hq
    simp only [Function.comp_apply, dite_eq_left ((hφ.2 q hq).mp q.2)]
  continuousOn_invFun := by
    refine (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr ?_
    refine (φ.continuousOn_symm.comp continuous_subtype_val.continuousOn fun y hy ↦ hy).congr ?_
    intro y hy
    have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
    simp only [Function.comp_apply, dite_eq_left hN]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
open scoped Classical in
theorem sliceChart_apply_coe {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (p₀ : N)
    {q : N} (hq : (q : M) ∈ φ.source) : ((sliceChart hφ p₀ q : S) : E) = φ q := by
  change ((if h : φ q ∈ S then (⟨φ q, h⟩ : S) else 0 : S) : E) = φ q
  rw [dite_eq_left ((hφ.2 q hq).mp q.2)]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
open scoped Classical in
theorem sliceChart_symm_apply_coe {φ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ)
    (p₀ : N) {y : S} (hy : (y : E) ∈ φ.target) :
    (((sliceChart hφ p₀).symm y : N) : M) = φ.symm y := by
  have hN : φ.symm y ∈ N := (hφ.2 _ (φ.map_target hy)).mpr (by rw [φ.right_inv hy]; exact y.2)
  change ((if h : φ.symm y ∈ N then (⟨φ.symm y, h⟩ : N) else p₀ : N) : M) = φ.symm y
  rw [dite_eq_left hN]

/-- The transition maps between induced charts are smooth: they are restrictions to `S` of
transition maps of `M`, with values in `S`. -/
theorem smoothMBOn_sliceChart_transition (hS : IsClosed (S : Set E))
    {φ ψ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (hψ : IsSliceChart N S ψ)
    (p₀ p₁ : N) :
    SmoothMBOn ⇑((sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁)
      ((sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁).source := by
  set e := sliceChart hφ p₀
  set e' := sliceChart hψ p₁
  have hV : IsOpen (e.symm ≫ₕ e').source := (e.symm ≫ₕ e').open_source
  have hsub : ∀ y ∈ (e.symm ≫ₕ e').source,
      (y : E) ∈ φ.target ∩ φ.symm ⁻¹' ψ.source ∧ ((e.symm y : N) : M) = φ.symm y := by
    rintro y ⟨hy, hy'⟩
    have hy₁ : (y : E) ∈ φ.target := hy
    have hc := sliceChart_symm_apply_coe hφ p₀ hy₁
    refine ⟨⟨hy₁, ?_⟩, hc⟩
    have : ((e.symm y : N) : M) ∈ ψ.source := hy'
    rwa [hc] at this
  intro k
  have hh : ContDiffMBOn k ((ψ ∘ φ.symm) ∘ S.subtypeL) (e.symm ≫ₕ e').source :=
    (smoothMBOn_transition hφ.1 hψ.1 k).comp hV (φ.isOpen_inter_preimage_symm ψ.open_source)
      (S.subtypeL.contDiffMBOn k _) fun y hy ↦ (hsub y hy).1
  refine ContDiffMBOn.codRestrict hS hV hh fun y hy ↦ ?_
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    sliceChart_apply_coe hψ p₁ (by rw [(hsub y hy).2]; exact (hsub y hy).1.2), (hsub y hy).2]
  rfl

theorem sliceChart_transition_mem (hS : IsClosed (S : Set E))
    {φ ψ : OpenPartialHomeomorph M E} (hφ : IsSliceChart N S φ) (hψ : IsSliceChart N S ψ)
    (p₀ p₁ : N) :
    (sliceChart hφ p₀).symm ≫ₕ sliceChart hψ p₁ ∈ mbGroupoid S := by
  refine ⟨smoothMBOn_sliceChart_transition hS hφ hψ p₀ p₁, ?_⟩
  have h := smoothMBOn_sliceChart_transition hS hψ hφ p₁ p₀
  rw [OpenPartialHomeomorph.trans_source] at h
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h

/-- The charted space structure of an embedded submanifold, by the induced charts. -/
@[instance_reducible]
def IsEmbeddedSubmanifold.chartedSpace (h : IsEmbeddedSubmanifold N S) : ChartedSpace S N where
  atlas := {e | ∃ (φ : OpenPartialHomeomorph M E) (hφ : IsSliceChart N S φ) (p₀ : N),
    e = sliceChart hφ p₀}
  chartAt p := sliceChart (h.exists_sliceChart p p.2).choose_spec.1 p
  mem_chart_source p := (h.exists_sliceChart p p.2).choose_spec.2
  chart_mem_atlas p := ⟨_, _, p, rfl⟩

/-- **An embedded submanifold is a manifold** modeled on `S`. -/
theorem IsEmbeddedSubmanifold.mbManifold (h : IsEmbeddedSubmanifold N S) :
    letI := h.chartedSpace; MBManifold S N := by
  let := h.chartedSpace
  exact ⟨by
    rintro _ _ ⟨φ, hφ, p₀, rfl⟩ ⟨ψ, hψ, p₁, rfl⟩
    exact sliceChart_transition_mem h.isClosed hφ hψ p₀ p₁⟩

/-- The inclusion of an embedded submanifold is smooth. -/
theorem IsEmbeddedSubmanifold.smoothMBM_val (h : IsEmbeddedSubmanifold N S) :
    letI := h.chartedSpace; SmoothMBM S E (Subtype.val : N → M) := by
  let := h.chartedSpace
  intro k
  refine ⟨continuous_subtype_val.continuousOn, fun p _ ↦ ?_⟩
  obtain ⟨hφ, hp⟩ := (h.exists_sliceChart p p.2).choose_spec
  set φ := (h.exists_sliceChart p p.2).choose
  set c := chartAt E (p : M)
  change ContDiffMBOn k (c ∘ Subtype.val ∘ (sliceChart hφ p).symm)
    (chartDomain Subtype.val univ (sliceChart hφ p) c)
  have hD : IsOpen (chartDomain Subtype.val univ (sliceChart hφ p) c) :=
    isOpen_chartDomain isOpen_univ continuous_subtype_val.continuousOn _ _
  have hsub : ∀ y ∈ chartDomain Subtype.val univ (sliceChart hφ p) c,
      (y : E) ∈ φ.target ∩ φ.symm ⁻¹' c.source ∧
        (((sliceChart hφ p).symm y : N) : M) = φ.symm y := by
    rintro y ⟨hy, -, hyc⟩
    have hc := sliceChart_symm_apply_coe hφ p (y := y) hy
    refine ⟨⟨hy, ?_⟩, hc⟩
    have : (((sliceChart hφ p).symm y : N) : M) ∈ c.source := hyc
    rwa [hc] at this
  have hh : ContDiffMBOn k ((c ∘ φ.symm) ∘ S.subtypeL)
      (chartDomain Subtype.val univ (sliceChart hφ p) c) :=
    (smoothMBOn_transition hφ.1 (chart_mem_atlas E (p : M)) k).comp hD
      (φ.isOpen_inter_preimage_symm c.open_source) (S.subtypeL.contDiffMBOn k _)
      fun y hy ↦ (hsub y hy).1
  refine ContDiffMBOn.congr_of_isOpen hD (fun y hy ↦ ?_) hh
  simp only [Function.comp_apply, (hsub y hy).2]
  rfl

end Submanifold

end LCManifolds
