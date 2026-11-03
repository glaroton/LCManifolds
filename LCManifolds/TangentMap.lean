/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.TangentBundle

/-!
# The tangent map

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, §I.3; H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3.

For a `C^1` map `f : M → N` between manifolds modeled on `E` and `F`, the tangent map
`Tf : TM → TN` sends a tangent vector `v` at `x`, written in the preferred chart `c` at `x`, to
the vector `d(c' ∘ f ∘ c⁻¹)(c x) v` at `f x`, written in the preferred chart `c'` at `f x`. We
show:

* `dMB_chart_comp`, `dMB_comp_chart`: derivatives of local representatives transform under
  changes of charts by the derivatives of the transition maps (the chain rule);
* `tangentMap_chart`: in the charts of the tangent bundles, `Tf` reads
  `(y, w) ↦ (h y, dh(y) w)`, where `h` is the local representative of `f`;
* `ContMDiffMB.tangentMap`: if `f` is `C^(k+1)`, then `Tf` is `C^k`;
* `tangentMap_comp`, `tangentMap_id`: functoriality, `T(g ∘ f) = Tg ∘ Tf` and `T id = id`.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

section Calculus

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The chain rule for a map that agrees with a composition near the point. -/
theorem dMB_eq_comp_of_eventuallyEq {g₀ : E → F} {g₁ : F → G} {h : E → G} {U : Set E}
    {V : Set F} (hV : IsOpen V) (hg₁ : ContDiffMBOn 1 g₁ V) (hg₀ : ContDiffMBOn 1 g₀ U)
    (hUV : MapsTo g₀ U V) {y : E} (hy : y ∈ U) (hh : h =ᶠ[𝓝 y] g₁ ∘ g₀) (v : E) :
    dMB h (y, v) = dMB g₁ (g₀ y, dMB g₀ (y, v)) := by
  rw [dMB_congr_of_eventuallyEq hh]
  exact ContDiffMBOn.dMB_comp hV hg₁ hg₀ hUV hy v

end Calculus

section Charts

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]
  {f : M → N}

/-- Changing the chart of the source:
`d(e' f e₂⁻¹)(e₂ x) ∘ d(e₂ e₁⁻¹)(e₁ x) = d(e' f e₁⁻¹)(e₁ x)`. -/
theorem dMB_chart_comp (hf : ContMDiffMB E F 1 f) {e₁ e₂ : OpenPartialHomeomorph M E}
    (he₁ : e₁ ∈ atlas E M) (he₂ : e₂ ∈ atlas E M) {e' : OpenPartialHomeomorph N F}
    (he' : e' ∈ atlas F N) {x : M} (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source)
    (hfx : f x ∈ e'.source) (v : E) :
    dMB (e' ∘ f ∘ e₂.symm) (e₂ x, dMB (e₂ ∘ e₁.symm) (e₁ x, v)) =
      dMB (e' ∘ f ∘ e₁.symm) (e₁ x, v) := by
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  set U := e₁.target ∩ e₁.symm ⁻¹' (e₂.source ∩ f ⁻¹' e'.source)
  have hU : IsOpen U :=
    e₁.isOpen_inter_preimage_symm (e₂.open_source.inter (e'.open_source.preimage hfc))
  have hxU : e₁ x ∈ U := ⟨e₁.map_source hx₁, by simp [e₁.left_inv hx₁, hx₂, hfx]⟩
  have hg₀ : ContDiffMBOn 1 (e₂ ∘ e₁.symm) U :=
    (smoothMBOn_transition he₁ he₂ 1).mono fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hg₁ : ContDiffMBOn 1 (e' ∘ f ∘ e₂.symm) (chartDomain f univ e₂ e') :=
    hf.contDiffMBOn_chart isOpen_univ he₂ he'
  have hmaps : MapsTo (e₂ ∘ e₁.symm) U (chartDomain f univ e₂ e') := by
    rintro z ⟨-, hz₂, hzf⟩
    exact ⟨e₂.map_source hz₂, by simp [e₂.left_inv hz₂, hzf]⟩
  have hh : e' ∘ f ∘ e₁.symm =ᶠ[𝓝 (e₁ x)] (e' ∘ f ∘ e₂.symm) ∘ (e₂ ∘ e₁.symm) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun z hz ↦ by
      simp [e₂.left_inv hz.2.1]
  rw [dMB_eq_comp_of_eventuallyEq (isOpen_chartDomain isOpen_univ hf.1 e₂ e') hg₁ hg₀ hmaps
    hxU hh v]
  simp [e₁.left_inv hx₁]

/-- Changing the chart of the target:
`d(e₂' e₁'⁻¹)(e₁' f x) ∘ d(e₁' f e⁻¹)(e x) = d(e₂' f e⁻¹)(e x)`. -/
theorem dMB_comp_chart (hf : ContMDiffMB E F 1 f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ atlas E M) {e₁' e₂' : OpenPartialHomeomorph N F} (he₁' : e₁' ∈ atlas F N)
    (he₂' : e₂' ∈ atlas F N) {x : M} (hx : x ∈ e.source) (hfx₁ : f x ∈ e₁'.source)
    (hfx₂ : f x ∈ e₂'.source) (v : E) :
    dMB (e₂' ∘ e₁'.symm) (e₁' (f x), dMB (e₁' ∘ f ∘ e.symm) (e x, v)) =
      dMB (e₂' ∘ f ∘ e.symm) (e x, v) := by
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  set U := e.target ∩ e.symm ⁻¹' (f ⁻¹' (e₁'.source ∩ e₂'.source))
  have hU : IsOpen U :=
    e.isOpen_inter_preimage_symm ((e₁'.open_source.inter e₂'.open_source).preimage hfc)
  have hxU : e x ∈ U := ⟨e.map_source hx, by simp [e.left_inv hx, hfx₁, hfx₂]⟩
  have hg₀ : ContDiffMBOn 1 (e₁' ∘ f ∘ e.symm) U :=
    (hf.contDiffMBOn_chart isOpen_univ he he₁').mono fun z hz ↦ ⟨hz.1, mem_univ _, hz.2.1⟩
  have hg₁ : ContDiffMBOn 1 (e₂' ∘ e₁'.symm) (e₁'.target ∩ e₁'.symm ⁻¹' e₂'.source) :=
    smoothMBOn_transition he₁' he₂' 1
  have hmaps : MapsTo (e₁' ∘ f ∘ e.symm) U (e₁'.target ∩ e₁'.symm ⁻¹' e₂'.source) := by
    rintro z ⟨-, hz₁, hz₂⟩
    exact ⟨e₁'.map_source hz₁, by simp [e₁'.left_inv hz₁, hz₂]⟩
  have hh : e₂' ∘ f ∘ e.symm =ᶠ[𝓝 (e x)] (e₂' ∘ e₁'.symm) ∘ (e₁' ∘ f ∘ e.symm) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun z hz ↦ by
      simp [e₁'.left_inv hz.2.1]
  rw [dMB_eq_comp_of_eventuallyEq (e₁'.isOpen_inter_preimage_symm e₂'.open_source) hg₁ hg₀
    hmaps hxU hh v]
  simp [e.left_inv hx]

end Charts

section TangentMap

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

variable (E F) in
/-- The tangent map `Tf : TM → TN`: a vector `v` at `x`, written in the preferred chart at `x`,
goes to `d(c' ∘ f ∘ c⁻¹)(c x) v` at `f x`, written in the preferred chart `c'` at `f x`. -/
def tangentMap (f : M → N) (p : TangentBundle E M) : TangentBundle F N :=
  ⟨f p.proj, (dMB (chartAt F (f p.proj) ∘ f ∘ (chartAt E p.proj).symm)
    (chartAt E p.proj p.proj, (p.2 : E)) : F)⟩

theorem tangentMap_proj (f : M → N) (p : TangentBundle E M) :
    (tangentMap E F f p).proj = f p.proj :=
  rfl

/-- In the charts of the tangent bundles over charts `i` of `M` and `j` of `N`, the tangent map
reads `(y, w) ↦ (h y, dh(y) w)`, where `h = j ∘ f ∘ i⁻¹` is the local representative of `f`. -/
theorem tangentMap_chart {f : M → N} (hf : ContMDiffMB E F 1 f) (i : atlas E M)
    (j : atlas F N) {y : E} (hy : y ∈ i.1.target) (hfy : f (i.1.symm y) ∈ j.1.source) (w : E) :
    tangentChart j j.1 (tangentMap E F f ((tangentChart i i.1).symm (y, w))) =
      (j.1 (f (i.1.symm y)), dMB (j.1 ∘ f ∘ i.1.symm) (y, w)) := by
  set z := i.1.symm y
  have hz : z ∈ i.1.source := i.1.map_target hy
  have hiz : i.1 z = y := i.1.right_inv hy
  rw [tangentChart_apply]
  refine Prod.ext rfl ?_
  change tangentCoordChange ⟨chartAt F (f z), chart_mem_atlas F _⟩ j (f z)
      (dMB (chartAt F (f z) ∘ f ∘ (chartAt E z).symm) (chartAt E z z,
        tangentCoordChange i ⟨chartAt E z, chart_mem_atlas E _⟩ z w)) = _
  simp only [tangentCoordChange]
  rw [← hiz, dMB_chart_comp hf i.2 (chart_mem_atlas E z) (chart_mem_atlas F (f z)) hz
      (mem_chart_source E z) (mem_chart_source F (f z)),
    dMB_comp_chart hf i.2 (chart_mem_atlas F (f z)) j.2 hz (mem_chart_source F (f z)) hfy]

theorem chartAt_tangentBundle (p : TangentBundle E M) :
    chartAt (E × E) p = tangentChart ⟨chartAt E p.proj, chart_mem_atlas E _⟩ (chartAt E p.proj) :=
  rfl

/-- If `f` is `C^(k+1)`, the tangent map `Tf` is `C^k`. -/
theorem ContMDiffMB.tangentMap {k : ℕ} {f : M → N} (hf : ContMDiffMB E F (k + 1) f) :
    ContMDiffMB (E × E) (F × F) k (tangentMap E F f) := by
  have hf1 : ContMDiffMB E F 1 f := by
    refine ⟨hf.1, fun x hx ↦ (hf.2 x hx).of_le (by omega)⟩
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  -- the data attached to a point `x` of `M`
  have key : ∀ x : M,
      let c := chartAt E x
      let c' := chartAt F (f x)
      let D := chartDomain f univ c c'
      let R : E × E → F × F := fun q ↦ (c' (f (c.symm q.1)), dMB (c' ∘ f ∘ c.symm) q)
      IsOpen D ∧ (∀ k', k' ≤ k → ContDiffMBOn k' R (D ×ˢ univ)) := by
    intro x c c' D R
    have hD : IsOpen D := isOpen_chartDomain isOpen_univ hf.1 c c'
    have hh : ContDiffMBOn (k + 1) (c' ∘ f ∘ c.symm) D := hf.2 x (mem_univ x)
    refine ⟨hD, fun k' hk' ↦ ?_⟩
    have hDU : IsOpen (D ×ˢ (univ : Set E)) := hD.prod isOpen_univ
    have h1 :
        ContDiffMBOn k' ((c' ∘ f ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
      (hh.of_le (by omega)).comp hDU hD ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k' _)
        fun q hq ↦ hq.1
    have h2 : ContDiffMBOn k' (dMB (c' ∘ f ∘ c.symm)) (D ×ˢ univ) :=
      ((hh.of_le (by omega : k' + 1 ≤ k + 1)).2.2 : ContDiffMBOn k' _ _)
    exact h1.prodMk hDU h2
  -- the local expression in the charts of the tangent bundles
  have hrep : ∀ x : M, ∀ q ∈ chartDomain f univ (chartAt E x) (chartAt F (f x)) ×ˢ univ,
      tangentChart ⟨chartAt F (f x), chart_mem_atlas F _⟩ (chartAt F (f x))
        (LCManifolds.tangentMap E F f
          ((tangentChart ⟨chartAt E x, chart_mem_atlas E _⟩ (chartAt E x)).symm q)) =
        (chartAt F (f x) (f ((chartAt E x).symm q.1)),
          dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) q) := by
    rintro x ⟨y, w⟩ ⟨⟨hy, -, hfy⟩, -⟩
    exact tangentMap_chart hf1 ⟨_, chart_mem_atlas E x⟩ ⟨_, chart_mem_atlas F (f x)⟩ hy hfy w
  -- continuity
  have hcont : Continuous (LCManifolds.tangentMap E F f) := by
    refine continuous_iff_continuousAt.mpr fun p ↦ ?_
    set x := p.proj
    set ψ := tangentChart ⟨chartAt E x, chart_mem_atlas E _⟩ (chartAt E x)
    set ψ' := tangentChart ⟨chartAt F (f x), chart_mem_atlas F _⟩ (chartAt F (f x))
    obtain ⟨hD, hR⟩ := key x
    set W := ψ.source ∩ Bundle.TotalSpace.proj ⁻¹' (f ⁻¹' (chartAt F (f x)).source)
    have hW : IsOpen W := ψ.open_source.inter
      (((chartAt F (f x)).open_source.preimage hfc).preimage
        (tangentBundleCore E M).continuous_proj)
    have hpW : p ∈ W := ⟨(mem_tangentChart_source _ _ _).mpr
      ⟨mem_chart_source E x, mem_chart_source E x⟩, mem_chart_source F (f x)⟩
    set R : E × E → F × F := fun q ↦ (chartAt F (f x) (f ((chartAt E x).symm q.1)),
      dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) q)
    set D := chartDomain f univ (chartAt E x) (chartAt F (f x))
    have hψW : MapsTo ψ W (D ×ˢ univ) := by
      rintro p' ⟨hp', hp'f⟩
      rw [mem_tangentChart_source] at hp'
      refine ⟨⟨(chartAt E x).map_source hp'.2, mem_univ _, ?_⟩, mem_univ _⟩
      rw [tangentChart_apply]
      simp only [mem_preimage, (chartAt E x).left_inv hp'.2]
      exact hp'f
    have hRT : MapsTo R (D ×ˢ univ) ψ'.target := by
      rintro q ⟨⟨-, -, hq⟩, -⟩
      rw [mem_tangentChart_target]
      refine ⟨(chartAt F (f x)).map_source hq, ?_⟩
      change (chartAt F (f x)).symm (chartAt F (f x) (f ((chartAt E x).symm q.1))) ∈ _
      rw [(chartAt F (f x)).left_inv hq]
      exact hq
    have hcomp : ContinuousOn (ψ'.symm ∘ R ∘ ψ) W :=
      ψ'.continuousOn_symm.comp (((hR 0 (Nat.zero_le _)).continuousOn).comp
        (ψ.continuousOn.mono inter_subset_left) hψW) (hRT.comp hψW)
    have heq : EqOn (LCManifolds.tangentMap E F f) (ψ'.symm ∘ R ∘ ψ) W := by
      intro p' hp'
      have hsrc : LCManifolds.tangentMap E F f p' ∈ ψ'.source :=
        (mem_tangentChart_source _ _ _).mpr ⟨hp'.2, hp'.2⟩
      have hrep' := hrep x (ψ p') (hψW hp')
      rw [ψ.left_inv hp'.1] at hrep'
      simp only [Function.comp_apply]
      rw [show R (ψ p') = ψ' (LCManifolds.tangentMap E F f p') from hrep'.symm,
        ψ'.left_inv hsrc]
    exact ((hcomp.congr heq).continuousAt (hW.mem_nhds hpW))
  -- smoothness of the local representatives
  refine ⟨hcont.continuousOn, fun p _ ↦ ?_⟩
  set x := p.proj
  obtain ⟨hD, hR⟩ := key x
  change ContDiffMBOn k (tangentChart ⟨chartAt F (f x), chart_mem_atlas F _⟩ (chartAt F (f x)) ∘
      LCManifolds.tangentMap E F f ∘
        (tangentChart ⟨chartAt E x, chart_mem_atlas E _⟩ (chartAt E x)).symm) _
  have hsub : chartDomain (LCManifolds.tangentMap E F f) univ
      (tangentChart ⟨chartAt E x, chart_mem_atlas E _⟩ (chartAt E x))
      (tangentChart ⟨chartAt F (f x), chart_mem_atlas F _⟩ (chartAt F (f x))) ⊆
      chartDomain f univ (chartAt E x) (chartAt F (f x)) ×ˢ univ := by
    rintro q ⟨hq, -, hqf⟩
    rw [mem_tangentChart_target] at hq
    rw [mem_preimage, mem_tangentChart_source] at hqf
    exact ⟨⟨hq.1, mem_univ _, hqf.1⟩, mem_univ _⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hcont.continuousOn _ _)
    (fun q hq ↦ (hrep x q (hsub hq)).symm) ((hR k le_rfl).mono hsub)

/-- `T id = id`. -/
theorem tangentMap_id (p : TangentBundle E M) : tangentMap E E (id : M → M) p = p := by
  obtain ⟨x, v⟩ := p
  change (⟨x, (tangentCoordChange ⟨chartAt E x, chart_mem_atlas E x⟩
    ⟨chartAt E x, chart_mem_atlas E x⟩ x (v : E) : E)⟩ : TangentBundle E M) = ⟨x, v⟩
  exact congrArg (Bundle.TotalSpace.mk (F := E) x)
    (tangentCoordChange_self ⟨chartAt E x, chart_mem_atlas E x⟩ (mem_chart_source E x) v)

variable {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P] [MBManifold G P]

/-- The chain rule `T(g ∘ f) = Tg ∘ Tf`. -/
theorem tangentMap_comp {f : M → N} {g : N → P} (hg : ContMDiffMB F G 1 g)
    (hf : ContMDiffMB E F 1 f) (p : TangentBundle E M) :
    tangentMap F G g (tangentMap E F f p) = tangentMap E G (g ∘ f) p := by
  obtain ⟨x, v⟩ := p
  set c := chartAt E x
  set c' := chartAt F (f x)
  set c'' := chartAt G (g (f x))
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  have hgc : Continuous g := continuousOn_univ.mp hg.1
  set U := c.target ∩ c.symm ⁻¹' (f ⁻¹' (c'.source ∩ g ⁻¹' c''.source))
  have hU : IsOpen U := c.isOpen_inter_preimage_symm
    ((c'.open_source.inter (c''.open_source.preimage hgc)).preimage hfc)
  have hxU : c x ∈ U := ⟨c.map_source (mem_chart_source E x), by
    simp [c, c', c'', c.left_inv (mem_chart_source E x), mem_chart_source]⟩
  have hg₀ : ContDiffMBOn 1 (c' ∘ f ∘ c.symm) U :=
    (hf.contDiffMBOn_chart isOpen_univ (chart_mem_atlas E x) (chart_mem_atlas F (f x))).mono
      fun z hz ↦ ⟨hz.1, mem_univ _, hz.2.1⟩
  have hg₁ : ContDiffMBOn 1 (c'' ∘ g ∘ c'.symm) (chartDomain g univ c' c'') :=
    hg.contDiffMBOn_chart isOpen_univ (chart_mem_atlas F (f x)) (chart_mem_atlas G _)
  have hmaps : MapsTo (c' ∘ f ∘ c.symm) U (chartDomain g univ c' c'') := by
    rintro z ⟨-, hz', hz''⟩
    exact ⟨c'.map_source hz', by simp [c'.left_inv hz', hz'']⟩
  have hh : c'' ∘ (g ∘ f) ∘ c.symm =ᶠ[𝓝 (c x)] (c'' ∘ g ∘ c'.symm) ∘ (c' ∘ f ∘ c.symm) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun z hz ↦ by
      simp [c'.left_inv hz.2.1]
  have := dMB_eq_comp_of_eventuallyEq (isOpen_chartDomain isOpen_univ hg.1 c' c'') hg₁ hg₀
    hmaps hxU hh v
  simp only [Function.comp_apply, c.left_inv (mem_chart_source E x)] at this
  change (⟨g (f x), (dMB (c'' ∘ g ∘ c'.symm)
      (c' (f x), dMB (c' ∘ f ∘ c.symm) (c x, (v : E))) : G)⟩ : TangentBundle G P) =
    ⟨g (f x), (dMB (c'' ∘ (g ∘ f) ∘ c.symm) (c x, (v : E)) : G)⟩
  rw [this]

end TangentMap

end LCManifolds
