/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.Higher
import LocallyConvexManifolds.Basic

/-!
# `C^k` maps between manifolds

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, §I.3; H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3.

Let `M` and `N` be manifolds modeled on locally convex spaces `E` and `F`. A map `f : M → N` is
`C^k` on an open set `U ⊆ M` if it is continuous on `U` and its local representatives
`chartAt (f x) ∘ f ∘ (chartAt x)⁻¹` are `C^k` in the sense of Michal–Bastiani on their (open)
domains. We show:

* `ContMDiffMBOn.contDiffMBOn_chart`: then the local representatives in *any* charts of the
  atlases are `C^k`, because the transition maps are smooth;
* `ContMDiffMBOn.comp`: compositions of `C^k` maps are `C^k`;
* identities and constant maps are smooth, and for maps between the model spaces themselves the
  notion agrees with `ContDiffMBOn` (`contMDiffMBOn_iff_contDiffMBOn`).
-/

open Set
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

section Domain

variable {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- The domain of the local representative `e' ∘ f ∘ e⁻¹` of `f` on `U`, in the charts `e`, `e'`:
the points of `e.target` that `e⁻¹` sends into `U ∩ f⁻¹ e'.source`. -/
def chartDomain (f : M → N) (U : Set M) (e : OpenPartialHomeomorph M E)
    (e' : OpenPartialHomeomorph N F) : Set E :=
  e.target ∩ e.symm ⁻¹' (U ∩ f ⁻¹' e'.source)

theorem isOpen_chartDomain {f : M → N} {U : Set M} (hU : IsOpen U) (hf : ContinuousOn f U)
    (e : OpenPartialHomeomorph M E) (e' : OpenPartialHomeomorph N F) :
    IsOpen (chartDomain f U e e') :=
  e.isOpen_inter_preimage_symm (hf.isOpen_inter_preimage hU e'.open_source)

end Domain

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]

/-- `f : M → N` is `C^k` on `U` (meant to be open): it is continuous on `U`, and its local
representatives in the preferred charts are `C^k` in the sense of Michal–Bastiani. -/
def ContMDiffMBOn (k : ℕ) (f : M → N) (U : Set M) : Prop :=
  ContinuousOn f U ∧ ∀ x ∈ U,
    ContDiffMBOn k (chartAt F (f x) ∘ f ∘ (chartAt E x).symm)
      (chartDomain f U (chartAt E x) (chartAt F (f x)))

variable (E F) in
/-- `C^k` maps `M → N`. -/
def ContMDiffMB (k : ℕ) (f : M → N) : Prop := ContMDiffMBOn (E := E) (F := F) k f univ

variable (E F) in
/-- Smooth maps on `U`. -/
def SmoothMBMOn (f : M → N) (U : Set M) : Prop := ∀ k, ContMDiffMBOn (E := E) (F := F) k f U

variable (E F) in
/-- Smooth maps `M → N`. -/
def SmoothMBM (f : M → N) : Prop := ∀ k, ContMDiffMB E F k f

theorem ContMDiffMBOn.continuousOn {k : ℕ} {f : M → N} {U : Set M}
    (hf : ContMDiffMBOn (E := E) (F := F) k f U) : ContinuousOn f U :=
  hf.1

variable
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Transition maps are smooth. -/
theorem smoothMBOn_transition [MBManifold E M] {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ atlas E M) (he' : e' ∈ atlas E M) :
    SmoothMBOn (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h := (HasGroupoid.compatible (G := mbGroupoid E) he he').1
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h
  exact h

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Transition maps between charts of the maximal atlas (charts compatible with the atlas) are
smooth. -/
theorem smoothMBOn_transition_of_mem_maximalAtlas [MBManifold E M]
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ (mbGroupoid E).maximalAtlas M)
    (he' : e' ∈ (mbGroupoid E).maximalAtlas M) :
    SmoothMBOn (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h := ((mbGroupoid E).compatible_of_mem_maximalAtlas he he').1
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h
  exact h

variable [MBManifold E M] [MBManifold F N] [MBManifold G P]

/-- The local representatives of a `C^k` map in arbitrary charts of the atlases are `C^k`. -/
theorem ContMDiffMBOn.contDiffMBOn_chart {k : ℕ} {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffMBOn (E := E) (F := F) k f U) {e : OpenPartialHomeomorph M E}
    (he : e ∈ atlas E M) {e' : OpenPartialHomeomorph N F} (he' : e' ∈ atlas F N) :
    ContDiffMBOn k (e' ∘ f ∘ e.symm) (chartDomain f U e e') := by
  have hD := isOpen_chartDomain hU hf.1 e e'
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  obtain ⟨hye, hyU, hyf⟩ := hy
  set p := e.symm y
  set c := chartAt E p
  set c' := chartAt F (f p)
  have hc : c ∈ atlas E M := chart_mem_atlas E p
  have hc' : c' ∈ atlas F N := chart_mem_atlas F (f p)
  -- near `y`, `e' ∘ f ∘ e⁻¹ = (e' ∘ c'⁻¹) ∘ (c' ∘ f ∘ c⁻¹) ∘ (c ∘ e⁻¹)`
  have hUf : ∀ {s : Set M} {t : Set N}, IsOpen s → IsOpen t → IsOpen (U ∩ s ∩ f ⁻¹' t) :=
    fun hs ht ↦ (hf.1.mono inter_subset_left).isOpen_inter_preimage (hU.inter hs) ht
  set W := e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' (c'.source ∩ e'.source))
  have hW : IsOpen W :=
    e.isOpen_inter_preimage_symm (hUf c.open_source (c'.open_source.inter e'.open_source))
  have hyW : y ∈ W :=
    ⟨hye, ⟨hyU, mem_chart_source E p⟩, mem_chart_source F (f p), hyf⟩
  set V := c.target ∩ c.symm ⁻¹' (U ∩ univ ∩ f ⁻¹' (c'.source ∩ e'.source))
  have hV : IsOpen V :=
    c.isOpen_inter_preimage_symm (hUf isOpen_univ (c'.open_source.inter e'.open_source))
  set T := c'.target ∩ c'.symm ⁻¹' e'.source
  have hT : IsOpen T := c'.isOpen_inter_preimage_symm e'.open_source
  have hτ : ContDiffMBOn k (c ∘ e.symm) W :=
    (smoothMBOn_transition he hc k).mono fun z hz ↦ ⟨hz.1, hz.2.1.2⟩
  have hμ : ContDiffMBOn k (c' ∘ f ∘ c.symm) V :=
    (hf.2 p hyU).mono fun z hz ↦ ⟨hz.1, hz.2.1.1, hz.2.2.1⟩
  have hτ' : ContDiffMBOn k (e' ∘ c'.symm) T := smoothMBOn_transition hc' he' k
  have h1 : MapsTo (c ∘ e.symm) W V := by
    rintro z ⟨-, ⟨hzU, hzc⟩, hzf⟩
    refine ⟨c.map_source hzc, ?_⟩
    simp only [Function.comp_apply, mem_preimage, c.left_inv hzc]
    exact ⟨⟨hzU, mem_univ _⟩, hzf⟩
  have h2 : MapsTo (c' ∘ f ∘ c.symm) V T := by
    rintro z ⟨-, -, hzc', hze'⟩
    refine ⟨c'.map_source hzc', ?_⟩
    simp only [Function.comp_apply, mem_preimage, c'.left_inv hzc']
    exact hze'
  have hcomp := (hτ'.comp hV hT hμ h2).comp hW hV hτ h1
  refine ⟨W, hW, hyW, (ContDiffMBOn.congr_of_isOpen hW ?_ hcomp).mono inter_subset_right⟩
  rintro z ⟨-, ⟨-, hzc⟩, hzc', -⟩
  simp only [Function.comp_apply, c.left_inv hzc, c'.left_inv hzc']

/-- The local representatives of a `C^k` map in charts of the maximal atlases (charts
compatible with the atlases) are `C^k`. -/
theorem ContMDiffMBOn.contDiffMBOn_chart_of_mem_maximalAtlas {k : ℕ} {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffMBOn (E := E) (F := F) k f U) {e : OpenPartialHomeomorph M E}
    (he : e ∈ (mbGroupoid E).maximalAtlas M) {e' : OpenPartialHomeomorph N F}
    (he' : e' ∈ (mbGroupoid F).maximalAtlas N) :
    ContDiffMBOn k (e' ∘ f ∘ e.symm) (chartDomain f U e e') := by
  have hD := isOpen_chartDomain hU hf.1 e e'
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  obtain ⟨hye, hyU, hyf⟩ := hy
  set p := e.symm y
  set c := chartAt E p
  set c' := chartAt F (f p)
  have hc : c ∈ (mbGroupoid E).maximalAtlas M := (mbGroupoid E).chart_mem_maximalAtlas p
  have hc' : c' ∈ (mbGroupoid F).maximalAtlas N := (mbGroupoid F).chart_mem_maximalAtlas (f p)
  -- near `y`, `e' ∘ f ∘ e⁻¹ = (e' ∘ c'⁻¹) ∘ (c' ∘ f ∘ c⁻¹) ∘ (c ∘ e⁻¹)`
  have hUf : ∀ {s : Set M} {t : Set N}, IsOpen s → IsOpen t → IsOpen (U ∩ s ∩ f ⁻¹' t) :=
    fun hs ht ↦ (hf.1.mono inter_subset_left).isOpen_inter_preimage (hU.inter hs) ht
  set W := e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' (c'.source ∩ e'.source))
  have hW : IsOpen W :=
    e.isOpen_inter_preimage_symm (hUf c.open_source (c'.open_source.inter e'.open_source))
  have hyW : y ∈ W :=
    ⟨hye, ⟨hyU, mem_chart_source E p⟩, mem_chart_source F (f p), hyf⟩
  set V := c.target ∩ c.symm ⁻¹' (U ∩ univ ∩ f ⁻¹' (c'.source ∩ e'.source))
  have hV : IsOpen V :=
    c.isOpen_inter_preimage_symm (hUf isOpen_univ (c'.open_source.inter e'.open_source))
  set T := c'.target ∩ c'.symm ⁻¹' e'.source
  have hT : IsOpen T := c'.isOpen_inter_preimage_symm e'.open_source
  have hτ : ContDiffMBOn k (c ∘ e.symm) W :=
    (smoothMBOn_transition_of_mem_maximalAtlas he hc k).mono fun z hz ↦ ⟨hz.1, hz.2.1.2⟩
  have hμ : ContDiffMBOn k (c' ∘ f ∘ c.symm) V :=
    (hf.2 p hyU).mono fun z hz ↦ ⟨hz.1, hz.2.1.1, hz.2.2.1⟩
  have hτ' : ContDiffMBOn k (e' ∘ c'.symm) T := smoothMBOn_transition_of_mem_maximalAtlas hc' he' k
  have h1 : MapsTo (c ∘ e.symm) W V := by
    rintro z ⟨-, ⟨hzU, hzc⟩, hzf⟩
    refine ⟨c.map_source hzc, ?_⟩
    simp only [Function.comp_apply, mem_preimage, c.left_inv hzc]
    exact ⟨⟨hzU, mem_univ _⟩, hzf⟩
  have h2 : MapsTo (c' ∘ f ∘ c.symm) V T := by
    rintro z ⟨-, -, hzc', hze'⟩
    refine ⟨c'.map_source hzc', ?_⟩
    simp only [Function.comp_apply, mem_preimage, c'.left_inv hzc']
    exact hze'
  have hcomp := (hτ'.comp hV hT hμ h2).comp hW hV hτ h1
  refine ⟨W, hW, hyW, (ContDiffMBOn.congr_of_isOpen hW ?_ hcomp).mono inter_subset_right⟩
  rintro z ⟨-, ⟨-, hzc⟩, hzc', -⟩
  simp only [Function.comp_apply, c.left_inv hzc, c'.left_inv hzc']

/-- A continuous map whose local representatives in the preferred charts are `C^k` near the
center of each chart is `C^k`. -/
theorem contMDiffMB_of_chartAt {k : ℕ} {f : M → N} (hf : Continuous f)
    (h : ∀ x, ∃ O : Set E, IsOpen O ∧ chartAt E x x ∈ O ∧
      O ⊆ chartDomain f univ (chartAt E x) (chartAt F (f x)) ∧
      ContDiffMBOn k (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) O) :
    ContMDiffMB E F k f := by
  refine ⟨hf.continuousOn, fun x _ ↦ ?_⟩
  set e := chartAt E x
  set e' := chartAt F (f x)
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have he' : e' ∈ atlas F N := chart_mem_atlas F (f x)
  have hD := isOpen_chartDomain isOpen_univ hf.continuousOn e e'
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  obtain ⟨hye, -, hyf⟩ := hy
  set p := e.symm y
  set c := chartAt E p
  set c' := chartAt F (f p)
  have hc : c ∈ atlas E M := chart_mem_atlas E p
  have hc' : c' ∈ atlas F N := chart_mem_atlas F (f p)
  obtain ⟨O, hO, hpO, hOD, hμ⟩ := h p
  -- near `y`, `e' ∘ f ∘ e⁻¹ = (e' ∘ c'⁻¹) ∘ (c' ∘ f ∘ c⁻¹) ∘ (c ∘ e⁻¹)`
  have hτ : ContDiffMBOn k (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source) :=
    smoothMBOn_transition he hc k
  have hτc : ContinuousOn (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source) := hτ.continuousOn
  set W := (e.target ∩ e.symm ⁻¹' (c.source ∩ f ⁻¹' e'.source)) ∩ (c ∘ e.symm) ⁻¹' O
  have hW : IsOpen W := by
    have h1 : IsOpen (e.target ∩ e.symm ⁻¹' (c.source ∩ f ⁻¹' e'.source)) :=
      e.isOpen_inter_preimage_symm (c.open_source.inter (e'.open_source.preimage hf))
    exact (hτc.mono fun z (hz : z ∈ e.target ∩ e.symm ⁻¹' (c.source ∩ f ⁻¹' e'.source)) ↦
      ⟨hz.1, hz.2.1⟩).isOpen_inter_preimage h1 hO
  have hyW : y ∈ W := ⟨⟨hye, mem_chart_source E p, hyf⟩, by
    change c (e.symm y) ∈ O
    exact hpO⟩
  set T := c'.target ∩ c'.symm ⁻¹' e'.source
  have hT : IsOpen T := c'.isOpen_inter_preimage_symm e'.open_source
  have hτ' : ContDiffMBOn k (e' ∘ c'.symm) T := smoothMBOn_transition hc' he' k
  have h1 : MapsTo (c ∘ e.symm) W O := fun z hz ↦ hz.2
  have h2 : MapsTo (c' ∘ f ∘ c.symm) (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) T := fun z hz ↦ hz.2
  have hOT : IsOpen (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) := hμ.continuousOn.isOpen_inter_preimage hO hT
  have h1' : MapsTo (c ∘ e.symm) W (O ∩ (c' ∘ f ∘ c.symm) ⁻¹' T) := by
    rintro z ⟨⟨hze, hzc, hzf⟩, hzO⟩
    refine ⟨hzO, ?_⟩
    have hcz : c.symm (c (e.symm z)) = e.symm z := c.left_inv hzc
    have hzc' : f (e.symm z) ∈ c'.source := by
      have := (hOD hzO).2.2
      change f (c.symm (c (e.symm z))) ∈ c'.source at this
      rwa [hcz] at this
    refine ⟨by simp only [Function.comp_apply, hcz]; exact c'.map_source hzc', ?_⟩
    simp only [Function.comp_apply, mem_preimage, hcz, c'.left_inv hzc']
    exact hzf
  have hcomp := (hτ'.comp hOT hT (hμ.mono inter_subset_left) h2).comp hW hOT
    (hτ.mono fun z hz ↦ ⟨hz.1.1, hz.1.2.1⟩) h1'
  refine ⟨W, hW, hyW, (ContDiffMBOn.congr_of_isOpen hW ?_ hcomp).mono inter_subset_right⟩
  rintro z ⟨⟨-, hzc, -⟩, hzO⟩
  have hcz : c.symm (c (e.symm z)) = e.symm z := c.left_inv hzc
  have hzc' : f (e.symm z) ∈ c'.source := by
    have := (hOD hzO).2.2
    change f (c.symm (c (e.symm z))) ∈ c'.source at this
    rwa [hcz] at this
  change e' (c'.symm (c' (f (c.symm (c (e.symm z)))))) = e' (f (e.symm z))
  rw [hcz, c'.left_inv hzc']

/-- Compositions of `C^k` maps are `C^k`. -/
theorem ContMDiffMBOn.comp {k : ℕ} {f : M → N} {g : N → P} {U : Set M} {V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ContMDiffMBOn (E := F) (F := G) k g V)
    (hf : ContMDiffMBOn (E := E) (F := F) k f U) (hUV : MapsTo f U V) :
    ContMDiffMBOn (E := E) (F := G) k (g ∘ f) U := by
  have hgf : ContinuousOn (g ∘ f) U := hg.1.comp hf.1 hUV
  refine ⟨hgf, fun x hx ↦ ?_⟩
  set c := chartAt E x
  set c'' := chartAt G (g (f x))
  have hD := isOpen_chartDomain hU hgf c c''
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  have hyU : c.symm y ∈ U := hy.2.1
  set d := chartAt F (f (c.symm y))
  set W := chartDomain f U c d ∩ chartDomain (g ∘ f) U c c''
  have hW : IsOpen W := (isOpen_chartDomain hU hf.1 c d).inter hD
  have hyW : y ∈ W := ⟨⟨hy.1, hyU, mem_chart_source F _⟩, hy⟩
  have hgd : ContDiffMBOn k (c'' ∘ g ∘ d.symm) (chartDomain g V d c'') :=
    hg.contDiffMBOn_chart hV (chart_mem_atlas F _) (chart_mem_atlas G _)
  have hfd : ContDiffMBOn k (d ∘ f ∘ c.symm) W :=
    (hf.contDiffMBOn_chart hU (chart_mem_atlas E x) (chart_mem_atlas F _)).mono
      inter_subset_left
  have hmaps : MapsTo (d ∘ f ∘ c.symm) W (chartDomain g V d c'') := by
    rintro z ⟨⟨-, hzU, hzd⟩, -, -, hzg⟩
    refine ⟨d.map_source hzd, ?_, ?_⟩
    · simp only [Function.comp_apply, d.left_inv hzd]; exact hUV hzU
    · simp only [Function.comp_apply, mem_preimage, d.left_inv hzd]; exact hzg
  have hcomp := hgd.comp hW (isOpen_chartDomain hV hg.1 d c'') hfd hmaps
  refine ⟨W, hW, hyW, (ContDiffMBOn.congr_of_isOpen hW ?_ hcomp).mono inter_subset_right⟩
  rintro z ⟨⟨-, -, hzd⟩, -⟩
  simp only [Function.comp_apply, d.left_inv hzd]
  rfl

/-- Compositions of smooth maps are smooth. -/
theorem SmoothMBMOn.comp {f : M → N} {g : N → P} {U : Set M} {V : Set N} (hU : IsOpen U)
    (hV : IsOpen V) (hg : SmoothMBMOn F G g V) (hf : SmoothMBMOn E F f U) (hUV : MapsTo f U V) :
    SmoothMBMOn E G (g ∘ f) U :=
  fun k ↦ (hg k).comp hU hV (hf k) hUV

/-- Compositions of smooth maps are smooth. -/
theorem SmoothMBM.comp {f : M → N} {g : N → P} (hg : SmoothMBM F G g) (hf : SmoothMBM E F f) :
    SmoothMBM E G (g ∘ f) :=
  fun k ↦ (hg k).comp isOpen_univ isOpen_univ (hf k) (mapsTo_univ _ _)

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- The identity is smooth. -/
theorem smoothMBMOn_id {U : Set M} (hU : IsOpen U) : SmoothMBMOn E E (id : M → M) U := by
  refine fun k ↦ ⟨continuousOn_id, fun x _ ↦ ?_⟩
  set c := chartAt E x
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain hU continuousOn_id c c)
    (fun z hz ↦ ?_) ((smoothMBOn_id _ k).mono subset_rfl)
  exact (c.right_inv hz.1).symm

omit [MBManifold E M] [MBManifold F N] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- Constant maps are smooth. -/
theorem smoothMBMOn_const (U : Set M) (n : N) :
    SmoothMBMOn E F (fun _ : M ↦ n) U := by
  refine fun k ↦ ⟨continuousOn_const, fun x _ ↦ ?_⟩
  exact contDiffMBOn_const (E₁ := E) k (chartAt F n n) _

omit [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [ChartedSpace G P]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  [MBManifold G P] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- For maps between the model spaces, `C^k` maps in the sense of manifolds are the `C^k` maps in
the sense of Michal–Bastiani. -/
theorem contMDiffMBOn_iff_contDiffMBOn {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U) :
    ContMDiffMBOn (E := E) (F := F) k f U ↔ ContDiffMBOn k f U := by
  have hD : ∀ x : E, chartDomain f U (chartAt E x) (chartAt F (f x)) = U := fun x ↦ by
    simp [chartDomain]
  constructor
  · intro hf
    refine ContDiffMBOn.of_local hU fun x hx ↦ ⟨U, hU, hx, ?_⟩
    have := hf.2 x hx
    rw [hD] at this
    simpa using this
  · intro hf
    refine ⟨hf.continuousOn, fun x _ ↦ ?_⟩
    rw [hD]
    simpa using hf

end LocallyConvex.Manifolds
