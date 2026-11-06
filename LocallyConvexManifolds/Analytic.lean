/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.InverseAlgebra
import LocallyConvexManifolds.ContMDiff

/-!
# Real and complex analytic manifolds

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362),
Definitions 3.1.3–3.1.4 (`C^r`-manifolds for `r ∈ ℕ₀ ∪ {∞, ω}`; the `C^ω_𝕂`-manifolds are the
`𝕂`-analytic manifolds), Example 3.1.8, and Definition 2.2.18 (complexifications).

As for smooth manifolds (`LocallyConvexManifolds.Basic`), an analytic manifold is a `ChartedSpace` whose
transition maps lie in a structure groupoid:

* `realAnalyticGroupoid E`: the homeomorphisms between open subsets of a real locally convex
  space `E` which are real analytic in the sense of Milnor (`LocallyConvex.Analysis.RealAnalyticOn`:
  restrictions of complex analytic maps on open subsets of `E_ℂ`), together with their inverses;
* `complexAnalyticGroupoid E`: the same for a complex locally convex space `E` and complex
  analytic maps (`LocallyConvex.Analysis.ComplexAnalyticOn`).

No completeness of the model space is assumed (GN's convention, see `LocallyConvexManifolds.Basic`): the
facts used about analytic maps (composition, locality, analytic implies smooth, complex
analytic implies real analytic) hold without completeness in `LocallyConvex.Analysis`.

## Main results

* `realAnalyticGroupoid_le_mbGroupoid`, `complexAnalyticGroupoid_le_realAnalyticGroupoid`:
  every complex analytic manifold is real analytic (GN, Proposition 2.2.11) and every real
  analytic manifold is smooth (GN, Lemma 2.2.5); both are instances.
* Open subsets of analytic manifolds are analytic manifolds (GN, Example 3.1.9), through
  Mathlib's `TopologicalSpace.Opens` charted space and `ClosedUnderRestriction`.
* `RealAnalyticMOn`, `ComplexAnalyticMOn`: analytic maps between analytic manifolds, defined
  through the preferred charts. Their local representatives in *any* charts of the maximal atlases
  are analytic (`RealAnalyticMOn.realAnalyticOn_chart`), they compose, identities and constants
  are analytic, analytic maps are smooth, complex analytic maps are real analytic, and on the
  model spaces the notions agree with those of `LocallyConvex.Analysis`.
* `IsComplexification`: GN, Definition 2.2.18; `E_ℂ` is a complexification of `E`.
* Example: inversion on the (open) unit group of a real continuous inverse algebra is a real
  analytic map (GN, Proposition 2.2.13).
-/

open Set
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Congruence of analytic maps -/

section Congr

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- Real analyticity on a set only depends on the values on that set (the set need not be open:
the complex extension is only required to extend `f` on `U`). -/
theorem realAnalyticOn_congr {f g : E → F} {U : Set E} (h : EqOn f g U)
    (hf : RealAnalyticOn f U) : RealAnalyticOn g U := by
  obtain ⟨V, hV, G, hG, hext⟩ := hf
  exact ⟨V, hV, G, hG, fun x hx ↦ ⟨(hext x hx).1, by rw [← h hx]; exact (hext x hx).2⟩⟩

end Congr

/-! ### The analytic groupoids -/

section RealGroupoid

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The groupoid of real analytic diffeomorphisms between open subsets of the real locally convex
space `E`: real analytic (in the sense of Milnor) homeomorphisms with real analytic inverses. -/
def realAnalyticGroupoid : StructureGroupoid E where
  members := {e | RealAnalyticOn e e.source ∧ RealAnalyticOn e.symm e.target}
  trans' e e' he he' := by
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.coe_trans]
      refine he'.1.comp (he.1.mono ?_) fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_source]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_source] at hx; exact hx.2
    · rw [OpenPartialHomeomorph.coe_trans_symm]
      refine he.2.comp (he'.2.mono ?_) fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_target]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_target] at hx; exact hx.2
  symm' := fun _ he ↦ ⟨he.2, he.1⟩
  id_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using (ContinuousLinearMap.id ℝ E).realAnalyticOn univ
  locality' e h := by
    refine ⟨RealAnalyticOn.of_local e.open_source fun x hx ↦ ?_,
      RealAnalyticOn.of_local e.open_target fun y hy ↦ ?_⟩
    · obtain ⟨s, hs, hxs, hes⟩ := h x hx
      refine ⟨s, hs, hxs, ?_⟩
      have := hes.1
      rwa [e.restr_source' s hs] at this
    · obtain ⟨s, hs, hxs, hes⟩ := h (e.symm y) (e.map_target hy)
      refine ⟨e.target ∩ e.symm ⁻¹' s, e.isOpen_inter_preimage_symm hs, ⟨hy, hxs⟩, ?_⟩
      have := hes.2
      have ht : (e.restr s).target = e.target ∩ e.symm ⁻¹' s := by
        rw [e.restr_toPartialEquiv' s hs]
        rfl
      rw [ht] at this
      rwa [← inter_assoc, inter_self]
  mem_of_eqOnSource' e e' he heq := by
    refine ⟨?_, ?_⟩
    · rw [heq.source_eq]
      exact realAnalyticOn_congr (fun x hx ↦ (heq.eqOn (heq.source_eq ▸ hx)).symm) he.1
    · have hs := heq.symm'
      change RealAnalyticOn e'.symm e'.symm.source
      rw [hs.source_eq]
      exact realAnalyticOn_congr (fun x hx ↦ (hs.eqOn (hs.source_eq ▸ hx)).symm) he.2

theorem mem_realAnalyticGroupoid {e : OpenPartialHomeomorph E E} :
    e ∈ realAnalyticGroupoid E ↔ RealAnalyticOn e e.source ∧ RealAnalyticOn e.symm e.target :=
  Iff.rfl

/-- **Real analytic diffeomorphisms are smooth diffeomorphisms** (GN, Lemma 2.2.5). -/
theorem realAnalyticGroupoid_le_mbGroupoid : realAnalyticGroupoid E ≤ mbGroupoid E :=
  StructureGroupoid.le_iff.2 fun e he ↦
    ⟨he.1.smoothMBOn e.open_source, he.2.smoothMBOn e.open_target⟩

instance : ClosedUnderRestriction (realAnalyticGroupoid E) where
  closedUnderRestriction he _ _ :=
    ⟨he.1.mono fun _ hx ↦ hx.1, he.2.mono fun _ hx ↦ hx.1⟩

end RealGroupoid

section ComplexGroupoid

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E]

attribute [local instance] continuousSMul_real_of_complex

/-- The groupoid of complex analytic diffeomorphisms between open subsets of the complex locally
convex space `E`. -/
def complexAnalyticGroupoid : StructureGroupoid E where
  members := {e | ComplexAnalyticOn e e.source ∧ ComplexAnalyticOn e.symm e.target}
  trans' e e' he he' := by
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.coe_trans]
      refine he'.1.comp (he.1.mono e.open_source (e.trans e').open_source ?_)
        (e.trans e').open_source e'.open_source fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_source]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_source] at hx; exact hx.2
    · rw [OpenPartialHomeomorph.coe_trans_symm]
      refine he.2.comp (he'.2.mono e'.open_target (e.trans e').open_target ?_)
        (e.trans e').open_target e.open_target fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_target]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_target] at hx; exact hx.2
  symm' := fun _ he ↦ ⟨he.2, he.1⟩
  id_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using (ContinuousLinearMap.id ℂ E).complexAnalyticOn isOpen_univ
  locality' e h := by
    refine ⟨ComplexAnalyticOn.of_local e.open_source fun x hx ↦ ?_,
      ComplexAnalyticOn.of_local e.open_target fun y hy ↦ ?_⟩
    · obtain ⟨s, hs, hxs, hes⟩ := h x hx
      refine ⟨s, hs, hxs, ?_⟩
      have := hes.1
      rwa [e.restr_source' s hs] at this
    · obtain ⟨s, hs, hxs, hes⟩ := h (e.symm y) (e.map_target hy)
      refine ⟨e.target ∩ e.symm ⁻¹' s, e.isOpen_inter_preimage_symm hs, ⟨hy, hxs⟩, ?_⟩
      have := hes.2
      have ht : (e.restr s).target = e.target ∩ e.symm ⁻¹' s := by
        rw [e.restr_toPartialEquiv' s hs]
        rfl
      rw [ht] at this
      rwa [← inter_assoc, inter_self]
  mem_of_eqOnSource' e e' he heq := by
    refine ⟨?_, ?_⟩
    · rw [heq.source_eq]
      exact he.1.congr e.open_source fun x hx ↦ (heq.eqOn (heq.source_eq ▸ hx)).symm
    · have hs := heq.symm'
      change ComplexAnalyticOn e'.symm e'.symm.source
      rw [hs.source_eq]
      exact he.2.congr e.symm.open_source fun x hx ↦ (hs.eqOn (hs.source_eq ▸ hx)).symm

theorem mem_complexAnalyticGroupoid {e : OpenPartialHomeomorph E E} :
    e ∈ complexAnalyticGroupoid E ↔
      ComplexAnalyticOn e e.source ∧ ComplexAnalyticOn e.symm e.target :=
  Iff.rfl

/-- **Complex analytic diffeomorphisms are real analytic diffeomorphisms** (GN,
Proposition 2.2.11), without completeness. -/
theorem complexAnalyticGroupoid_le_realAnalyticGroupoid :
    complexAnalyticGroupoid E ≤ realAnalyticGroupoid E :=
  StructureGroupoid.le_iff.2 fun e he ↦
    ⟨he.1.realAnalyticOn e.open_source, he.2.realAnalyticOn e.open_target⟩

instance : ClosedUnderRestriction (complexAnalyticGroupoid E) where
  closedUnderRestriction {e} he s _ :=
    ⟨he.1.mono e.open_source (e.restr s).open_source fun _ hx ↦ hx.1,
      he.2.mono e.open_target (e.restr s).open_target fun _ hx ↦ hx.1⟩

end ComplexGroupoid

/-! ### Analytic manifolds -/

section Manifolds

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- A **real analytic manifold** modeled on the real locally convex space `E` (GN,
Definition 3.1.4 with `r = ω`, `𝕂 = ℝ`): the transition maps are real analytic. -/
abbrev RealAnalyticManifold (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  HasGroupoid M (realAnalyticGroupoid E)

/-- Real analytic manifolds are smooth manifolds. -/
instance (priority := 100) RealAnalyticManifold.mbManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace E M] [h : RealAnalyticManifold E M] : MBManifold E M :=
  hasGroupoid_of_le h (realAnalyticGroupoid_le_mbGroupoid E)

end Manifolds

section ComplexManifolds

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E]

/-- A **complex analytic manifold** modeled on the complex locally convex space `E` (GN,
Definition 3.1.4 with `r = ω`, `𝕂 = ℂ`): the transition maps are complex analytic. -/
abbrev ComplexAnalyticManifold (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  HasGroupoid M (complexAnalyticGroupoid E)

attribute [local instance] continuousSMul_real_of_complex

/-- Complex analytic manifolds are real analytic manifolds (GN, Proposition 2.2.11). -/
theorem ComplexAnalyticManifold.realAnalyticManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace E M] [h : ComplexAnalyticManifold E M] : RealAnalyticManifold E M :=
  hasGroupoid_of_le h (complexAnalyticGroupoid_le_realAnalyticGroupoid E)

end ComplexManifolds

/-! ### Changing charts -/

section ChartChange

variable {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- **Insertion of charts** (GN, Remark 3.1.5), the set-theoretic part: near a point `y` of the
domain of the local representative `e' ∘ f ∘ e⁻¹`, it factors as
`(e' ∘ c'⁻¹) ∘ (c' ∘ f ∘ c⁻¹) ∘ (c ∘ e⁻¹)` through other charts `c`, `c'`, with explicit open
domains. Used to show that every regularity class closed under composition and local is chart
independent. -/
theorem exists_chartChange {f : M → N} {U : Set M} (hU : IsOpen U) (hf : ContinuousOn f U)
    (e c : OpenPartialHomeomorph M E) (e' c' : OpenPartialHomeomorph N F) {y : E}
    (hy : y ∈ chartDomain f U e e') (hc : e.symm y ∈ c.source)
    (hc' : f (e.symm y) ∈ c'.source) :
    ∃ W V : Set E, IsOpen W ∧ IsOpen V ∧ y ∈ W ∧ W ⊆ chartDomain f U e e' ∧
      W ⊆ e.target ∩ e.symm ⁻¹' c.source ∧ V ⊆ chartDomain f U c c' ∧
      MapsTo (c ∘ e.symm) W V ∧ MapsTo (c' ∘ f ∘ c.symm) V (c'.target ∩ c'.symm ⁻¹' e'.source) ∧
      EqOn (e' ∘ f ∘ e.symm) (((e' ∘ c'.symm) ∘ (c' ∘ f ∘ c.symm)) ∘ (c ∘ e.symm)) W := by
  obtain ⟨hye, hyU, hyf⟩ := hy
  have hUf : ∀ {t : Set N}, IsOpen t → IsOpen (U ∩ f ⁻¹' t) :=
    fun ht ↦ hf.isOpen_inter_preimage hU ht
  refine ⟨e.target ∩ e.symm ⁻¹' (U ∩ c.source ∩ f ⁻¹' (c'.source ∩ e'.source)),
    c.target ∩ c.symm ⁻¹' (U ∩ f ⁻¹' (c'.source ∩ e'.source)), ?_, ?_,
    ⟨hye, ⟨hyU, hc⟩, hc', hyf⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine e.isOpen_inter_preimage_symm ?_
    rw [inter_right_comm]
    exact (hUf (c'.open_source.inter e'.open_source)).inter c.open_source
  · exact c.isOpen_inter_preimage_symm (hUf (c'.open_source.inter e'.open_source))
  · rintro z ⟨hz, ⟨hzU, -⟩, -, hzf⟩; exact ⟨hz, hzU, hzf⟩
  · rintro z ⟨hz, ⟨-, hzc⟩, -⟩; exact ⟨hz, hzc⟩
  · rintro z ⟨hz, hzU, hzc', -⟩; exact ⟨hz, hzU, hzc'⟩
  · rintro z ⟨-, ⟨hzU, hzc⟩, hzf⟩
    refine ⟨c.map_source hzc, ?_⟩
    simp only [Function.comp_apply, mem_preimage, c.left_inv hzc]
    exact ⟨hzU, hzf⟩
  · rintro z ⟨-, -, hzc', hze'⟩
    refine ⟨c'.map_source hzc', ?_⟩
    simp only [Function.comp_apply, mem_preimage, c'.left_inv hzc']
    exact hze'
  · rintro z ⟨-, ⟨-, hzc⟩, hzc', -⟩
    simp only [Function.comp_apply, c.left_inv hzc, c'.left_inv hzc']

end ChartChange

/-! ### Real analytic maps between manifolds -/

section RealMaps

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]

/-- `f : M → N` is **real analytic** on `U` (meant to be open): it is continuous on `U`, and its
local representatives in the preferred charts are real analytic. -/
def RealAnalyticMOn (f : M → N) (U : Set M) : Prop :=
  ContinuousOn f U ∧ ∀ x ∈ U,
    RealAnalyticOn (chartAt F (f x) ∘ f ∘ (chartAt E x).symm)
      (chartDomain f U (chartAt E x) (chartAt F (f x)))

variable
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Transition maps between charts of the maximal atlas of a real analytic manifold are real
analytic. -/
theorem realAnalyticOn_transition [RealAnalyticManifold E M] {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ (realAnalyticGroupoid E).maximalAtlas M)
    (he' : e' ∈ (realAnalyticGroupoid E).maximalAtlas M) :
    RealAnalyticOn (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h := ((realAnalyticGroupoid E).compatible_of_mem_maximalAtlas he he').1
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h
  exact h

variable [RealAnalyticManifold E M] [RealAnalyticManifold F N] [RealAnalyticManifold G P]

/-- The local representatives of a real analytic map in arbitrary charts of the maximal atlases
are real analytic. -/
theorem RealAnalyticMOn.realAnalyticOn_chart {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : RealAnalyticMOn (E := E) (F := F) f U) {e : OpenPartialHomeomorph M E}
    (he : e ∈ (realAnalyticGroupoid E).maximalAtlas M) {e' : OpenPartialHomeomorph N F}
    (he' : e' ∈ (realAnalyticGroupoid F).maximalAtlas N) :
    RealAnalyticOn (e' ∘ f ∘ e.symm) (chartDomain f U e e') := by
  refine RealAnalyticOn.of_local (isOpen_chartDomain hU hf.1 e e') fun y hy ↦ ?_
  set p := e.symm y
  obtain ⟨W, V, hW, -, hyW, hWD, hWτ, hVD, h1, h2, heq⟩ :=
    exists_chartChange hU hf.1 e (chartAt E p) e' (chartAt F (f p)) hy (mem_chart_source E p)
      (mem_chart_source F (f p))
  have hτ := (realAnalyticOn_transition he
    ((realAnalyticGroupoid E).chart_mem_maximalAtlas p)).mono hWτ
  have hμ := (hf.2 p hy.2.1).mono hVD
  have hτ' := realAnalyticOn_transition ((realAnalyticGroupoid F).chart_mem_maximalAtlas (f p)) he'
  refine ⟨W, hW, hyW, ?_⟩
  rw [inter_eq_right.2 hWD]
  exact realAnalyticOn_congr heq.symm ((hτ'.comp hμ h2).comp hτ h1)

/-- Compositions of real analytic maps are real analytic. -/
theorem RealAnalyticMOn.comp {f : M → N} {g : N → P} {U : Set M} {V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hg : RealAnalyticMOn (E := F) (F := G) g V)
    (hf : RealAnalyticMOn (E := E) (F := F) f U) (hUV : MapsTo f U V) :
    RealAnalyticMOn (E := E) (F := G) (g ∘ f) U := by
  have hgf : ContinuousOn (g ∘ f) U := hg.1.comp hf.1 hUV
  refine ⟨hgf, fun x hx ↦ ?_⟩
  set c := chartAt E x
  set c'' := chartAt G (g (f x))
  have hD := isOpen_chartDomain hU hgf c c''
  refine RealAnalyticOn.of_local hD fun y hy ↦ ?_
  have hyU : c.symm y ∈ U := hy.2.1
  set d := chartAt F (f (c.symm y))
  set W := chartDomain f U c d ∩ chartDomain (g ∘ f) U c c''
  have hW : IsOpen W := (isOpen_chartDomain hU hf.1 c d).inter hD
  have hyW : y ∈ W := ⟨⟨hy.1, hyU, mem_chart_source F _⟩, hy⟩
  have hgd : RealAnalyticOn (c'' ∘ g ∘ d.symm) (chartDomain g V d c'') :=
    hg.realAnalyticOn_chart hV ((realAnalyticGroupoid F).chart_mem_maximalAtlas _)
      ((realAnalyticGroupoid G).chart_mem_maximalAtlas _)
  have hfd : RealAnalyticOn (d ∘ f ∘ c.symm) W :=
    (hf.realAnalyticOn_chart hU ((realAnalyticGroupoid E).chart_mem_maximalAtlas x)
      ((realAnalyticGroupoid F).chart_mem_maximalAtlas _)).mono inter_subset_left
  have hmaps : MapsTo (d ∘ f ∘ c.symm) W (chartDomain g V d c'') := by
    rintro z ⟨⟨-, hzU, hzd⟩, -, -, hzg⟩
    refine ⟨d.map_source hzd, ?_, ?_⟩
    · simp only [Function.comp_apply, d.left_inv hzd]; exact hUV hzU
    · simp only [Function.comp_apply, mem_preimage, d.left_inv hzd]; exact hzg
  refine ⟨W, hW, hyW, (realAnalyticOn_congr ?_ (hgd.comp hfd hmaps)).mono inter_subset_right⟩
  rintro z ⟨⟨-, -, hzd⟩, -⟩
  simp only [Function.comp_apply, d.left_inv hzd]
  rfl

omit [RealAnalyticManifold E M] [RealAnalyticManifold F N] [RealAnalyticManifold G P] in
/-- **Real analytic maps are smooth** (GN, Lemma 2.2.5, globalized). -/
theorem RealAnalyticMOn.smoothMBMOn {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : RealAnalyticMOn (E := E) (F := F) f U) : SmoothMBMOn E F f U :=
  fun k ↦ ⟨hf.1, fun x hx ↦ (hf.2 x hx).smoothMBOn (isOpen_chartDomain hU hf.1 _ _) k⟩

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [RealAnalyticManifold E M] [RealAnalyticManifold F N] [RealAnalyticManifold G P] in
/-- The identity is real analytic. -/
theorem realAnalyticMOn_id (U : Set M) : RealAnalyticMOn (E := E) (F := E) (id : M → M) U := by
  refine ⟨continuousOn_id, fun x _ ↦ realAnalyticOn_congr (fun z hz ↦ ?_)
    ((ContinuousLinearMap.id ℝ E).realAnalyticOn _)⟩
  exact (OpenPartialHomeomorph.right_inv _ hz.1).symm

omit [RealAnalyticManifold E M] [RealAnalyticManifold F N] [RealAnalyticManifold G P] in
/-- Constant maps are real analytic. -/
theorem realAnalyticMOn_const (U : Set M) (n : N) :
    RealAnalyticMOn (E := E) (F := F) (fun _ : M ↦ n) U :=
  ⟨continuousOn_const, fun _ _ ↦ realAnalyticOn_const (chartAt F n n) _⟩

omit [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [ChartedSpace G P]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  [RealAnalyticManifold E M] [RealAnalyticManifold F N] [RealAnalyticManifold G P] in
/-- For maps between the model spaces, real analytic maps in the sense of manifolds are the real
analytic maps in the sense of `LocallyConvex.Analysis`. -/
theorem realAnalyticMOn_iff_realAnalyticOn {f : E → F} {U : Set E} (hU : IsOpen U) :
    RealAnalyticMOn (E := E) (F := F) f U ↔ RealAnalyticOn f U := by
  have hD : ∀ x : E, chartDomain f U (chartAt E x) (chartAt F (f x)) = U := fun x ↦ by
    simp [chartDomain]
  constructor
  · intro hf
    refine RealAnalyticOn.of_local hU fun x hx ↦ ⟨U, hU, hx, ?_⟩
    have := hf.2 x hx
    rw [hD] at this
    simpa using this
  · intro hf
    refine ⟨((hf.smoothMBOn hU) 0).continuousOn, fun x _ ↦ ?_⟩
    rw [hD]
    simpa using hf

end RealMaps

/-! ### Complex analytic maps between manifolds -/

section ComplexMaps

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [AddCommGroup G] [Module ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℂ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]

attribute [local instance] continuousSMul_real_of_complex

/-- `f : M → N` is **complex analytic** on `U` (meant to be open): it is continuous on `U`, and
its local representatives in the preferred charts are complex analytic. -/
def ComplexAnalyticMOn (f : M → N) (U : Set M) : Prop :=
  ContinuousOn f U ∧ ∀ x ∈ U,
    ComplexAnalyticOn (chartAt F (f x) ∘ f ∘ (chartAt E x).symm)
      (chartDomain f U (chartAt E x) (chartAt F (f x)))

omit [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace F] [ChartedSpace F N]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Transition maps between charts of the maximal atlas of a complex analytic manifold are
complex analytic. -/
theorem complexAnalyticOn_transition [ComplexAnalyticManifold E M]
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ (complexAnalyticGroupoid E).maximalAtlas M)
    (he' : e' ∈ (complexAnalyticGroupoid E).maximalAtlas M) :
    ComplexAnalyticOn (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h := ((complexAnalyticGroupoid E).compatible_of_mem_maximalAtlas he he').1
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h
  exact h

variable [ComplexAnalyticManifold E M] [ComplexAnalyticManifold F N]
  [ComplexAnalyticManifold G P]

/-- The local representatives of a complex analytic map in arbitrary charts of the maximal
atlases are complex analytic. -/
theorem ComplexAnalyticMOn.complexAnalyticOn_chart {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ComplexAnalyticMOn (E := E) (F := F) f U) {e : OpenPartialHomeomorph M E}
    (he : e ∈ (complexAnalyticGroupoid E).maximalAtlas M) {e' : OpenPartialHomeomorph N F}
    (he' : e' ∈ (complexAnalyticGroupoid F).maximalAtlas N) :
    ComplexAnalyticOn (e' ∘ f ∘ e.symm) (chartDomain f U e e') := by
  refine ComplexAnalyticOn.of_local (isOpen_chartDomain hU hf.1 e e') fun y hy ↦ ?_
  set p := e.symm y
  set c := chartAt E p
  set c' := chartAt F (f p)
  obtain ⟨W, V, hW, hV, hyW, hWD, hWτ, hVD, h1, h2, heq⟩ :=
    exists_chartChange hU hf.1 e c e' c' hy (mem_chart_source E p) (mem_chart_source F (f p))
  have hτ := (complexAnalyticOn_transition he
    ((complexAnalyticGroupoid E).chart_mem_maximalAtlas p)).mono
      (e.isOpen_inter_preimage_symm c.open_source) hW hWτ
  have hμ := (hf.2 p hy.2.1).mono (isOpen_chartDomain hU hf.1 _ _) hV hVD
  have hT : IsOpen (c'.target ∩ c'.symm ⁻¹' e'.source) :=
    c'.isOpen_inter_preimage_symm e'.open_source
  have hτ' := complexAnalyticOn_transition
    ((complexAnalyticGroupoid F).chart_mem_maximalAtlas (f p)) he'
  refine ⟨W, hW, hyW, ?_⟩
  rw [inter_eq_right.2 hWD]
  exact ((hτ'.comp hμ hV hT h2).comp hτ hW hV h1).congr hW heq.symm

/-- Compositions of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticMOn.comp {f : M → N} {g : N → P} {U : Set M} {V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hg : ComplexAnalyticMOn (E := F) (F := G) g V)
    (hf : ComplexAnalyticMOn (E := E) (F := F) f U) (hUV : MapsTo f U V) :
    ComplexAnalyticMOn (E := E) (F := G) (g ∘ f) U := by
  have hgf : ContinuousOn (g ∘ f) U := hg.1.comp hf.1 hUV
  refine ⟨hgf, fun x hx ↦ ?_⟩
  set c := chartAt E x
  set c'' := chartAt G (g (f x))
  have hD := isOpen_chartDomain hU hgf c c''
  refine ComplexAnalyticOn.of_local hD fun y hy ↦ ?_
  have hyU : c.symm y ∈ U := hy.2.1
  set d := chartAt F (f (c.symm y))
  set W := chartDomain f U c d ∩ chartDomain (g ∘ f) U c c''
  have hW : IsOpen W := (isOpen_chartDomain hU hf.1 c d).inter hD
  have hyW : y ∈ W := ⟨⟨hy.1, hyU, mem_chart_source F _⟩, hy⟩
  have hgd : ComplexAnalyticOn (c'' ∘ g ∘ d.symm) (chartDomain g V d c'') :=
    hg.complexAnalyticOn_chart hV ((complexAnalyticGroupoid F).chart_mem_maximalAtlas _)
      ((complexAnalyticGroupoid G).chart_mem_maximalAtlas _)
  have hfd : ComplexAnalyticOn (d ∘ f ∘ c.symm) W :=
    (hf.complexAnalyticOn_chart hU ((complexAnalyticGroupoid E).chart_mem_maximalAtlas x)
      ((complexAnalyticGroupoid F).chart_mem_maximalAtlas _)).mono
        (isOpen_chartDomain hU hf.1 c d) hW inter_subset_left
  have hmaps : MapsTo (d ∘ f ∘ c.symm) W (chartDomain g V d c'') := by
    rintro z ⟨⟨-, hzU, hzd⟩, -, -, hzg⟩
    refine ⟨d.map_source hzd, ?_, ?_⟩
    · simp only [Function.comp_apply, d.left_inv hzd]; exact hUV hzU
    · simp only [Function.comp_apply, mem_preimage, d.left_inv hzd]; exact hzg
  have hcomp := hgd.comp hfd hW (isOpen_chartDomain hV hg.1 d c'') hmaps
  refine ⟨W, hW, hyW, (hcomp.congr hW fun z hz ↦ ?_).mono hW (hD.inter hW) inter_subset_right⟩
  obtain ⟨⟨-, -, hzd⟩, -⟩ := hz
  simp only [Function.comp_apply, d.left_inv hzd]
  rfl

omit [ComplexAnalyticManifold E M] [ComplexAnalyticManifold F N]
  [ComplexAnalyticManifold G P] in
/-- **Complex analytic maps are real analytic** (GN, Proposition 2.2.11, globalized). -/
theorem ComplexAnalyticMOn.realAnalyticMOn {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ComplexAnalyticMOn (E := E) (F := F) f U) : RealAnalyticMOn (E := E) (F := F) f U :=
  ⟨hf.1, fun x hx ↦ (hf.2 x hx).realAnalyticOn (isOpen_chartDomain hU hf.1 _ _)⟩

omit [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F] [TopologicalSpace F]
  [ChartedSpace F N] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F]
  [T2Space F] [ComplexAnalyticManifold E M] [ComplexAnalyticManifold F N]
  [ComplexAnalyticManifold G P] in
/-- The identity is complex analytic. -/
theorem complexAnalyticMOn_id {U : Set M} (hU : IsOpen U) :
    ComplexAnalyticMOn (E := E) (F := E) (id : M → M) U := by
  refine ⟨continuousOn_id, fun x _ ↦ ?_⟩
  have hD := isOpen_chartDomain hU continuousOn_id (chartAt E x) (chartAt E x)
  refine ((ContinuousLinearMap.id ℂ E).complexAnalyticOn hD).congr hD fun z hz ↦ ?_
  exact (OpenPartialHomeomorph.right_inv _ hz.1).symm

omit [ComplexAnalyticManifold E M] [ComplexAnalyticManifold F N]
  [ComplexAnalyticManifold G P] in
/-- Constant maps are complex analytic. -/
theorem complexAnalyticMOn_const {U : Set M} (hU : IsOpen U) (n : N) :
    ComplexAnalyticMOn (E := E) (F := F) (fun _ : M ↦ n) U :=
  ⟨continuousOn_const, fun x _ ↦ complexAnalyticOn_const (chartAt F n n)
    (isOpen_chartDomain hU continuousOn_const (chartAt E x) (chartAt F n))⟩

omit [AddCommGroup G] [Module ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G] [TopologicalSpace G]
  [ChartedSpace G P] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G] [LocallyConvexSpace ℝ G]
  [T2Space G] [ComplexAnalyticManifold E M] [ComplexAnalyticManifold F N]
  [ComplexAnalyticManifold G P] in
/-- For maps between the model spaces, complex analytic maps in the sense of manifolds are the
complex analytic maps in the sense of `LocallyConvex.Analysis`. -/
theorem complexAnalyticMOn_iff_complexAnalyticOn {f : E → F} {U : Set E} (hU : IsOpen U) :
    ComplexAnalyticMOn (E := E) (F := F) f U ↔ ComplexAnalyticOn f U := by
  have hD : ∀ x : E, chartDomain f U (chartAt E x) (chartAt F (f x)) = U := fun x ↦ by
    simp [chartDomain]
  constructor
  · intro hf
    refine ComplexAnalyticOn.of_local hU fun x hx ↦ ⟨U, hU, hx, ?_⟩
    have := hf.2 x hx
    rw [hD] at this
    simpa using this
  · intro hf
    refine ⟨hf.1, fun x _ ↦ ?_⟩
    rw [hD]
    simpa using hf

end ComplexMaps

/-! ### Complexifications (GN, Definition 2.2.18) -/

section Complexification

open Complexification

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- `ι : M → M*` makes the complex analytic manifold `M*`, modeled on `E_ℂ`, a
**complexification** of the real analytic manifold `M`, modeled on `E` (Glöckner–Neeb,
Definition 2.2.18, where `M ⊆ M*`): `ι` is injective and each point of `M` lies in the domain of
a chart `ψ` of `M` which is the restriction of a chart `φ` of `M*`, in the sense that
`ψ.source = ι⁻¹(φ.source)`, `φ ∘ ι = ψ` (with `E ⊆ E_ℂ`) on `ψ.source`,
`ψ.target = E ∩ φ.target`, and `φ` maps the points of `ι(M)` in its domain exactly to the real
points `E ∩ φ.target`. -/
structure IsComplexification (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    (Mc : Type*) [TopologicalSpace Mc] [ChartedSpace (Complexification E) Mc] (ι : M → Mc) :
    Prop where
  injective : Function.Injective ι
  exists_chart : ∀ x : M, ∃ φ ∈ (complexAnalyticGroupoid (Complexification E)).maximalAtlas Mc,
    ∃ ψ ∈ (realAnalyticGroupoid E).maximalAtlas M, x ∈ ψ.source ∧ ψ.source = ι ⁻¹' φ.source ∧
      ψ.target = ofReal ⁻¹' φ.target ∧ (∀ y ∈ ψ.source, φ (ι y) = ofReal (ψ y)) ∧
      φ.source ∩ range ι = φ.source ∩ φ ⁻¹' range ofReal

/-- `E_ℂ` is a complexification of `E`. -/
theorem isComplexification_ofReal :
    IsComplexification E E (Complexification E) (ofReal : E → Complexification E) := by
  refine ⟨ofReal_injective, fun x ↦ ⟨OpenPartialHomeomorph.refl _, ?_,
    OpenPartialHomeomorph.refl _, ?_, by simp, by simp, by simp, fun y _ ↦ rfl, by simp⟩⟩
  · simpa using (complexAnalyticGroupoid (Complexification E)).chart_mem_maximalAtlas
      (M := Complexification E) (ofReal x)
  · simpa using (realAnalyticGroupoid E).chart_mem_maximalAtlas (M := E) x

end Complexification

/-! ### Example: inversion in a continuous inverse algebra -/

section InverseAlgebra

variable {A : Type u} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A]

/-- The unit group `A^×` of a real continuous inverse algebra is an open subset of `A`, hence a
real analytic manifold, and inversion `A^× → A^×` is real analytic (GN, Proposition 2.2.13). -/
theorem realAnalyticMOn_inverse :
    RealAnalyticMOn (E := A) (F := A) (Ring.inverse : A → A) {a : A | IsUnit a} :=
  (realAnalyticMOn_iff_realAnalyticOn ContinuousInverseAlgebra.isOpen_units).2
    realAnalyticOn_inverse

example (U : TopologicalSpace.Opens A) : RealAnalyticManifold A U := inferInstance

end InverseAlgebra

end LocallyConvex.Manifolds
