/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.ContMDiff

/-!
# Products of manifolds

If `M` and `N` are manifolds modeled on `E` and `F`, then `M × N` is a manifold modeled on
`E × F` (`Prod.mbManifold`), with the product charts of Mathlib's `prodChartedSpace`: the
transition maps are products of transition maps. The projections are smooth
(`smoothMBM_fst`, `smoothMBM_snd`).

The model space is Mathlib's `ModelProd E F`, a type synonym of `E × F` used to avoid instance
diamonds when `M` or `N` is itself a product.
-/

open Set
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

section ModelProd

variable (A B : Type*) [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
  [AddCommGroup B] [Module ℝ B] [TopologicalSpace B]

instance : AddCommGroup (ModelProd A B) := inferInstanceAs (AddCommGroup (A × B))

instance : Module ℝ (ModelProd A B) := inferInstanceAs (Module ℝ (A × B))

instance [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] :
    IsTopologicalAddGroup (ModelProd A B) :=
  inferInstanceAs (IsTopologicalAddGroup (A × B))

instance [ContinuousSMul ℝ A] [ContinuousSMul ℝ B] : ContinuousSMul ℝ (ModelProd A B) :=
  inferInstanceAs (ContinuousSMul ℝ (A × B))

instance [LocallyConvexSpace ℝ A] [LocallyConvexSpace ℝ B] :
    LocallyConvexSpace ℝ (ModelProd A B) :=
  inferInstanceAs (LocallyConvexSpace ℝ (A × B))

instance [T2Space A] [T2Space B] : T2Space (ModelProd A B) :=
  inferInstanceAs (T2Space (A × B))

end ModelProd

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- Products of smooth maps are smooth. -/
theorem SmoothMBOn.prodMap {g : E → E} {h : F → F} {U : Set E} {V : Set F} (hU : IsOpen U)
    (hV : IsOpen V) (hg : SmoothMBOn g U) (hh : SmoothMBOn h V) :
    SmoothMBOn (fun p : E × F ↦ (g p.1, h p.2)) (U ×ˢ V) := by
  intro k
  have hUV : IsOpen (U ×ˢ V) := hU.prod hV
  have h1 : ContDiffMBOn k (g ∘ ContinuousLinearMap.fst ℝ E F) (U ×ˢ V) :=
    (hg k).comp hUV hU ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn k _) fun p hp ↦ hp.1
  have h2 : ContDiffMBOn k (h ∘ ContinuousLinearMap.snd ℝ E F) (U ×ˢ V) :=
    (hh k).comp hUV hV ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn k _) fun p hp ↦ hp.2
  exact h1.prodMk hUV h2

/-- The product of two smooth diffeomorphisms between open sets is one. -/
theorem prod_mem_mbGroupoid {g : OpenPartialHomeomorph E E} {h : OpenPartialHomeomorph F F}
    (hg : g ∈ mbGroupoid E) (hh : h ∈ mbGroupoid F) :
    g.prod h ∈ mbGroupoid (ModelProd E F) :=
  ⟨SmoothMBOn.prodMap g.open_source h.open_source hg.1 hh.1,
    SmoothMBOn.prodMap g.open_target h.open_target hg.2 hh.2⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

/-- The product of two manifolds is a manifold. -/
instance Prod.mbManifold : MBManifold (ModelProd E F) (M × N) where
  compatible := by
    rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
    rw [OpenPartialHomeomorph.prod_symm_trans_prod]
    exact prod_mem_mbGroupoid (HasGroupoid.compatible he he') (HasGroupoid.compatible hf hf')

omit [MBManifold E M] [MBManifold F N] in
/-- The first projection `M × N → M` is smooth. -/
theorem smoothMBM_fst : SmoothMBM (ModelProd E F) E (Prod.fst : M × N → M) := by
  intro k
  refine ⟨continuous_fst.continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E x.1
  set d := chartAt F x.2
  have hD : chartDomain Prod.fst univ (chartAt (ModelProd E F) x) c ⊆ c.target ×ˢ d.target :=
    fun y hy ↦ hy.1
  refine ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain isOpen_univ continuous_fst.continuousOn _ _) (fun y hy ↦ ?_)
    (((ContinuousLinearMap.fst ℝ E F).contDiffMBOn k univ).mono (subset_univ _))
  change y.1 = c (c.symm y.1)
  rw [c.right_inv (hD hy).1]

omit [MBManifold E M] [MBManifold F N] in
/-- The second projection `M × N → N` is smooth. -/
theorem smoothMBM_snd : SmoothMBM (ModelProd E F) F (Prod.snd : M × N → N) := by
  intro k
  refine ⟨continuous_snd.continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E x.1
  set d := chartAt F x.2
  have hD : chartDomain Prod.snd univ (chartAt (ModelProd E F) x) d ⊆ c.target ×ˢ d.target :=
    fun y hy ↦ hy.1
  refine ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain isOpen_univ continuous_snd.continuousOn _ _) (fun y hy ↦ ?_)
    (((ContinuousLinearMap.snd ℝ E F).contDiffMBOn k univ).mono (subset_univ _))
  change y.2 = d (d.symm y.2)
  rw [d.right_inv (hD hy).2]

omit [MBManifold E M] [MBManifold F N] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- A pair of `C^k` maps into `M` and `N` is a `C^k` map into `M × N`. -/
theorem ContMDiffMBOn.prodMk {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {k : ℕ} {f : P → M} {g : P → N}
    {U : Set P} (hU : IsOpen U) (hf : ContMDiffMBOn (E := G) (F := E) k f U)
    (hg : ContMDiffMBOn (E := G) (F := F) k g U) :
    ContMDiffMBOn (E := G) (F := ModelProd E F) k (fun p ↦ (f p, g p)) U := by
  have hfg : ContinuousOn (fun p ↦ (f p, g p)) U := hf.1.prodMk hg.1
  refine ⟨hfg, fun x hx ↦ ?_⟩
  have hD : chartDomain (fun p ↦ (f p, g p)) U (chartAt G x) (chartAt (ModelProd E F) (f x, g x))
      ⊆ chartDomain f U (chartAt G x) (chartAt E (f x)) ∩
        chartDomain g U (chartAt G x) (chartAt F (g x)) :=
    fun y hy ↦ ⟨⟨hy.1, hy.2.1, hy.2.2.1⟩, ⟨hy.1, hy.2.1, hy.2.2.2⟩⟩
  have hopen := (isOpen_chartDomain hU hf.1 (chartAt G x) (chartAt E (f x))).inter
    (isOpen_chartDomain hU hg.1 (chartAt G x) (chartAt F (g x)))
  exact (((hf.2 x hx).mono inter_subset_left).prodMk hopen
    ((hg.2 x hx).mono inter_subset_right)).mono hD

end LocallyConvex.Manifolds
