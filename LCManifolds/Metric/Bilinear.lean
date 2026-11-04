/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Metric.Finsler

/-!
# Weak Riemannian, Lorentzian and pseudo-Riemannian metrics

References: A. Schmeding, *An Introduction to Infinite-Dimensional Differential Geometry*,
Cambridge University Press (2023), §4.1, Def. 4.1.1 (weak and strong Riemannian metrics);
S. Lang, *Fundamentals of Differential Geometry*, Ch. VII; J. Bognár, *Indefinite Inner Product
Spaces*, Springer (1974) (fundamental decompositions, Krein and Pontryagin spaces).

All the metrics of this file are fields of **symmetric bilinear forms** `g_x` on the tangent
spaces, smooth in charts (`SymmBilinField`). They are organized by their signature.

## Riemannian metrics

A **weak Riemannian metric** (`WeakRiemannianMetric`, Schmeding, Def. 4.1.1) is a field of
positive definite forms. "Weak" refers to the **topology of the fibers**: `g_x` is continuous
on `T_x M`, but the norm `√(g_x(v, v))` may induce a strictly coarser topology than the one of
the model. It is **strong** (`WeakRiemannianMetric.IsStrongAt`) when both topologies agree.
Strong Riemannian metrics force the model to be a pre-Hilbert space (normable, with a norm
coming from an inner product); following the convention of this library, it is a *Hilbert*
manifold only when the model is complete. On a Fréchet model that is not normable, such as
`C^∞_per`, every Riemannian metric is weak.

**Riemannian metrics are Finsler metrics.** `μ_x(v) = √(g_x(v, v))` is a reversible Finsler
norm, by the Cauchy–Schwarz inequality, and it is continuous on the whole tangent bundle
(`WeakRiemannianMetric.toFinslerMetric`). So lengths and distances of Riemannian metrics are
those of `LCManifolds.Metric.Finsler`.

## Fundamental decompositions and the index

For an indefinite form `B` on `E`, a **fundamental decomposition** (`FundamentalDecomposition`)
is a splitting `E = E₊ ⊕ E₋` by a continuous projection, `B`-orthogonal, with `B` positive
definite on `E₊` and negative definite on `E₋`. The **index** is the dimension of `E₋`.

* The index does not depend on the decomposition (`FundamentalDecomposition.rank_neg_eq`). This
  holds for the *algebraic* dimension and in complete generality: a negative definite subspace
  meets `E₊` only at `0`, so the projection onto `E₋` along `E₊` is injective on it.
* For a Krein space one usually measures `E₋` by its *Hilbert* dimension. For infinite index the
  two dimensions differ, and the invariance of the Hilbert dimension uses the completeness of
  `(E₊, B)` and `(E₋, -B)` (Bognár); it is not formalized here.

## Lorentzian and pseudo-Riemannian metrics

A **weak pseudo-Riemannian metric** (`WeakPseudoRiemannianMetric`) admits a fundamental
decomposition of each tangent space; it is then weakly nondegenerate
(`FundamentalDecomposition.nondegenerate`), and its index at `x` is well defined
(`WeakPseudoRiemannianMetric.index`). Its index may be any cardinal:

* index `0`: a weak Riemannian metric (`WeakRiemannianMetric.toWeakPseudoRiemannianMetric`);
* index `1`: a **weak Lorentzian metric** (`WeakLorentzianMetric`). Equivalently at each point,
  there is a timelike vector `v` (`g(v, v) < 0`) whose `g`-orthogonal is positive definite; the
  decomposition `E = ℝ v ⊕ v^⊥` is then automatically topological, with continuous projection
  `w ↦ w - g(w, v)/g(v, v) v` (`FundamentalDecomposition.ofTimelike`);
* finite index: the tangent spaces are of Pontryagin type;
* infinite index: of Krein type.

**Lorentzian and pseudo-Riemannian metrics are not Finsler metrics.** `g_x(v, v)` takes negative
values, so `√(g_x(v, v))` is not defined, and `√|g_x(v, v)|` is not subadditive. Their theory of
lengths (timelike curves, the reverse triangle inequality) is different and is not developed
here.

**Not formalized yet** (flagged as infinite dimensional subtleties): whether the index is locally
constant, whether fundamental decompositions can be chosen continuously in `x`, and the
Krein-space conditions (completeness of `(E₊, g)` and `(E₋, -g)`, topology given by the majorant
`g(P₊ ·, P₊ ·) - g(P₋ ·, P₋ ·)`).
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

/-! ### Linear algebra of a symmetric bilinear form -/

section LinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Cauchy–Schwarz** for a positive semidefinite symmetric bilinear form. -/
theorem BilinForm.sq_le_mul (B : LinearMap.BilinForm ℝ E) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (v w : E) : B v w ^ 2 ≤ B v v * B w w := by
  have h : ∀ t : ℝ, 0 ≤ B w w * (t * t) + (2 * B v w) * t + B v v := fun t ↦ by
    have := hpos (v + t • w)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm w v] at this
    linarith
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

/-- The triangle inequality for `√(B(v, v))`. -/
theorem BilinForm.sqrt_add_le (B : LinearMap.BilinForm ℝ E) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (v w : E) :
    √(B (v + w) (v + w)) ≤ √(B v v) + √(B w w) := by
  rw [Real.sqrt_le_left (by positivity)]
  have hcs := BilinForm.sq_le_mul B hsymm hpos v w
  have hvw : B v w ≤ √(B v v) * √(B w w) := by
    rw [← Real.sqrt_mul (hpos v)]
    exact Real.le_sqrt_of_sq_le hcs
  have e1 : B (v + w) (v + w) = B v v + 2 * B v w + B w w := by
    simp only [map_add, LinearMap.add_apply, hsymm w v]
    ring
  rw [e1, add_sq, Real.sq_sqrt (hpos v), Real.sq_sqrt (hpos w)]
  linarith

/-- A **fundamental decomposition** of a symmetric bilinear form `B` on a topological vector
space: `E = E₊ ⊕ E₋` with a continuous projection `P` onto `E₊` along `E₋`, `B`-orthogonal, with
`B` positive definite on `E₊` and negative definite on `E₋`. -/
structure FundamentalDecomposition [TopologicalSpace E] (B : LinearMap.BilinForm ℝ E) where
  /-- The positive part `E₊`. -/
  pos : Submodule ℝ E
  /-- The negative part `E₋`. -/
  neg : Submodule ℝ E
  /-- The continuous projection onto `E₊` along `E₋`. -/
  proj : E →L[ℝ] E
  proj_mem : ∀ v, proj v ∈ pos
  sub_proj_mem : ∀ v, v - proj v ∈ neg
  isCompl : IsCompl pos neg
  orth : ∀ a ∈ pos, ∀ b ∈ neg, B a b = 0
  pos_def : ∀ a ∈ pos, a ≠ 0 → 0 < B a a
  neg_def : ∀ b ∈ neg, b ≠ 0 → B b b < 0

namespace FundamentalDecomposition

variable [TopologicalSpace E] {B : LinearMap.BilinForm ℝ E}

/-- A negative definite subspace has dimension at most `dim E₋`: the projection onto `E₋` along
`E₊` is injective on it, since it meets `E₊` only at `0`. -/
theorem rank_le_rank_neg (D : FundamentalDecomposition B) (N : Submodule ℝ E)
    (hN : ∀ n ∈ N, n ≠ 0 → B n n < 0) : Module.rank ℝ N ≤ Module.rank ℝ D.neg := by
  let f : N →ₗ[ℝ] D.neg :=
    LinearMap.codRestrict D.neg
      ((LinearMap.id - D.proj.toLinearMap).domRestrict N) fun n ↦ D.sub_proj_mem n
  refine f.rank_le_of_injective fun n m hnm ↦ ?_
  have h : ((n : E) - m) - D.proj ((n : E) - m) = 0 := by
    have : (n : E) - D.proj n = (m : E) - D.proj m := congrArg Subtype.val hnm
    rw [map_sub]
    calc ((n : E) - m) - (D.proj n - D.proj m) = ((n : E) - D.proj n) - ((m : E) - D.proj m) := by
          abel
      _ = 0 := by rw [this, sub_self]
  have hpos : (n : E) - m ∈ D.pos := by
    rw [sub_eq_zero] at h
    rw [h]
    exact D.proj_mem _
  by_contra hne
  have hne' : (n : E) - m ≠ 0 := fun h0 ↦ hne (Subtype.ext (sub_eq_zero.mp h0))
  have h1 := D.pos_def _ hpos hne'
  have h2 := hN _ (N.sub_mem n.2 m.2) hne'
  linarith

/-- **The index is well defined**: two fundamental decompositions have negative parts of the same
(algebraic) dimension. No completeness is needed. -/
theorem rank_neg_eq (D D' : FundamentalDecomposition B) :
    Module.rank ℝ D.neg = Module.rank ℝ D'.neg :=
  le_antisymm (D'.rank_le_rank_neg D.neg D.neg_def) (D.rank_le_rank_neg D'.neg D'.neg_def)

/-- A form with a fundamental decomposition is **weakly nondegenerate**: `B(v, ·) = 0` forces
`v = 0`. -/
theorem nondegenerate (D : FundamentalDecomposition B) (hsymm : ∀ v w, B v w = B w v) {v : E}
    (hv : ∀ w, B v w = 0) : v = 0 := by
  set a := D.proj v
  set b := v - D.proj v
  have ha : a ∈ D.pos := D.proj_mem v
  have hb : b ∈ D.neg := D.sub_proj_mem v
  have hvab : v = a + b := by simp [a, b]
  have hBa : B a a = 0 := by
    have := hv a
    rw [hvab, map_add, LinearMap.add_apply, hsymm b a, D.orth a ha b hb, add_zero] at this
    exact this
  have hBb : B b b = 0 := by
    have := hv b
    rw [hvab, map_add, LinearMap.add_apply, D.orth a ha b hb, zero_add] at this
    exact this
  have ha0 : a = 0 := by
    by_contra h
    exact (D.pos_def a ha h).ne' hBa
  have hb0 : b = 0 := by
    by_contra h
    exact (D.neg_def b hb h).ne hBb
  rw [hvab, ha0, hb0, add_zero]

/-- The trivial decomposition `E₊ = E`, `E₋ = 0` of a positive definite form (index `0`). -/
def ofPosDef (hpos : ∀ v, v ≠ 0 → 0 < B v v) : FundamentalDecomposition B where
  pos := ⊤
  neg := ⊥
  proj := ContinuousLinearMap.id ℝ E
  proj_mem _ := Submodule.mem_top
  sub_proj_mem v := by simp
  isCompl := isCompl_top_bot
  orth a _ b hb := by
    rw [Submodule.mem_bot] at hb
    simp [hb]
  pos_def a _ ha := hpos a ha
  neg_def b hb hb0 := absurd ((Submodule.mem_bot ℝ).mp hb) hb0

theorem rank_neg_ofPosDef (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    Module.rank ℝ (ofPosDef hpos).neg = 0 :=
  rank_bot ℝ E

section Timelike

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **The Lorentzian decomposition.** If `v` is timelike (`B(v, v) < 0`) and `B` is positive
definite on the `B`-orthogonal of `v`, then `E = v^⊥ ⊕ ℝ v` is a fundamental decomposition. The
projection `w ↦ w - B(w, v)/B(v, v) v` is continuous as soon as `B(v, ·)` is, so the
decomposition is automatically topological. -/
def ofTimelike (hsymm : ∀ v w, B v w = B w v) {v : E} (hv : B v v < 0)
    (hcont : Continuous fun w ↦ B v w) (hpos : ∀ w, B v w = 0 → w ≠ 0 → 0 < B w w) :
    FundamentalDecomposition B where
  pos := LinearMap.ker (B v)
  neg := ℝ ∙ v
  proj := ContinuousLinearMap.id ℝ E -
    (⟨B v, hcont⟩ : E →L[ℝ] ℝ).smulRight ((B v v)⁻¹ • v)
  proj_mem w := by
    have hv0 : B v v ≠ 0 := hv.ne
    rw [LinearMap.mem_ker]
    change B v (w - B v w • ((B v v)⁻¹ • v)) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  sub_proj_mem w := by
    change w - (w - B v w • ((B v v)⁻¹ • v)) ∈ ℝ ∙ v
    rw [sub_sub_cancel, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  isCompl := by
    have hv0 : B v v ≠ 0 := hv.ne
    constructor
    · rw [Submodule.disjoint_def]
      intro w hw hw'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
      rw [LinearMap.mem_ker, map_smul, smul_eq_mul] at hw
      have hc : c = 0 := by
        rcases mul_eq_zero.mp hw with h | h
        · exact h
        · exact absurd h hv0
      simp [hc]
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      have hw : w = (w - (B v w / B v v) • v) + (B v w / B v v) • v := by abel
      rw [hw]
      refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
  orth a ha b hb := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [LinearMap.mem_ker] at ha
    rw [map_smul, smul_eq_mul, hsymm a v, ha, mul_zero]
  pos_def a ha ha0 := hpos a (LinearMap.mem_ker.mp ha) ha0
  neg_def b hb hb0 := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hc : c ≠ 0 := by
      rintro rfl
      simp at hb0
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have : 0 < c * c := mul_self_pos.mpr hc
    nlinarith

/-- The Lorentzian decomposition has index `1`. -/
theorem rank_neg_ofTimelike (hsymm : ∀ v w, B v w = B w v) {v : E} (hv : B v v < 0)
    (hcont : Continuous fun w ↦ B v w) (hpos : ∀ w, B v w = 0 → w ≠ 0 → 0 < B w w) :
    Module.rank ℝ (ofTimelike hsymm hv hcont hpos).neg = 1 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  change Module.rank ℝ (ℝ ∙ v) = 1
  rw [← Module.finrank_eq_rank, finrank_span_singleton hv0, Nat.cast_one]

end Timelike

end FundamentalDecomposition

end LinearAlgebra

/-! ### Symmetric bilinear fields on a manifold -/

section Manifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E) in
/-- The preferred chart at `x`, as an element of the atlas. Tangent vectors at `x` are stored in
its coordinates. -/
def prefAtlas (x : M) : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩

/-- The local representative of a field of bilinear forms in the chart `i`:
`(y, a, b) ↦ g_x(a, b)` with `x = i⁻¹ y` and `a, b` read in the chart `i`. -/
def bilinLocalRep (g : M → LinearMap.BilinForm ℝ E) (i : atlas E M) (q : E × E × E) : ℝ :=
  g (i.1.symm q.1)
    (tangentCoordChange i (prefAtlas E (i.1.symm q.1)) (i.1.symm q.1) q.2.1)
    (tangentCoordChange i (prefAtlas E (i.1.symm q.1)) (i.1.symm q.1) q.2.2)

variable (E M) in
/-- A **smooth field of symmetric bilinear forms** `g_x` on the tangent spaces: smooth means that
the local representatives `(y, a, b) ↦ g_{i⁻¹ y}(a, b)` are smooth. -/
structure SymmBilinField where
  /-- The form `g_x` on `T_x M`, in the coordinates of the preferred chart at `x`. -/
  toFun : M → LinearMap.BilinForm ℝ E
  symm' : ∀ x v w, toFun x v w = toFun x w v
  smooth' : ∀ i : atlas E M, SmoothMBOn (bilinLocalRep toFun i) (i.1.target ×ˢ univ)

namespace SymmBilinField

variable (g : SymmBilinField E M)

omit [LocallyConvexSpace ℝ E] [MBManifold E M] in
/-- In the preferred chart at `x`, the local representative at `x` is `g_x` itself. -/
theorem bilinLocalRep_pref (x : M) (v w : E) :
    bilinLocalRep g.toFun (prefAtlas E x) (chartAt E x x, v, w) = g.toFun x v w := by
  have hx : (chartAt E x).symm (chartAt E x x) = x := (chartAt E x).left_inv (mem_chart_source E x)
  simp only [bilinLocalRep, prefAtlas, hx]
  rw [tangentCoordChange_self _ (mem_chart_source E x), tangentCoordChange_self _
    (mem_chart_source E x)]

omit [LocallyConvexSpace ℝ E] [MBManifold E M] in
/-- Each `g_x` is jointly continuous on `T_x M × T_x M`. -/
theorem continuous_fiber (x : M) : Continuous fun p : E × E ↦ g.toFun x p.1 p.2 := by
  have h := (g.smooth' (prefAtlas E x) 0).continuousOn
  have hmaps : MapsTo (fun p : E × E ↦ (chartAt E x x, p.1, p.2)) univ
      ((prefAtlas E x).1.target ×ˢ univ) := fun _ _ ↦
    ⟨(chartAt E x).map_source (mem_chart_source E x), mem_univ _⟩
  have hc := h.comp_continuous (by fun_prop) fun p ↦ hmaps (mem_univ p)
  refine hc.congr fun p ↦ ?_
  exact g.bilinLocalRep_pref x p.1 p.2

/-- **The quadratic form `v ↦ g_x(v, v)` is continuous on the tangent bundle.** In the chart of
`TM` over a chart `i`, it is the local representative evaluated at `(y, a, a)`. -/
theorem continuous_quadratic :
    Continuous fun p : TangentBundle E M ↦ g.toFun p.proj p.2 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := prefAtlas E p.proj
  set Ψ := tangentChart i i.1
  have hpS : p ∈ Ψ.source := (mem_tangentChart_source i i.1 p).mpr
    ⟨mem_chart_source E _, mem_chart_source E _⟩
  have hrep : ∀ q ∈ Ψ.source, g.toFun q.proj q.2 q.2 =
      bilinLocalRep g.toFun i ((Ψ q).1, (Ψ q).2, (Ψ q).2) := by
    intro q hq
    have hq' := ((mem_tangentChart_source i i.1 q).mp hq).1
    have h1 : (Ψ q).1 = i.1 q.proj := rfl
    have h2 : (Ψ q).2 = tangentCoordChange (prefAtlas E q.proj) i q.proj q.2 := rfl
    have hsymm : i.1.symm (i.1 q.proj) = q.proj := i.1.left_inv hq'
    have hcc : tangentCoordChange i (prefAtlas E q.proj) q.proj
        (tangentCoordChange (prefAtlas E q.proj) i q.proj q.2) = q.2 := by
      exact (tangentCoordChange_comp (prefAtlas E q.proj) i (prefAtlas E q.proj)
        ⟨⟨mem_chart_source E q.proj, hq'⟩, mem_chart_source E q.proj⟩ (show E from q.2)).trans
        (tangentCoordChange_self _ (mem_chart_source E q.proj) _)
    simp only [bilinLocalRep, h1, h2, hsymm, hcc]
  have hev : (fun q : TangentBundle E M ↦ g.toFun q.proj q.2 q.2) =ᶠ[𝓝 p]
      (bilinLocalRep g.toFun i ∘ fun r : E × E ↦ (r.1, r.2, r.2)) ∘ Ψ :=
    Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hpS) hrep
  refine ContinuousAt.congr ?_ hev.symm
  have hcont := (g.smooth' i 0).continuousOn
  have hΨ : ContinuousAt Ψ p := Ψ.continuousAt hpS
  have hmem : (fun r : E × E ↦ (r.1, r.2, r.2)) (Ψ p) ∈ i.1.target ×ˢ (univ : Set (E × E)) :=
    ⟨i.1.map_source (mem_chart_source E _), mem_univ _⟩
  have hopen : IsOpen (i.1.target ×ˢ (univ : Set (E × E))) := i.1.open_target.prod isOpen_univ
  have hdiag : Continuous fun r : E × E ↦ (r.1, r.2, r.2) := by fun_prop
  have h3 : ContinuousAt (bilinLocalRep g.toFun i) ((fun r : E × E ↦ (r.1, r.2, r.2)) (Ψ p)) :=
    hcont.continuousAt (hopen.mem_nhds hmem)
  exact ContinuousAt.comp (ContinuousAt.comp (f := fun r : E × E ↦ (r.1, r.2, r.2)) h3
    hdiag.continuousAt) hΨ

/-- `g` is **weakly nondegenerate** at every point: `g_x(v, ·) = 0` forces `v = 0`. -/
def IsWeaklyNondegenerate : Prop := ∀ x v, (∀ w, g.toFun x v w = 0) → v = 0

end SymmBilinField

/-! ### Riemannian metrics -/

variable (E M) in
/-- A **weak Riemannian metric** (Schmeding, Def. 4.1.1): a smooth field of positive definite
symmetric bilinear forms. "Weak": the norm `√(g_x(v, v))` need not induce the topology of the
model; see `WeakRiemannianMetric.IsStrongAt`. -/
structure WeakRiemannianMetric extends SymmBilinField E M where
  pos_def' : ∀ x v, v ≠ 0 → 0 < toFun x v v

namespace WeakRiemannianMetric

variable (g : WeakRiemannianMetric E M)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem nonneg (x : M) (v : E) : 0 ≤ g.toFun x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos_def' x v hv).le

/-- `g` is **strong** at `x` (Schmeding, Def. 4.1.1(c)) if the sets `{v | g_x(v, v) < ε}` form a
basis of neighborhoods of `0` in `T_x M`: the norm of `g_x` induces the topology of the model.
This forces the model to be a pre-Hilbert space. -/
def IsStrongAt (x : M) : Prop :=
  (𝓝 (0 : E)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {v | g.toFun x v v < ε}

/-- **A weak Riemannian metric is a Finsler metric**: `μ_x(v) = √(g_x(v, v))` is a reversible
Finsler norm, continuous on the tangent bundle. -/
def toFinslerMetric : FinslerMetric E M where
  toFun p := √(g.toFun p.proj p.2 p.2)
  nonneg' _ := Real.sqrt_nonneg _
  add_le' x v w := BilinForm.sqrt_add_le (g.toFun x) (g.symm' x) (g.nonneg x) v w
  smul_eq' x c hc v := by
    change √(g.toFun x (c • v) (c • v)) = c * √(g.toFun x v v)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self hc]
  continuous_fiber' x :=
    Real.continuous_sqrt.comp ((g.continuous_fiber x).comp (by fun_prop :
      Continuous fun v : E ↦ (v, v)))
  continuous' := Real.continuous_sqrt.comp g.continuous_quadratic

theorem toFinslerMetric_apply (x : M) (v : E) :
    g.toFinslerMetric.toFun ⟨x, v⟩ = √(g.toFun x v v) := rfl

theorem toFinslerMetric_isNondegenerate :
    g.toFinslerMetric.toFinslerSeminormField.IsNondegenerate := by
  intro x v hv
  change √(g.toFun x v v) = 0 at hv
  by_contra h
  exact (Real.sqrt_pos.mpr (g.pos_def' x v h)).ne' hv

theorem toFinslerMetric_isReversible :
    g.toFinslerMetric.toFinslerSeminormField.IsReversible := by
  intro x v
  change √(g.toFun x (-v) (-v)) = √(g.toFun x v v)
  simp

end WeakRiemannianMetric

/-! ### Pseudo-Riemannian and Lorentzian metrics -/

variable (E M) in
/-- A **weak pseudo-Riemannian metric**: a smooth field of symmetric bilinear forms admitting a
fundamental decomposition `T_x M = E₊ ⊕ E₋` at each point. The index `dim E₋` may be any
cardinal; "weak" again refers to the topology of the fibers. -/
structure WeakPseudoRiemannianMetric extends SymmBilinField E M where
  decomposition' : ∀ x, Nonempty (FundamentalDecomposition (toFun x))

namespace WeakPseudoRiemannianMetric

variable (g : WeakPseudoRiemannianMetric E M)

/-- The **index** of `g` at `x`: the dimension of the negative part of any fundamental
decomposition (it does not depend on the choice, `FundamentalDecomposition.rank_neg_eq`). -/
def index (x : M) : Cardinal := Module.rank ℝ (g.decomposition' x).some.neg

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem index_eq (x : M) (D : FundamentalDecomposition (g.toFun x)) :
    g.index x = Module.rank ℝ D.neg :=
  (g.decomposition' x).some.rank_neg_eq D

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- A weak pseudo-Riemannian metric is weakly nondegenerate. -/
theorem isWeaklyNondegenerate : g.toSymmBilinField.IsWeaklyNondegenerate :=
  fun x _ hv ↦ (g.decomposition' x).some.nondegenerate (g.symm' x) hv

end WeakPseudoRiemannianMetric

/-- A weak Riemannian metric is a weak pseudo-Riemannian metric of index `0`. -/
def WeakRiemannianMetric.toWeakPseudoRiemannianMetric (g : WeakRiemannianMetric E M) :
    WeakPseudoRiemannianMetric E M where
  toSymmBilinField := g.toSymmBilinField
  decomposition' x := ⟨FundamentalDecomposition.ofPosDef (g.pos_def' x)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem WeakRiemannianMetric.index_eq_zero (g : WeakRiemannianMetric E M) (x : M) :
    g.toWeakPseudoRiemannianMetric.index x = 0 := by
  rw [WeakPseudoRiemannianMetric.index_eq _ x (FundamentalDecomposition.ofPosDef (g.pos_def' x))]
  exact FundamentalDecomposition.rank_neg_ofPosDef _

variable (E M) in
/-- A **weak Lorentzian metric**: a weak pseudo-Riemannian metric of index `1` at every point. -/
structure WeakLorentzianMetric extends WeakPseudoRiemannianMetric E M where
  index_eq_one' : ∀ x, toWeakPseudoRiemannianMetric.index x = 1

/-- **Lorentzian metrics from timelike vectors.** A smooth field of symmetric bilinear forms such
that each `T_x M` contains a timelike vector `v` (`g_x(v, v) < 0`) with positive definite
`g_x`-orthogonal is a weak Lorentzian metric: the decomposition `ℝ v ⊕ v^⊥` is topological
(`FundamentalDecomposition.ofTimelike`). -/
def SymmBilinField.toWeakLorentzianMetric (g : SymmBilinField E M)
    (htime : ∀ x, ∃ v, g.toFun x v v < 0 ∧
      ∀ w, g.toFun x v w = 0 → w ≠ 0 → 0 < g.toFun x w w) :
    WeakLorentzianMetric E M where
  toSymmBilinField := g
  decomposition' x := by
    obtain ⟨v, hv, hpos⟩ := htime x
    have hcont : Continuous fun w ↦ g.toFun x v w :=
      (g.continuous_fiber x).comp (by fun_prop : Continuous fun w : E ↦ (v, w))
    exact ⟨FundamentalDecomposition.ofTimelike (g.symm' x) hv hcont hpos⟩
  index_eq_one' x := by
    obtain ⟨v, hv, hpos⟩ := htime x
    have hcont : Continuous fun w ↦ g.toFun x v w :=
      (g.continuous_fiber x).comp (by fun_prop : Continuous fun w : E ↦ (v, w))
    rw [WeakPseudoRiemannianMetric.index_eq _ x
      (FundamentalDecomposition.ofTimelike (g.symm' x) hv hcont hpos)]
    exact FundamentalDecomposition.rank_neg_ofTimelike _ _ _ _

end Manifold

end LCManifolds
