/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Connection

/-!
# Sprays

References: S. Lang, *Fundamentals of Differential Geometry*, §IV.3 and §VIII.2;
G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 6.

A spray (second order vector field) on `M` is given in each chart `i` of the atlas by its local
part `fᵢ(x, v)`: in the chart, the spray is `(x, v) ↦ (x, v; v, fᵢ(x, v))`. The local parts obey
the change of charts law
`fⱼ(τ x, dτₓ v) = dτₓ fᵢ(x, v) + d²τₓ(v, v)`, `τ = j ∘ i⁻¹`,
which is the change of charts law of the double tangent bundle restricted to the points
`(x, v; v, w)` (`Spray`). Geodesics are the curves with `α̈ = f(α, α̇)` in charts; their existence
is not assumed (it needs ODE theory, not available in locally convex spaces).

A spray is quadratic if `fᵢ(x, s v) = s² fᵢ(x, v)`. We show (Lang, Prop. IV.3.2 and §VIII.2):

* every connection induces a spray, `f(x, v) = Γₓ(v, v)` (`Connection.toSpray`), which is
  quadratic;
* conversely, a quadratic spray comes from a unique symmetric connection, with
  `Γₓ(a, b) = ½ d²(f(x, ·))₀(a, b)` (`Spray.toConnection`). The key facts are that a homogeneous
  map of degree 2 is the restriction to the diagonal of half its second derivative at `0`
  (`dMB_dMB_zero_of_homogeneous`), and the polarization of the change of charts law.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

section Calculus

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- A homogeneous map of degree 2 has derivative `2 s g(v)` at `s v` in the direction `v`. -/
theorem hasDirDerivAt_of_homogeneous {g : E → F} (hg : ∀ (s : ℝ) v, g (s • v) = s ^ 2 • g v)
    (s : ℝ) (v : E) : HasDirDerivAt g (s • v) v ((2 * s) • g v) := by
  have hl : Tendsto (fun t : ℝ ↦ (2 * s + t) • g v) (𝓝[≠] 0) (𝓝 ((2 * s) • g v)) := by
    have : Continuous fun t : ℝ ↦ (2 * s + t) • g v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  rw [← add_smul, hg, hg, ← sub_smul, smul_smul]
  congr 1
  field_simp
  ring

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **A homogeneous map of degree 2 is half its second derivative at `0` on the diagonal**:
`d²g₀(v, v) = 2 g(v)`. No regularity is needed for this identity. -/
theorem dMB_dMB_zero_of_homogeneous {g : E → F} (hg : ∀ (s : ℝ) v, g (s • v) = s ^ 2 • g v)
    (v : E) : dMB (dMB g) (((0 : E), v), (v, 0)) = (2 : ℝ) • g v := by
  have hd : ∀ s : ℝ, dMB g (s • v, v) = (2 * s) • g v := fun s ↦
    (hasDirDerivAt_of_homogeneous hg s v).dMB_eq
  have h : HasDirDerivAt (dMB g) ((0 : E), v) (v, 0) ((2 : ℝ) • g v) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, add_zero]
    rw [hd t, show (0 : E) = (0 : ℝ) • v by simp, hd 0]
    simp only [mul_zero, zero_smul, sub_zero, smul_smul]
    congr 1
    field_simp
  exact h.dMB_eq

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The second derivative `d²g_y(a, b) = d(dg(·) b)(y) a` of a `C^2` map is additive in `a`. -/
theorem dMB_dMB_add_left {g : E → F} {U : Set E} (hU : IsOpen U) (hg : ContDiffMBOn 2 g U)
    {y : E} (hy : y ∈ U) (a a' b : E) :
    dMB (dMB g) ((y, b), (a + a', 0)) =
      dMB (dMB g) ((y, b), (a, 0)) + dMB (dMB g) ((y, b), (a', 0)) := by
  have hdg : ContDiffMBOn 1 (dMB g) (U ×ˢ univ) := hg.2.2
  have hp : (y, b) ∈ U ×ˢ (univ : Set E) := ⟨hy, mem_univ b⟩
  have := hdg.dMB_add (hU.prod isOpen_univ) hp (a, 0) (a', 0)
  simpa using this

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem dMB_dMB_smul_left {g : E → F} {U : Set E} (hg : ContDiffMBOn 2 g U) {y : E}
    (hy : y ∈ U) (c : ℝ) (a b : E) :
    dMB (dMB g) ((y, b), (c • a, 0)) = c • dMB (dMB g) ((y, b), (a, 0)) := by
  have hdg : ContDiffMBOn 1 (dMB g) (U ×ˢ univ) := hg.2.2
  have hp : (y, b) ∈ U ×ˢ (univ : Set E) := ⟨hy, mem_univ b⟩
  have := hdg.dMB_smul hp c (a, 0)
  simpa using this

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The second derivative is additive in `b` (by symmetry). -/
theorem dMB_dMB_add_right {g : E → F} {U : Set E} (hU : IsOpen U) (hg : ContDiffMBOn 2 g U)
    {y : E} (hy : y ∈ U) (a b b' : E) :
    dMB (dMB g) ((y, b + b'), (a, 0)) =
      dMB (dMB g) ((y, b), (a, 0)) + dMB (dMB g) ((y, b'), (a, 0)) := by
  rw [hg.dMB_dMB_symm hU hy, dMB_dMB_add_left hU hg hy, hg.dMB_dMB_symm hU hy b,
    hg.dMB_dMB_symm hU hy b']

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem dMB_dMB_smul_right {g : E → F} {U : Set E} (hU : IsOpen U) (hg : ContDiffMBOn 2 g U)
    {y : E} (hy : y ∈ U) (c : ℝ) (a b : E) :
    dMB (dMB g) ((y, c • b), (a, 0)) = c • dMB (dMB g) ((y, b), (a, 0)) := by
  rw [hg.dMB_dMB_symm hU hy, dMB_dMB_smul_left hg hy, hg.dMB_dMB_symm hU hy b]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Polarization: for a symmetric bilinear `B`, `B(a+b, a+b) − B(a−b, a−b) = 4 B(a, b)`. -/
theorem polarization {B : E → E → F} (hadd : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (hsmul : ∀ (c : ℝ) a b, B (c • a) b = c • B a b) (hsym : ∀ a b, B a b = B b a) (a b : E) :
    B (a + b) (a + b) - B (a - b) (a - b) = (4 : ℝ) • B a b := by
  have hsub : ∀ a a' b, B (a - a') b = B a b - B a' b := fun a a' b ↦ by
    rw [sub_eq_add_neg, hadd, ← neg_one_smul ℝ a', hsmul, neg_one_smul, ← sub_eq_add_neg]
  have hadd' : ∀ a b b', B a (b + b') = B a b + B a b' := fun a b b' ↦ by
    rw [hsym, hadd, hsym b, hsym b']
  have hsub' : ∀ a b b', B a (b - b') = B a b - B a b' := fun a b b' ↦ by
    rw [hsym, hsub, hsym b, hsym b']
  rw [hadd, hadd', hadd', hsub, hsub', hsub', hsym b a]
  module

end Calculus

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E M) in
/-- A spray on `M`, by its local parts: in the chart `i`, the spray is
`(x, v) ↦ (x, v; v, fᵢ(x, v))`, and the local parts obey the change of charts law
`fⱼ(τ x, dτₓ v) = dτₓ fᵢ(x, v) + d²τₓ(v, v)`. -/
structure Spray where
  /-- The local part of the spray in the chart `i`. -/
  f : atlas E M → E → E → E
  smooth : ∀ i, SmoothMBOn (fun p : E × E ↦ f i p.1 p.2) (i.1.target ×ˢ univ)
  transition : ∀ i j : atlas E M, ∀ y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source, ∀ v,
    f j ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, v)) =
      dMB (j.1 ∘ i.1.symm) (y, f i y v) + dMB (dMB (j.1 ∘ i.1.symm)) ((y, v), (v, 0))

namespace Spray

/-- A spray is quadratic if its local parts are homogeneous of degree 2 in `v`. -/
def IsQuadratic (F : Spray E M) : Prop := ∀ i x (s : ℝ) v, F.f i x (s • v) = s ^ 2 • F.f i x v

variable (F : Spray E M)

omit [MBManifold E M] in
/-- In a chart, the local part of a spray is a `C^2` (indeed smooth) function of `v`. -/
theorem contDiffMBOn_f (i : atlas E M) {x : E} (hx : x ∈ i.1.target) (k : ℕ) :
    ContDiffMBOn k (F.f i x) univ := by
  have hpair : ContDiffMBOn k (fun v : E ↦ (x, v)) univ :=
    (contDiffMBOn_const k x univ).prodMk isOpen_univ
      ((ContinuousLinearMap.id ℝ E).contDiffMBOn k univ)
  exact ContDiffMBOn.comp (g := fun p : E × E ↦ F.f i p.1 p.2) (f := fun v : E ↦ (x, v))
    isOpen_univ (i.1.open_target.prod isOpen_univ) (F.smooth i k) hpair
    fun v _ ↦ ⟨hx, mem_univ v⟩

variable {F}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem f_zero (hF : F.IsQuadratic) (i : atlas E M) (x : E) : F.f i x 0 = 0 := by
  have := hF i x 0 0
  simpa using this

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem f_neg (hF : F.IsQuadratic) (i : atlas E M) (x v : E) : F.f i x (-v) = F.f i x v := by
  have := hF i x (-1) v
  simpa using this

open scoped Classical in
/-- The symbols of a quadratic spray, by polarization:
`Γₓ(a, b) = ¼ (f(x, a + b) − f(x, a − b))` (and `0` outside the chart). -/
def polar (F : Spray E M) (i : atlas E M) (x a b : E) : E :=
  if x ∈ i.1.target then (1 / 4 : ℝ) • (F.f i x (a + b) - F.f i x (a - b)) else 0

omit [MBManifold E M] in
/-- In a chart, the polarization of a quadratic spray is half the second derivative of its
local part at `0`, which is symmetric and bilinear. -/
theorem polar_eq (hF : F.IsQuadratic) (i : atlas E M) {x : E} (hx : x ∈ i.1.target) (a b : E) :
    polar F i x a b = (1 / 2 : ℝ) • dMB (dMB (F.f i x)) (((0 : E), b), (a, 0)) := by
  have hg := F.contDiffMBOn_f i hx 2
  set B : E → E → E := fun a b ↦ (1 / 2 : ℝ) • dMB (dMB (F.f i x)) (((0 : E), b), (a, 0))
  have hdiag : ∀ v, B v v = F.f i x v := fun v ↦ by
    simp only [B, dMB_dMB_zero_of_homogeneous (hF i x) v, smul_smul]
    norm_num
  have hadd : ∀ a a' b, B (a + a') b = B a b + B a' b := fun a a' b ↦ by
    simp only [B, dMB_dMB_add_left isOpen_univ hg (mem_univ 0), smul_add]
  have hsmul : ∀ (c : ℝ) a b, B (c • a) b = c • B a b := fun c a b ↦ by
    simp only [B, dMB_dMB_smul_left hg (mem_univ 0), smul_comm c]
  have hsym : ∀ a b, B a b = B b a := fun a b ↦ by
    simp only [B, hg.dMB_dMB_symm isOpen_univ (mem_univ 0) b a]
  have hpol := polarization hadd hsmul hsym a b
  rw [hdiag, hdiag] at hpol
  rw [polar, ite_eq_left hx, hpol, smul_smul]
  norm_num
  rfl

omit [MBManifold E M] in
theorem polar_add_left (hF : F.IsQuadratic) (i : atlas E M) (x a a' b : E) :
    polar F i x (a + a') b = polar F i x a b + polar F i x a' b := by
  by_cases hx : x ∈ i.1.target
  · rw [polar_eq hF i hx, polar_eq hF i hx, polar_eq hF i hx,
      dMB_dMB_add_left isOpen_univ (F.contDiffMBOn_f i hx 2) (mem_univ 0), smul_add]
  · simp [polar, hx]

omit [MBManifold E M] in
theorem polar_smul_left (hF : F.IsQuadratic) (i : atlas E M) (x : E) (c : ℝ) (a b : E) :
    polar F i x (c • a) b = c • polar F i x a b := by
  by_cases hx : x ∈ i.1.target
  · rw [polar_eq hF i hx, polar_eq hF i hx,
      dMB_dMB_smul_left (F.contDiffMBOn_f i hx 2) (mem_univ 0), smul_comm]
  · simp [polar, hx]

omit [MBManifold E M] in
theorem polar_add_right (hF : F.IsQuadratic) (i : atlas E M) (x a b b' : E) :
    polar F i x a (b + b') = polar F i x a b + polar F i x a b' := by
  by_cases hx : x ∈ i.1.target
  · rw [polar_eq hF i hx, polar_eq hF i hx, polar_eq hF i hx,
      dMB_dMB_add_right isOpen_univ (F.contDiffMBOn_f i hx 2) (mem_univ 0), smul_add]
  · simp [polar, hx]

omit [MBManifold E M] in
theorem polar_smul_right (hF : F.IsQuadratic) (i : atlas E M) (x : E) (c : ℝ) (a b : E) :
    polar F i x a (c • b) = c • polar F i x a b := by
  by_cases hx : x ∈ i.1.target
  · rw [polar_eq hF i hx, polar_eq hF i hx,
      dMB_dMB_smul_right isOpen_univ (F.contDiffMBOn_f i hx 2) (mem_univ 0), smul_comm]
  · simp [polar, hx]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem polar_symm (hF : F.IsQuadratic) (i : atlas E M) (x a b : E) :
    polar F i x a b = polar F i x b a := by
  by_cases hx : x ∈ i.1.target
  · simp only [polar, hx, ite_true]
    rw [add_comm b a, show b - a = -(a - b) by abel, f_neg hF]
  · simp [polar, hx]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The polarization recovers the spray on the diagonal: `Γₓ(v, v) = f(x, v)`. -/
theorem polar_self (hF : F.IsQuadratic) (i : atlas E M) {x : E} (hx : x ∈ i.1.target) (v : E) :
    polar F i x v v = F.f i x v := by
  simp only [polar, hx, ite_true, sub_self]
  rw [f_zero hF i x, show v + v = (2 : ℝ) • v by rw [two_smul], hF, sub_zero, smul_smul]
  norm_num

omit [MBManifold E M] in
theorem smoothMBOn_polar (i : atlas E M) :
    SmoothMBOn (fun p : E × (E × E) ↦ polar F i p.1 p.2.1 p.2.2) (i.1.target ×ˢ univ) := by
  intro k
  have hU : IsOpen (i.1.target ×ˢ (univ : Set (E × E))) := i.1.open_target.prod isOpen_univ
  have hV : IsOpen (i.1.target ×ˢ (univ : Set E)) := i.1.open_target.prod isOpen_univ
  have hfst : ContDiffMBOn k (ContinuousLinearMap.fst ℝ E (E × E)) (i.1.target ×ˢ univ) :=
    (ContinuousLinearMap.fst ℝ E (E × E)).contDiffMBOn k _
  have hplus : ContDiffMBOn k (fun p : E × (E × E) ↦ (p.1, p.2.1 + p.2.2)) (i.1.target ×ˢ univ) :=
    hfst.prodMk hU (((ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E).comp
      (ContinuousLinearMap.snd ℝ E (E × E))).contDiffMBOn k _)
  have hminus : ContDiffMBOn k (fun p : E × (E × E) ↦ (p.1, p.2.1 - p.2.2))
      (i.1.target ×ˢ univ) :=
    hfst.prodMk hU (((ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E).comp
      (ContinuousLinearMap.snd ℝ E (E × E))).contDiffMBOn k _)
  have h1 := ContDiffMBOn.comp (g := fun p : E × E ↦ F.f i p.1 p.2)
    (f := fun p : E × (E × E) ↦ (p.1, p.2.1 + p.2.2)) hU hV (F.smooth i k) hplus
    fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have h2 := ContDiffMBOn.comp (g := fun p : E × E ↦ F.f i p.1 p.2)
    (f := fun p : E × (E × E) ↦ (p.1, p.2.1 - p.2.2)) hU hV (F.smooth i k) hminus
    fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have h3 := ContDiffMBOn.comp (F₁ := E × E) hU isOpen_univ
    (((1 / 4 : ℝ) • (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)).contDiffMBOn
      k univ) (h1.prodMk hU h2) (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen hU (fun p hp ↦ ?_) h3
  simp only [Function.comp_apply, smul_apply, sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', polar, hp.1, ite_true]

/-- The polarization of a quadratic spray obeys the change of charts law of connections. -/
theorem polar_transition (i j : atlas E M) (y : E)
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (a b : E) :
    polar F j ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, a)) (dMB (j.1 ∘ i.1.symm) (y, b)) =
      dMB (j.1 ∘ i.1.symm) (y, polar F i y a b) +
        dMB (dMB (j.1 ∘ i.1.symm)) ((y, b), (a, 0)) := by
  set τ := j.1 ∘ i.1.symm
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hτ : ContDiffMBOn 2 τ T := smoothMBOn_transition' i j 2
  have hτy : τ y ∈ j.1.target := j.1.map_source hy.2
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT hy
  -- the second derivative of `τ` is symmetric and bilinear, so it polarizes
  set B : E → E → E := fun a b ↦ dMB (dMB τ) ((y, b), (a, 0))
  have hpolB := polarization (B := B) (fun a a' b ↦ dMB_dMB_add_left hT hτ hy a a' b)
    (fun c a b ↦ dMB_dMB_smul_left hτ hy c a b) (fun a b ↦ hτ.dMB_dMB_symm hT hy b a) a b
  have eplus : dMB τ (y, a) + dMB τ (y, b) = dMB τ (y, a + b) := by rw [← hL, ← hL, ← hL, map_add]
  have eminus : dMB τ (y, a) - dMB τ (y, b) = dMB τ (y, a - b) := by
    rw [← hL, ← hL, ← hL, map_sub]
  simp only [polar, hτy, hy.1, ite_true]
  rw [eplus, eminus, F.transition i j y hy (a + b), F.transition i j y hy (a - b)]
  have hτdef : (j.1 ∘ i.1.symm) = τ := rfl
  rw [hτdef]
  have hD : dMB (dMB τ) ((y, a + b), (a + b, 0)) =
      dMB (dMB τ) ((y, a - b), (a - b, 0)) + (4 : ℝ) • B a b := by
    rw [← hpolB]; abel
  rw [hD]
  simp only [← hL, map_smul, map_sub, B]
  module

end Spray

namespace Connection

variable (C : Connection E M)

/-- The spray of a connection: `f(x, v) = Γₓ(v, v)`. -/
def toSpray : Spray E M where
  f i x v := C.Γ i x v v
  smooth i k := by
    have hL : ContDiffMBOn k (fun p : E × E ↦ (p.1, (p.2, p.2))) (i.1.target ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k _).prodMk
        (i.1.open_target.prod isOpen_univ)
        (((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _).prodMk
          (i.1.open_target.prod isOpen_univ) ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _))
    exact ContDiffMBOn.comp (g := fun p : E × (E × E) ↦ C.Γ i p.1 p.2.1 p.2.2)
      (f := fun p : E × E ↦ (p.1, (p.2, p.2))) (i.1.open_target.prod isOpen_univ)
      (i.1.open_target.prod isOpen_univ) (C.smooth i k) hL fun p hp ↦ ⟨hp.1, mem_univ _⟩
  transition i j y hy v := C.transition i j y hy v v

omit [MBManifold E M] in
/-- The spray of a connection is quadratic. -/
theorem toSpray_isQuadratic : C.toSpray.IsQuadratic := fun i x s v ↦ by
  change C.Γ i x (s • v) (s • v) = s ^ 2 • C.Γ i x v v
  rw [C.smul_left, C.smul_right, smul_smul, sq]

end Connection

namespace Spray

variable {F : Spray E M}

/-- **The symmetric connection of a quadratic spray**, with symbols
`Γₓ(a, b) = ¼ (f(x, a + b) − f(x, a − b)) = ½ d²(f(x, ·))₀(a, b)`. -/
def toConnection (hF : F.IsQuadratic) : Connection E M where
  Γ := polar F
  smooth := smoothMBOn_polar
  add_left := polar_add_left hF
  smul_left := polar_smul_left hF
  add_right := polar_add_right hF
  smul_right := polar_smul_right hF
  transition := polar_transition

theorem toConnection_isSymmetric (hF : F.IsQuadratic) : (toConnection hF).IsSymmetric :=
  polar_symm hF

/-- The spray of the connection of a quadratic spray is the original spray (in each chart). -/
theorem toConnection_toSpray (hF : F.IsQuadratic) (i : atlas E M) {x : E}
    (hx : x ∈ i.1.target) (v : E) : (toConnection hF).toSpray.f i x v = F.f i x v :=
  polar_self hF i hx v

end Spray

end Manifold

end LocallyConvex.Manifolds
