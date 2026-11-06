/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.CovariantCurve

/-!
# Finsler metrics and Finsler length structures

References: G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their
homogeneous spaces*, Forum Math. 31 (2019), Def. 2.2, 2.3, 2.6, 2.7 and Lemma 3.19;
R. S. Palais, *Lusternik–Schnirelman theory on Banach manifolds*, Topology 5 (1966), §2,
Def. 2.1 and 2.6; D. Burago, Y. Burago, S. Ivanov, *A Course in Metric Geometry*, AMS (2001)
(§2.1.1, definition of length structures).

## Terminology: two continuity conditions, two names

Let `M` be a manifold modeled on a locally convex space `E`, in the Michal–Bastiani setting, so
that the tangent bundle `TM` is a topological space. The objects of this file are, from the
most general to the most specific:

* A **Finsler seminorm** on `E` (`FinslerSeminorm`, Larotonda Def. 2.2): a continuous function
  `E → ℝ≥0` that is subadditive and *positively* homogeneous, `μ (c • v) = c * μ v` for
  `c ≥ 0`. It need not be symmetric (`μ (-v) ≠ μ v` is allowed) nor definite.
* A **field of Finsler seminorms** (`FinslerSeminormField`): a Finsler seminorm `μ_p` on each
  tangent space `T_p M`. **Nothing is assumed about how `μ_p` depends on `p`.**
* A **Finsler metric** (`FinslerMetric`, Larotonda Def. 2.3(2)): a field of Finsler seminorms
  such that `μ : TM → ℝ` is **continuous on the tangent bundle**. This is the notion meant by
  "Finsler metric" without further qualification, here and in the literature.
* A **Finsler length structure** (`FinslerLengthStructure`, Larotonda Def. 2.3(1), there called
  "continuous along paths"): a field of Finsler seminorms such that `t ↦ μ (γ̇ t)` is
  **continuous along every `C¹` curve `γ`**, and nothing more. It is exactly what is needed to
  measure lengths of curves, hence the name (compare the length structures of
  Burago–Burago–Ivanov, §2.1.1).

Every Finsler metric is a Finsler length structure (`FinslerMetric.toFinslerLengthStructure`):
the velocity of a `C¹` curve is a continuous curve in `TM` (`continuous_velocity`). The converse
fails, and the weaker notion is not a technical convenience: the quotient metric on a
homogeneous space `G/K` is always a Finsler length structure, but it is a Finsler metric only
when `π_* : TG → T(G/K)` is a quotient map (Larotonda, Lemma 3.19). In infinite dimensions,
paths lift along `π` but neighborhoods need not.

**Rule of use.** Lengths and distances are defined for Finsler length structures
(`FinslerLengthStructure.length`, `FinslerLengthStructure.dist`), so that they apply to quotient
metrics; statements that compare the topologies of `M` and of the distance use Finsler metrics.
Every statement in this file says which of the two it assumes.

**Two words we avoid.** We do not say *weak* Finsler metric: "weak" refers to the topology of
the fibers (a weak Riemannian metric does not induce the topology of the model), not to the
continuity in `TM`. We do not say *Finsler structure* alone: Palais uses it for the much stronger
notion in which every `μ_p` is a norm inducing the topology of the fiber, locally uniformly
equivalent to `μ_{p₀}` (Palais, Def. 2.1 and 2.6). That notion only makes sense for normable
models; it is not formalized here.

**Variants** (Larotonda, Def. 2.2): `FinslerSeminormField.IsNondegenerate` (each `μ_p` is a
Finsler *norm*: `μ_p v = 0 → v = 0`) and `FinslerSeminormField.IsReversible` (`μ_p (-v) = μ_p v`).

## Curves

Curves are `C¹` maps `ℝ → M` (`IsCkCurve E 1`), restricted to an interval `[a, b]` when their
length is measured. As in Larotonda, the distance is taken over **piecewise `C¹` paths**, encoded
as chains of `C¹` arcs (`FinslerLengthStructure.Reach`): an arc `γ|[a, b]` followed by a chain
from `γ b`. Concatenation of chains is then immediate (`Reach.trans`), and so is the **triangle
inequality** (`FinslerLengthStructure.dist_triangle`); no smoothing at the junctions is needed.
Reversing a curve (`isCkCurve_reverse`, `velocity_reverse`) preserves lengths when `μ` is
reversible, and then the distance is symmetric (`FinslerLengthStructure.dist_comm`). With a
reversibility constant, `μ_x(-v) ≤ λ μ_x(v)`, the asymmetry of the distance is bounded,
`d_b(y, x) ≤ λ d_b(x, y)` (`FinslerLengthStructure.dist_comm_le`).
-/

open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ENNReal
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Finsler seminorms on a vector space -/

/-- A **Finsler seminorm** on a topological vector space (Larotonda, Def. 2.2): a continuous,
nonnegative, subadditive, positively homogeneous function. It need not be symmetric. -/
structure FinslerSeminorm (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] where
  /-- The seminorm as a function. -/
  toFun : E → ℝ
  nonneg' : ∀ v, 0 ≤ toFun v
  add_le' : ∀ v w, toFun (v + w) ≤ toFun v + toFun w
  smul_eq' : ∀ c : ℝ, 0 ≤ c → ∀ v, toFun (c • v) = c * toFun v
  continuous' : Continuous toFun

namespace FinslerSeminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

instance : CoeFun (FinslerSeminorm E) fun _ ↦ E → ℝ := ⟨FinslerSeminorm.toFun⟩

variable (μ : FinslerSeminorm E)

theorem nonneg (v : E) : 0 ≤ μ v := μ.nonneg' v

theorem add_le (v w : E) : μ (v + w) ≤ μ v + μ w := μ.add_le' v w

theorem smul_eq {c : ℝ} (hc : 0 ≤ c) (v : E) : μ (c • v) = c * μ v := μ.smul_eq' c hc v

theorem continuous : Continuous μ := μ.continuous'

@[simp] theorem map_zero : μ 0 = 0 := by
  simpa using μ.smul_eq le_rfl (0 : E)

/-- A Finsler seminorm is a Finsler *norm* if it is definite (Larotonda, Def. 2.2(2)). -/
def IsNorm : Prop := ∀ v, μ v = 0 → v = 0

/-- A Finsler seminorm is *reversible* if it is symmetric: it is then a continuous seminorm in
the usual sense. -/
def IsReversible : Prop := ∀ v, μ (-v) = μ v

end FinslerSeminorm

/-! ### Fields of Finsler seminorms on a manifold -/

section Manifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E M) in
/-- A **field of Finsler seminorms**: a Finsler seminorm `μ_p` on each tangent space `T_p M`.
**No condition** relates `μ_p` and `μ_q` for `p ≠ q`; see `FinslerMetric` (continuity on `TM`)
and `FinslerLengthStructure` (continuity along `C¹` curves). -/
structure FinslerSeminormField where
  /-- The field, as a function on the tangent bundle. -/
  toFun : TangentBundle E M → ℝ
  nonneg' : ∀ p, 0 ≤ toFun p
  add_le' : ∀ (x : M) (v w : E), toFun ⟨x, v + w⟩ ≤ toFun ⟨x, v⟩ + toFun ⟨x, w⟩
  smul_eq' : ∀ (x : M) (c : ℝ), 0 ≤ c → ∀ v : E, toFun ⟨x, c • v⟩ = c * toFun ⟨x, v⟩
  continuous_fiber' : ∀ x : M, Continuous fun v : E ↦ toFun ⟨x, v⟩

namespace FinslerSeminormField

variable (μ : FinslerSeminormField E M)

instance : CoeFun (FinslerSeminormField E M) fun _ ↦ TangentBundle E M → ℝ := ⟨toFun⟩

/-- The Finsler seminorm `μ_x` on the tangent space at `x`. -/
def fiber (x : M) : FinslerSeminorm E where
  toFun v := μ ⟨x, v⟩
  nonneg' _ := μ.nonneg' _
  add_le' := μ.add_le' x
  smul_eq' := μ.smul_eq' x
  continuous' := μ.continuous_fiber' x

theorem fiber_apply (x : M) (v : E) : μ.fiber x v = μ ⟨x, v⟩ := rfl

theorem nonneg (p : TangentBundle E M) : 0 ≤ μ p := μ.nonneg' p

@[simp] theorem apply_zero (x : M) : μ ⟨x, (0 : E)⟩ = 0 := (μ.fiber x).map_zero

/-- Each `μ_p` is a Finsler norm (Larotonda, Def. 2.2(2)). -/
def IsNondegenerate : Prop := ∀ x, (μ.fiber x).IsNorm

/-- Each `μ_p` is symmetric. Exactly in this case the distance is symmetric. -/
def IsReversible : Prop := ∀ x, (μ.fiber x).IsReversible

end FinslerSeminormField

variable (E M) in
/-- A **Finsler metric** (Larotonda, Def. 2.3(2)): a field of Finsler seminorms that is
**continuous on the tangent bundle** `TM`. This is the standard meaning of "Finsler metric".
Compare `FinslerLengthStructure`, which only asks for continuity along `C¹` curves. -/
structure FinslerMetric extends FinslerSeminormField E M where
  continuous' : Continuous toFun

variable (E M) in
/-- A **Finsler length structure** (Larotonda, Def. 2.3(1), "continuous along paths"): a field of
Finsler seminorms such that `t ↦ μ (γ̇ t)` is **continuous along every `C¹` curve** `γ`. Nothing
is assumed about continuity on `TM`. It is the weakest hypothesis under which lengths of curves
are defined; quotient metrics on homogeneous spaces are of this kind (Larotonda, Lemma 3.19).
Every `FinslerMetric` is one (`FinslerMetric.toFinslerLengthStructure`). -/
structure FinslerLengthStructure extends FinslerSeminormField E M where
  continuous_velocity' : ∀ γ : ℝ → M, IsCkCurve E 1 γ →
    Continuous fun t ↦ toFun (velocity E γ t)

/-! ### The velocity is continuous in `TM` -/

/-- **The velocity of a `C¹` curve is a continuous curve in the tangent bundle.** In a chart `i`
around `γ t`, the velocity reads `s ↦ (i (γ s), (i ∘ γ)'(s))`, which is continuous, and the
chart of `TM` is a homeomorphism onto its image. -/
theorem continuous_velocity {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) :
    Continuous (velocity E γ) := by
  rw [continuous_iff_continuousAt]
  intro t
  set i : atlas E M := ⟨chartAt E (γ t), chart_mem_atlas E _⟩
  set Φ := tangentChart i i.1
  set O := γ ⁻¹' i.1.source
  have hO : IsOpen O := i.1.open_source.preimage hγ.1
  have htO : t ∈ O := mem_chart_source E (γ t)
  -- in the chart, the velocity is `s ↦ (i (γ s), liftCoord i (velocity) s)`
  set c : ℝ → E × E := fun s ↦ (i.1 (γ s), liftCoord i (velocity E γ) s)
  have hc : ContinuousOn c O := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact (hγ.2 i).continuousOn
    · exact ((isCkLift_velocity (k := 0) hγ).2 i).continuousOn
  have hsrc : ∀ s ∈ O, velocity E γ s ∈ Φ.source := fun s hs ↦
    (mem_tangentChart_source i i.1 _).mpr ⟨hs, hs⟩
  have hΦ : ∀ s ∈ O, Φ (velocity E γ s) = c s := fun s _ ↦ rfl
  have hev : velocity E γ =ᶠ[𝓝 t] Φ.symm ∘ c :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds htO) fun s hs ↦ by
      simp only [Function.comp_apply, ← hΦ s hs, Φ.left_inv (hsrc s hs)]
  refine ContinuousAt.congr ?_ hev.symm
  have htgt : c t ∈ Φ.target := by
    rw [← hΦ t htO]
    exact Φ.map_source (hsrc t htO)
  exact (Φ.continuousAt_symm htgt).comp (hc.continuousAt (hO.mem_nhds htO))

/-- **Every Finsler metric is a Finsler length structure**: continuity on `TM` gives continuity
along `C¹` curves, since their velocities are continuous in `TM`. -/
def FinslerMetric.toFinslerLengthStructure (μ : FinslerMetric E M) :
    FinslerLengthStructure E M where
  toFinslerSeminormField := μ.toFinslerSeminormField
  continuous_velocity' _ hγ := μ.continuous'.comp (continuous_velocity hγ)

/-! ### Length and distance (for Finsler length structures) -/

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

theorem continuous_velocity {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) :
    Continuous fun t ↦ μ.toFun (velocity E γ t) :=
  μ.continuous_velocity' γ hγ

/-- The **length** of a `C¹` curve `γ` on `[a, b]`: `∫ₐᵇ μ (γ̇ t) dt` (Larotonda, Def. 2.6). It
only uses the continuity of `μ` along curves, so it is defined for Finsler length structures. -/
def length (γ : ℝ → M) (a b : ℝ) : ℝ := ∫ t in a..b, μ.toFun (velocity E γ t)

theorem length_nonneg (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) : 0 ≤ μ.length γ a b :=
  intervalIntegral.integral_nonneg hab fun _ _ ↦ μ.nonneg' _

/-- Lengths add along adjacent intervals. -/
theorem length_add {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (a b c : ℝ) :
    μ.length γ a b + μ.length γ b c = μ.length γ a c :=
  intervalIntegral.integral_add_adjacent_intervals
    ((μ.continuous_velocity hγ).intervalIntegrable a b)
    ((μ.continuous_velocity hγ).intervalIntegrable b c)

/-- The velocity of a constant curve vanishes. -/
theorem velocity_const (x : M) (t : ℝ) : velocity E (fun _ : ℝ ↦ x) t = ⟨x, (0 : E)⟩ := by
  have h : HasDirDerivAt (chartAt E x ∘ fun _ : ℝ ↦ x) t 1 0 := by
    unfold HasDirDerivAt
    simp
  change (⟨x, dMB (chartAt E x ∘ fun _ : ℝ ↦ x) (t, 1)⟩ : TangentBundle E M) = ⟨x, (0 : E)⟩
  exact congrArg (fun v : E ↦ (⟨x, v⟩ : TangentBundle E M)) h.dMB_eq

/-- A constant curve has length zero. -/
theorem length_const (x : M) (a b : ℝ) : μ.length (fun _ ↦ x) a b = 0 := by
  simp [length, velocity_const]

/-- `μ.Reach x y L`: the point `y` is reached from `x` by a **chain of `C¹` arcs** of total length
`L`, that is, by a piecewise `C¹` path. A chain is either empty (`x = y`, `L = 0`) or an arc
`γ|[a, b]` from `x = γ a` followed by a chain from `γ b`. Working with chains, instead of a
single `C¹` curve, is what makes concatenation, hence the triangle inequality, immediate: no
smoothing at the junctions is needed. -/
inductive Reach : M → M → ℝ → Prop
  | refl (x : M) : Reach x x 0
  | cons {γ : ℝ → M} {a b : ℝ} {y : M} {L : ℝ} : IsCkCurve E 1 γ → a ≤ b →
      Reach (γ b) y L → Reach (γ a) y (μ.length γ a b + L)

variable {μ}

/-- A single `C¹` arc is a chain. -/
theorem Reach.single {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    μ.Reach (γ a) (γ b) (μ.length γ a b) := by
  simpa using Reach.cons hγ hab (Reach.refl (μ := μ) (γ b))

theorem Reach.nonneg {x y : M} {L : ℝ} (h : μ.Reach x y L) : 0 ≤ L := by
  induction h with
  | refl => exact le_rfl
  | cons _ hab _ ih => exact add_nonneg (μ.length_nonneg _ hab) ih

/-- **Concatenation of chains**: lengths add. -/
theorem Reach.trans {x y z : M} {L L' : ℝ} (h : μ.Reach x y L) (h' : μ.Reach y z L') :
    μ.Reach x z (L + L') := by
  induction h with
  | refl => simpa using h'
  | cons hγ hab _ ih =>
    rw [add_assoc]
    exact Reach.cons hγ hab (ih h')

variable (μ)

/-- The **Finsler distance** (Larotonda, Def. 2.7): the infimum of the lengths of piecewise `C¹`
paths (chains of `C¹` arcs, `Reach`) from `x` to `y`, with value `∞` if there is none. It is
defined for Finsler length structures. It need not be symmetric (it is when `μ` is reversible)
and it may vanish between distinct points, even when every `μ_p` is a norm (Michor–Mumford,
Doc. Math. 10 (2005), Thm. 5.2). -/
def dist (x y : M) : ℝ≥0∞ := ⨅ L : {L : ℝ // μ.Reach x y L}, ENNReal.ofReal L.1

theorem dist_le_of_reach {x y : M} {L : ℝ} (h : μ.Reach x y L) :
    μ.dist x y ≤ ENNReal.ofReal L :=
  iInf_le_of_le ⟨L, h⟩ le_rfl

theorem dist_le {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    μ.dist (γ a) (γ b) ≤ ENNReal.ofReal (μ.length γ a b) :=
  μ.dist_le_of_reach (Reach.single hγ hab)

/-- The distance from a point to itself is zero (the empty chain). -/
@[simp] theorem dist_self (x : M) : μ.dist x x = 0 := by
  have := μ.dist_le_of_reach (Reach.refl (μ := μ) x)
  rw [ENNReal.ofReal_zero] at this
  exact le_antisymm this bot_le

/-- **The triangle inequality** `d(x, z) ≤ d(x, y) + d(y, z)`, by concatenation of chains. With
`dist_self`, the Finsler distance is an extended, possibly asymmetric, pseudo-distance. -/
theorem dist_triangle (x y z : M) : μ.dist x z ≤ μ.dist x y + μ.dist y z := by
  rcases isEmpty_or_nonempty {L : ℝ // μ.Reach x y L} with hxy | hxy
  · have : μ.dist x y = ⊤ := by simp [dist]
    simp [this]
  rcases isEmpty_or_nonempty {L : ℝ // μ.Reach y z L} with hyz | hyz
  · have : μ.dist y z = ⊤ := by simp [dist]
    simp [this]
  refine ENNReal.le_iInf_add_iInf fun p q ↦ ?_
  rw [← ENNReal.ofReal_add p.2.nonneg q.2.nonneg]
  exact μ.dist_le_of_reach (p.2.trans q.2)

end FinslerLengthStructure

/-! ### Reversed curves and the symmetry of the distance -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [MBManifold E M] in
/-- The reversed curve `t ↦ γ (-t)` of a `C¹` curve is `C¹`. -/
theorem isCkCurve_reverse {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) :
    IsCkCurve E 1 (fun t ↦ γ (-t)) := by
  refine ⟨hγ.1.comp continuous_neg, fun i ↦ ?_⟩
  have h := (hγ.2 i).comp_clm (-ContinuousLinearMap.id ℝ ℝ) (i.1.open_source.preimage hγ.1)
  exact h

/-- The velocity of the reversed curve is the opposite of the velocity. -/
theorem velocity_reverse {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (t : ℝ) :
    velocity E (fun s ↦ γ (-s)) t = ⟨γ (-t), -(show E from (velocity E γ (-t)).2)⟩ := by
  set i : atlas E M := ⟨chartAt E (γ (-t)), chart_mem_atlas E _⟩
  set L : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hc : ContDiffMBOn 1 (i.1 ∘ γ) (γ ⁻¹' i.1.source) := hγ.2 i
  have hV : IsOpen (γ ⁻¹' i.1.source) := i.1.open_source.preimage hγ.1
  have hL : ContDiffMBOn 1 L (L ⁻¹' (γ ⁻¹' i.1.source)) := L.contDiffMBOn 1 _
  have hmem : t ∈ L ⁻¹' (γ ⁻¹' i.1.source) := by
    change γ (-t) ∈ i.1.source
    exact mem_chart_source E _
  have hcomp := ContDiffMBOn.dMB_comp hV hc hL (fun s hs ↦ hs) hmem 1
  have hL1 : dMB L (t, 1) = -1 := by
    rw [(L.hasDirDerivAt t 1).dMB_eq]
    simp [L]
  have hLt : L t = -t := by simp [L]
  have hneg := hc.dMB_smul (x := L t) hmem (-1) 1
  rw [hLt] at hneg hcomp
  have hfun : (i.1 ∘ fun s ↦ γ (-s)) = (i.1 ∘ γ) ∘ L := by
    funext s
    simp [L]
  have key : dMB (i.1 ∘ fun s ↦ γ (-s)) (t, 1) = -dMB (i.1 ∘ γ) (-t, 1) := by
    rw [hfun, hcomp, hL1]
    simpa using hneg
  change (⟨γ (-t), dMB (i.1 ∘ fun s ↦ γ (-s)) (t, 1)⟩ : TangentBundle E M) =
    ⟨γ (-t), -dMB (i.1 ∘ γ) (-t, 1)⟩
  exact congrArg (fun v : E ↦ (⟨γ (-t), v⟩ : TangentBundle E M)) key

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

/-- For a reversible `μ`, reversing a curve does not change its length. -/
theorem length_reverse (hrev : μ.IsReversible) {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (a b : ℝ) :
    μ.length (fun s ↦ γ (-s)) (-b) (-a) = μ.length γ a b := by
  have hpt : ∀ t, μ.toFun (velocity E (fun s ↦ γ (-s)) t) = μ.toFun (velocity E γ (-t)) := by
    intro t
    rw [velocity_reverse hγ t]
    exact hrev (γ (-t)) _
  simp only [length, hpt]
  rw [intervalIntegral.integral_comp_neg (fun t ↦ μ.toFun (velocity E γ t))]
  simp

variable {μ}

/-- For a reversible `μ`, chains can be run backwards. -/
theorem Reach.symm (hrev : μ.IsReversible) {x y : M} {L : ℝ} (h : μ.Reach x y L) :
    μ.Reach y x L := by
  induction h with
  | refl x => exact Reach.refl x
  | @cons γ a b y L hγ hab _ ih =>
    have hback := Reach.single (μ := μ) (isCkCurve_reverse hγ) (neg_le_neg hab)
    simp only [neg_neg] at hback
    rw [μ.length_reverse hrev hγ] at hback
    rw [add_comm]
    exact ih.trans hback

variable (μ)

/-- **For a reversible `μ`, the Finsler distance is symmetric**, hence an extended
pseudo-metric. -/
theorem dist_comm (hrev : μ.IsReversible) (x y : M) : μ.dist x y = μ.dist y x := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun p ↦ μ.dist_le_of_reach (p.2.symm hrev)
  · exact le_iInf fun p ↦ μ.dist_le_of_reach (p.2.symm hrev)

/-! ### Bounded reversibility -/

/-- **Bounded reversibility.** If `μ_x(-v) ≤ λ μ_x(v)` for all `x, v` (a *reversibility
constant* `λ ≥ 0`), reversing a `C¹` arc multiplies its length by at most `λ`. -/
theorem length_reverse_le {lam : ℝ} (hlam : ∀ x (v : E), μ.toFun ⟨x, -v⟩ ≤ lam * μ.toFun ⟨x, v⟩)
    {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    μ.length (fun s ↦ γ (-s)) (-b) (-a) ≤ lam * μ.length γ a b := by
  have hpt : ∀ t, μ.toFun (velocity E (fun s ↦ γ (-s)) t) ≤ lam * μ.toFun (velocity E γ (-t)) := by
    intro t
    rw [velocity_reverse hγ t]
    exact hlam (γ (-t)) _
  have hcont := μ.continuous_velocity hγ
  calc μ.length (fun s ↦ γ (-s)) (-b) (-a)
      ≤ ∫ t in (-b)..(-a), lam * μ.toFun (velocity E γ (-t)) :=
        intervalIntegral.integral_mono_on (neg_le_neg hab)
          ((μ.continuous_velocity (isCkCurve_reverse hγ)).intervalIntegrable _ _)
          (((hcont.comp continuous_neg).const_smul lam).intervalIntegrable _ _)
          fun t _ ↦ hpt t
    _ = lam * μ.length γ a b := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_neg (fun t ↦ μ.toFun (velocity E γ t))]
        simp [length]

variable {μ}

/-- With a reversibility constant `λ`, a chain of length `L` can be run backwards with length at
most `λ L`. -/
theorem Reach.reverse_le {lam : ℝ}
    (hlam : ∀ x (v : E), μ.toFun ⟨x, -v⟩ ≤ lam * μ.toFun ⟨x, v⟩) {x y : M} {L : ℝ}
    (h : μ.Reach x y L) : ∃ L' ≤ lam * L, μ.Reach y x L' := by
  induction h with
  | refl x => exact ⟨0, by simp, Reach.refl x⟩
  | @cons γ a b y L hγ hab _ ih =>
    obtain ⟨L', hL', hrest⟩ := ih
    have hback := Reach.single (μ := μ) (isCkCurve_reverse hγ) (neg_le_neg hab)
    simp only [neg_neg] at hback
    refine ⟨L' + μ.length (fun s ↦ γ (-s)) (-b) (-a), ?_, hrest.trans hback⟩
    have := μ.length_reverse_le hlam hγ hab
    nlinarith

variable (μ)

/-- **With a reversibility constant `λ > 0`, `d_b(y, x) ≤ λ d_b(x, y)`.** -/
theorem dist_comm_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ x (v : E), μ.toFun ⟨x, -v⟩ ≤ lam * μ.toFun ⟨x, v⟩) (x y : M) :
    μ.dist y x ≤ ENNReal.ofReal lam * μ.dist x y := by
  rw [dist, dist, ENNReal.mul_iInf_of_ne (by simpa using hlam0) (by simp)]
  refine le_iInf fun p ↦ ?_
  obtain ⟨L', hL', hL'reach⟩ := p.2.reverse_le hlam
  refine (μ.dist_le_of_reach hL'reach).trans ?_
  rw [← ENNReal.ofReal_mul hlam0.le]
  exact ENNReal.ofReal_le_ofReal hL'

end FinslerLengthStructure


namespace FinslerMetric

variable (μ : FinslerMetric E M)

/-- The length of a curve for a Finsler metric, through its Finsler length structure. -/
abbrev length (γ : ℝ → M) (a b : ℝ) : ℝ := μ.toFinslerLengthStructure.length γ a b

/-- The distance of a Finsler metric, through its Finsler length structure. -/
abbrev dist (x y : M) : ℝ≥0∞ := μ.toFinslerLengthStructure.dist x y

end FinslerMetric

end Manifold

end LocallyConvex.Manifolds
