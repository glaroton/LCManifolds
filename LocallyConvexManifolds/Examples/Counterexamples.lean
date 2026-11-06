/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.SubmanifoldNotions
import LocallyConvexAnalysis.BoundedBelow

/-!
# Counterexamples: weak immersions that are not immersions

The inclusion `ι : ℓ¹ → ℓ²` is a continuous injective linear map, hence a weak immersion
between the Banach spaces `ℓ¹` and `ℓ²` (seen as manifolds), but it is not an immersion: its
differential `ι` is not a topological isomorphism onto its range, since the vectors
`x_n = e₀ + ⋯ + e_{n-1}` have `‖x_n‖₁ = n` and `‖x_n‖₂ = √n`.
(`isWeakImmersion_lpInclusion`, `not_isImmersion_lpInclusion`).

Continuity of `ι` is obtained from the closed graph theorem: its graph is closed because the
coordinate evaluations are continuous on both spaces.
-/

open Set Filter
open scoped Topology Manifold ENNReal
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-- `ℓ^p` of real sequences. -/
abbrev ellp (p : ℝ≥0∞) := lp (fun _ : ℕ ↦ ℝ) p

instance : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The inclusion `ℓ¹ → ℓ²`, as a linear map. -/
def lpInclusionₗ : ellp 1 →ₗ[ℝ] ellp 2 := lp.linearMapOfLE ℝ (fun _ : ℕ ↦ ℝ) (by norm_num)

theorem lpInclusionₗ_apply (x : ellp 1) (i : ℕ) : lpInclusionₗ x i = x i := rfl

/-- The graph of the inclusion is closed: coordinates are continuous. -/
theorem isClosed_graph_lpInclusionₗ :
    IsClosed (lpInclusionₗ.graph : Set (ellp 1 × ellp 2)) := by
  have hset : (lpInclusionₗ.graph : Set (ellp 1 × ellp 2)) =
      ⋂ i : ℕ, {q | (q.2 : ℕ → ℝ) i = (q.1 : ℕ → ℝ) i} := by
    ext q
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h i; rw [h]; rfl
    · intro h; ext i; exact h i
  rw [hset]
  refine isClosed_iInter fun i ↦ isClosed_eq ?_ ?_
  · exact (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) (p := 2) i).continuous.comp continuous_snd
  · exact (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) (p := 1) i).continuous.comp continuous_fst

/-- The inclusion `ℓ¹ → ℓ²`, continuous by the closed graph theorem. -/
def lpInclusion : ellp 1 →L[ℝ] ellp 2 :=
  ⟨lpInclusionₗ, LinearMap.continuous_of_isClosed_graph lpInclusionₗ isClosed_graph_lpInclusionₗ⟩

theorem lpInclusion_apply (x : ellp 1) (i : ℕ) : (lpInclusion x : ℕ → ℝ) i = x i := rfl

theorem lpInclusion_injective : Function.Injective lpInclusion := by
  intro x y h
  ext i
  have := congrArg (fun z : ellp 2 ↦ (z : ℕ → ℝ) i) h
  simpa only [lpInclusion_apply] using this

/-- The vector `e₀ + ⋯ + e_{n-1}` in `ℓ^p`. -/
def ones (p : ℝ≥0∞) (n : ℕ) : ellp p := ∑ i ∈ Finset.range n, lp.single p i (1 : ℝ)

theorem norm_ones_one (n : ℕ) : ‖ones 1 n‖ = n := by
  have := lp.norm_sum_single (E := fun _ : ℕ ↦ ℝ) (p := 1) (by norm_num) (fun _ ↦ (1 : ℝ))
    (Finset.range n)
  simpa [ones] using this

theorem norm_ones_two (n : ℕ) : ‖ones 2 n‖ ^ 2 = n := by
  have := lp.norm_sum_single (E := fun _ : ℕ ↦ ℝ) (p := 2) (by norm_num) (fun _ ↦ (1 : ℝ))
    (Finset.range n)
  simpa [ones] using this

theorem lpInclusion_ones (n : ℕ) : lpInclusion (ones 1 n) = ones 2 n := by
  ext i
  rw [lpInclusion_apply]
  simp [ones, lp.coeFn_single]

/-- **The inclusion `ℓ¹ → ℓ²` is not bounded below.** -/
theorem not_boundedBelow_lpInclusion :
    ¬ ∃ m > 0, ∀ v, m * ‖v‖ ≤ ‖lpInclusion v‖ := by
  rintro ⟨m, hm, hbd⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / m ^ 2)
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
  have h := hbd (ones 1 n)
  rw [lpInclusion_ones, norm_ones_one] at h
  -- `m n ≤ √n`, so `m² n² ≤ n`, i.e. `m² n ≤ 1`
  have h2 : (m * n) ^ 2 ≤ ‖ones 2 n‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  rw [norm_ones_two] at h2
  have : m ^ 2 * n ≤ 1 := by nlinarith
  have : 1 < m ^ 2 * n := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  linarith

/-- In the (identity) charts of the model spaces, the differential of `ι` is `ι`. -/
theorem dMB_chart_lpInclusion (x : ellp 1) :
    (fun v : ellp 1 ↦ dMB (chartAt (ellp 2) (lpInclusion x) ∘ lpInclusion ∘
      (chartAt (ellp 1) x).symm) (chartAt (ellp 1) x x, v)) = ⇑lpInclusion := by
  funext v
  change dMB (⇑lpInclusion) (x, v) = lpInclusion v
  exact (lpInclusion.hasDirDerivAt x v).dMB_eq

/-- **`ℓ¹ → ℓ²` is a weak immersion** (injective differential). -/
theorem isWeakImmersion_lpInclusion : IsWeakImmersion (ellp 1) (ellp 2) lpInclusion := by
  refine ⟨fun k ↦ (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).mpr
    (lpInclusion.contDiffMBOn k univ), fun x ↦ ?_⟩
  rw [dMB_chart_lpInclusion]
  exact lpInclusion_injective

/-- **`ℓ¹ → ℓ²` is not an immersion**: its differential is not a topological isomorphism onto
its range. -/
theorem not_isImmersion_lpInclusion : ¬ IsImmersion (ellp 1) (ellp 2) lpInclusion := by
  intro h
  have hemb := (h.2 0).2
  rw [dMB_chart_lpInclusion] at hemb
  exact not_boundedBelow_lpInclusion (exists_boundedBelow_of_isEmbedding hemb)

end LocallyConvex.Manifolds
