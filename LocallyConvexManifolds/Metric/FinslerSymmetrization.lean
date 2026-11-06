/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Metric.FinslerMetricSpace

/-!
# The symmetrization of a Finsler structure

For a Finsler length structure `μ`, not necessarily reversible, the **symmetrization**
`μₛ(v) = μ(v) + μ(-v)` is a reversible Finsler length structure (`symm`, `symm_isReversible`).
It compares with `μ` as follows.

* Always: `μ ≤ μₛ` and `μ(-v) ≤ μₛ(v)`, hence `d_b(x, y) ≤ d_s(x, y)` and `d_b(y, x) ≤ d_s(x, y)`
  (`dist_le_dist_symm`, `dist_swap_le_dist_symm`): the symmetrized distance
  `max (d_b(x, y), d_b(y, x))` is at most `d_s`.
* With a reversibility constant `λ` (`μ(-v) ≤ λ μ(v)`): `μₛ ≤ (1 + λ) μ`, hence
  `d_s ≤ (1 + λ) d_b` (`dist_symm_le`), and the identity is a homeomorphism between `(M, d_b)` (with
  the symmetrized topology) and `(M, d_s)` (`homeomorphSymm`). So, **for the topology**, a
  non-reversible structure with bounded asymmetry may be replaced by its symmetrization.

What the symmetrization does not preserve is the metric geometry: lengths and shortest curves of
`d_b` and `d_s` are different, and without a reversibility constant `d_s` may be much larger than
`d_b(x, y) + d_b(y, x)` (both directions are measured along the same curve), so that its topology
may be strictly finer.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

/-- The **symmetrization** `μₛ(v) = μ(v) + μ(-v)`. -/
def symm : FinslerLengthStructure E M where
  toFun p := μ.toFun p + μ.toFun ⟨p.proj, -(show E from p.2)⟩
  nonneg' p := add_nonneg (μ.nonneg' _) (μ.nonneg' _)
  add_le' x v w := by
    have h1 := μ.add_le' x v w
    have h2 := μ.add_le' x (-v) (-w)
    rw [← neg_add] at h2
    change μ.toFun ⟨x, v + w⟩ + μ.toFun ⟨x, -(v + w)⟩ ≤
      μ.toFun ⟨x, v⟩ + μ.toFun ⟨x, -v⟩ + (μ.toFun ⟨x, w⟩ + μ.toFun ⟨x, -w⟩)
    linarith
  smul_eq' x c hc v := by
    change μ.toFun ⟨x, c • v⟩ + μ.toFun ⟨x, -(c • v)⟩ = c * (μ.toFun ⟨x, v⟩ + μ.toFun ⟨x, -v⟩)
    rw [← smul_neg, μ.smul_eq' x c hc, μ.smul_eq' x c hc, mul_add]
  continuous_fiber' x :=
    (μ.continuous_fiber' x).add ((μ.continuous_fiber' x).comp continuous_neg)
  continuous_velocity' γ hγ := by
    have h1 := μ.continuous_velocity hγ
    have h2 := (μ.continuous_velocity (isCkCurve_reverse hγ)).comp continuous_neg
    set F : ℝ → ℝ := fun u ↦ μ.toFun ⟨γ u, -(show E from (velocity E γ u).2)⟩
    have hF : ∀ s, μ.toFun (velocity E (fun r ↦ γ (-r)) s) = F (-s) := fun s ↦ by
      rw [velocity_reverse hγ s]
    refine h1.add (h2.congr fun t ↦ ?_)
    simp only [Function.comp_apply]
    rw [hF, neg_neg]
    rfl

theorem symm_apply (x : M) (v : E) :
    μ.symm.toFun ⟨x, v⟩ = μ.toFun ⟨x, v⟩ + μ.toFun ⟨x, -v⟩ := rfl

/-- The symmetrization is reversible. -/
theorem symm_isReversible : μ.symm.IsReversible := by
  intro x v
  change μ.toFun ⟨x, -v⟩ + μ.toFun ⟨x, - -v⟩ = μ.toFun ⟨x, v⟩ + μ.toFun ⟨x, -v⟩
  rw [neg_neg, add_comm]

/-! ### Comparison of lengths and distances -/

variable {μ}

/-- If `ν ≤ c μ` pointwise, lengths compare in the same way. -/
theorem length_le_mul_of_le {ν : FinslerLengthStructure E M} {c : ℝ}
    (h : ∀ p, ν.toFun p ≤ c * μ.toFun p) {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ}
    (hab : a ≤ b) : ν.length γ a b ≤ c * μ.length γ a b := by
  unfold length
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab ((ν.continuous_velocity hγ).intervalIntegrable _ _)
    (((μ.continuous_velocity hγ).const_smul c).intervalIntegrable _ _) fun t _ ↦ h _

/-- If `ν ≤ c μ` pointwise (`c ≥ 0`), a chain of length `L` for `μ` has length `≤ c L` for `ν`. -/
theorem Reach.mono_mul {ν : FinslerLengthStructure E M} {c : ℝ}
    (h : ∀ p, ν.toFun p ≤ c * μ.toFun p) {x y : M} {L : ℝ} (hL : μ.Reach x y L) :
    ∃ L' ≤ c * L, ν.Reach x y L' := by
  induction hL with
  | refl x => exact ⟨0, by simp, Reach.refl x⟩
  | @cons γ a b y L hγ hab _ ih =>
    obtain ⟨L', hL', hrest⟩ := ih
    refine ⟨ν.length γ a b + L', ?_, Reach.cons hγ hab hrest⟩
    have := length_le_mul_of_le h hγ hab
    nlinarith

/-- If `ν ≤ c μ` pointwise (`c > 0`), then `d_ν ≤ c d_μ`. -/
theorem dist_le_mul_of_le {ν : FinslerLengthStructure E M} {c : ℝ} (hc : 0 < c)
    (h : ∀ p, ν.toFun p ≤ c * μ.toFun p) (x y : M) :
    ν.dist x y ≤ ENNReal.ofReal c * μ.dist x y := by
  rw [dist, dist, ENNReal.mul_iInf_of_ne (by simpa using hc) (by simp)]
  refine le_iInf fun p ↦ ?_
  obtain ⟨L', hL', hreach⟩ := p.2.mono_mul h
  refine (ν.dist_le_of_reach hreach).trans ?_
  rw [← ENNReal.ofReal_mul hc.le]
  exact ENNReal.ofReal_le_ofReal hL'

variable (μ)

/-- `d_b ≤ d_s`. -/
theorem dist_le_dist_symm (x y : M) : μ.dist x y ≤ μ.symm.dist x y := by
  have h := dist_le_mul_of_le (μ := μ.symm) (ν := μ) one_pos
    (fun p ↦ by
      rw [one_mul]
      exact le_add_of_nonneg_right (μ.nonneg' _)) x y
  simpa using h

/-- `d_b(y, x) ≤ d_s(x, y)`. -/
theorem dist_swap_le_dist_symm (x y : M) : μ.dist y x ≤ μ.symm.dist x y := by
  rw [μ.symm.dist_comm μ.symm_isReversible]
  exact μ.dist_le_dist_symm y x

/-- **With a reversibility constant `λ`, `d_s ≤ (1 + λ) d_b`.** -/
theorem dist_symm_le {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ x (v : E), μ.toFun ⟨x, -v⟩ ≤ lam * μ.toFun ⟨x, v⟩) (x y : M) :
    μ.symm.dist x y ≤ ENNReal.ofReal (1 + lam) * μ.dist x y :=
  dist_le_mul_of_le (by linarith) (fun p ↦ by
    have := hlam p.proj p.2
    change μ.toFun p + μ.toFun ⟨p.proj, -(show E from p.2)⟩ ≤ (1 + lam) * μ.toFun p
    nlinarith) x y

/-- **For the topology, a structure with bounded asymmetry may be replaced by its
symmetrization**: with a reversibility constant, the identity `(M, d_b) → (M, d_s)` is a
homeomorphism (the topology of `(M, d_b)` being that of the symmetrized distance). -/
def homeomorphSymm {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ x (v : E), μ.toFun ⟨x, -v⟩ ≤ lam * μ.toFun ⟨x, v⟩) :
    μ.FinslerSpace ≃ₜ μ.symm.FinslerSpace := by
  haveI : Fact μ.symm.IsReversible := ⟨μ.symm_isReversible⟩
  refine
    { toFun := fun x ↦ μ.symm.toFinsler (μ.ofFinsler x)
      invFun := fun x ↦ μ.toFinsler (μ.symm.ofFinsler x)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · -- `d_s ≤ (1 + λ) d_b ≤ (1 + λ) max (d_b, d_b')`
    refine (show LipschitzWith (1 + lam).toNNReal _ from fun x y ↦ ?_).continuous
    rw [μ.symm.edist_toFinsler]
    refine (μ.dist_symm_le hlam0 hlam _ _).trans ?_
    exact mul_le_mul' le_rfl (bdist_le_edist x y)
  · -- `max (d_b, d_b') ≤ d_s`
    refine (LipschitzWith.of_edist_le fun x y ↦ ?_).continuous
    change edist (μ.toFinsler (μ.symm.ofFinsler x)) (μ.toFinsler (μ.symm.ofFinsler y)) ≤
      edist (μ.symm.toFinsler (μ.symm.ofFinsler x)) (μ.symm.toFinsler (μ.symm.ofFinsler y))
    rw [μ.symm.edist_toFinsler, edist_eq_max_bdist, bdist_toFinsler, bdist_toFinsler]
    exact max_le (μ.dist_le_dist_symm _ _) (μ.dist_swap_le_dist_symm _ _)

end FinslerLengthStructure

end LocallyConvex.Manifolds
