/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Metric.FinslerMetricSpace
import LCManifolds.Metric.Bilinear
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Bounded Finsler structures: the distance and the topology of the manifold

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 9,
§9.1.2: Definición 9.1.3, Observación 9.1.4, Lema 9.1.8 (adapted from H. Upmeier) and
Corolario 9.1.9.

In this file the model `E` is a **normed space**: the conditions of *Estructuras*, §9.1.2,
compare `μ` with the norm of the model. A Finsler structure `μ` is **bounded below** at `p`
(*acotada inferiormente*) if there are a chart `φ` around `p` and `C > 0` with
`‖φ_{*x} v‖ ≤ C μ_x(v)` for `x` in the domain of `φ` (`IsBoundedBelowOn`), and **bounded above**
(*acotada superiormente*) if `m μ_x(v) ≤ ‖φ_{*x} v‖` for some `m > 0`.

**A word of caution on locally convex models.** If the model is not normable, no Finsler norm
`μ_x` (a norm on `T_x M`) can be bounded above and below by a norm inducing its topology: the
topology of `E` would be a norm topology. So the "strong" Finsler manifolds of
*Estructuras*, Observación 9.1.4, are a phenomenon of normed models; this is Palais' setting.

## Main results

* `norm_chart_sub_le`: if `μ` is bounded below on a chart `φ` with constant `C`, a `C¹` curve
  that stays in the domain of `φ` satisfies `‖φ(γ t) − φ(γ s)‖ ≤ C L_b(γ|[s, t])`. This is the
  integrated form of the bound (*Estructuras*, (9.2)); the model is assumed complete (Banach),
as in *Estructuras*, since the proof integrates the derivative of `φ ∘ γ` in `E`.
* `arc_exit`, `reach_exit`: **leaving a chart costs length.** If `B̄(φ x₀, r) ⊆ φ(U)` and a chain
  of `C¹` arcs starts at `x₀`, then either `C L ≥ r` or the chain ends in `U`, at a point `y` with
  `‖φ y − φ x₀‖ ≤ C L`. This uses that `E` is **complete** and `M` is **Hausdorff**: a curve that
  leaves `U` before its image leaves the ball would have, by completeness, a limit point inside
  the ball, hence (by Hausdorff) inside `U`.
* `norm_chart_sub_le_dist` (**Lema 9.1.8**): near `x₀`, `‖φ y − φ x₀‖ ≤ C d_b(x₀, y)`, and the
  points at small `d_b`-distance from `x₀` lie in `U`;
* `eq_of_dist_eq_zero`: if `μ` is bounded below, `d_b(x, y) = 0` forces `x = y`;
* `continuous_ofFinsler` (**Lema 9.1.8**): if moreover `μ` is reversible, every open set of `M`
  is open for `d_b`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace FinslerSeminormField

variable (μ : FinslerSeminormField E M)

/-- `μ` is **bounded below** on the chart `i` with constant `C` (*acotada inferiormente*,
Definición 9.1.3): `‖φ_{*x} v‖ ≤ C μ_x(v)` for every `x` in the domain of `φ`. -/
def IsBoundedBelowOn (i : atlas E M) (C : ℝ) : Prop :=
  ∀ x ∈ i.1.source, ∀ v : E, ‖tangentCoordChange (prefAtlas E x) i x v‖ ≤ C * μ ⟨x, v⟩

/-- `μ` is **bounded above** on the chart `i` with constant `m` (*acotada superiormente*,
Definición 9.1.3): `m μ_x(v) ≤ ‖φ_{*x} v‖` for every `x` in the domain of `φ`. -/
def IsBoundedAboveOn (i : atlas E M) (m : ℝ) : Prop :=
  ∀ x ∈ i.1.source, ∀ v : E, m * μ ⟨x, v⟩ ≤ ‖tangentCoordChange (prefAtlas E x) i x v‖

/-- `μ` is **bounded below**: every point has a chart where it is bounded below. -/
def IsBoundedBelow : Prop :=
  ∀ p : M, ∃ i : atlas E M, p ∈ i.1.source ∧ ∃ C > 0, μ.IsBoundedBelowOn i C

/-- `μ` is **bounded above** (a *weak Finsler manifold*, Observación 9.1.4). -/
def IsBoundedAbove : Prop :=
  ∀ p : M, ∃ i : atlas E M, p ∈ i.1.source ∧ ∃ m > 0, μ.IsBoundedAboveOn i m

/-- `μ` is **bounded** (a *strong Finsler manifold*, Observación 9.1.4): every point has a chart
where it is bounded above and below. -/
def IsBounded : Prop :=
  ∀ p : M, ∃ i : atlas E M, p ∈ i.1.source ∧
    (∃ C > 0, μ.IsBoundedBelowOn i C) ∧ ∃ m > 0, μ.IsBoundedAboveOn i m

theorem IsBounded.isBoundedBelow {μ : FinslerSeminormField E M} (h : μ.IsBounded) :
    μ.IsBoundedBelow := fun p ↦ by
  obtain ⟨i, hp, hC, -⟩ := h p
  exact ⟨i, hp, hC⟩

theorem IsBounded.isBoundedAbove {μ : FinslerSeminormField E M} (h : μ.IsBounded) :
    μ.IsBoundedAbove := fun p ↦ by
  obtain ⟨i, hp, -, hm⟩ := h p
  exact ⟨i, hp, hm⟩

end FinslerSeminormField

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

/-- **The integrated bound** (*Estructuras*, (9.2)): if `μ` is bounded below on the chart `i`
with constant `C`, a `C¹` curve which stays in the domain of `i` on `[s, t]` satisfies
`‖φ(γ t) − φ(γ s)‖ ≤ C L_b(γ|[s, t])`. -/
theorem norm_chart_sub_le [CompleteSpace E] {i : atlas E M} {C : ℝ}
    (hC : μ.toFinslerSeminormField.IsBoundedBelowOn i C) {γ : ℝ → M} (hγ : IsCkCurve E 1 γ)
    {s t : ℝ} (hst : s ≤ t) (hin : ∀ τ ∈ Icc s t, γ τ ∈ i.1.source) :
    ‖i.1 (γ t) - i.1 (γ s)‖ ≤ C * μ.length γ s t := by
  set c : ℝ → E := i.1 ∘ γ
  have hO : IsOpen (γ ⁻¹' i.1.source) := i.1.open_source.preimage hγ.1
  have hcO : ContDiffMBOn 1 c (γ ⁻¹' i.1.source) := hγ.2 i
  have hder : ∀ τ ∈ γ ⁻¹' i.1.source, HasDerivAt c (dMB c (τ, 1)) τ := by
    intro τ hτ
    have hd := hcO.hasDirDerivAt hτ (1 : ℝ)
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa [HasDirDerivAt] using hd
  have hlift : ∀ τ ∈ γ ⁻¹' i.1.source, dMB c (τ, 1) = liftCoord i (velocity E γ) τ :=
    fun τ hτ ↦ (liftCoord_velocity hγ i hτ).symm
  have hcont : ContinuousOn (fun τ ↦ dMB c (τ, 1)) (γ ⁻¹' i.1.source) := by
    have h0 : ContinuousOn (liftCoord i (velocity E γ)) (γ ⁻¹' i.1.source) :=
      ((isCkLift_velocity (k := 0) hγ).2 i).continuousOn
    exact h0.congr hlift
  have hIcc : Icc s t ⊆ γ ⁻¹' i.1.source := fun τ hτ ↦ hin τ hτ
  have hint : IntervalIntegrable (fun τ ↦ dMB c (τ, 1)) volume s t :=
    (hcont.mono (by rwa [uIcc_of_le hst])).intervalIntegrable
  have hftc : ∫ τ in s..t, dMB c (τ, 1) = c t - c s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ hτ ↦ hder τ (hIcc (by rwa [uIcc_of_le hst] at hτ))) hint
  have hbound : ∀ τ ∈ Icc s t, ‖dMB c (τ, 1)‖ ≤ C * μ.toFun (velocity E γ τ) := by
    intro τ hτ
    rw [hlift τ (hIcc hτ)]
    exact hC (γ τ) (hin τ hτ) _
  have hμ : Continuous fun τ ↦ μ.toFun (velocity E γ τ) := μ.continuous_velocity hγ
  calc ‖i.1 (γ t) - i.1 (γ s)‖ = ‖∫ τ in s..t, dMB c (τ, 1)‖ := by rw [hftc]; rfl
    _ ≤ ∫ τ in s..t, ‖dMB c (τ, 1)‖ := intervalIntegral.norm_integral_le_integral_norm hst
    _ ≤ ∫ τ in s..t, C * μ.toFun (velocity E γ τ) :=
        intervalIntegral.integral_mono_on hst hint.norm
          ((hμ.const_smul C).intervalIntegrable s t) hbound
    _ = C * μ.length γ s t := intervalIntegral.integral_const_mul _ _

/-! ### Leaving a chart costs length -/

section Exit

variable [CompleteSpace E] [T2Space M] {i : atlas E M} {C : ℝ}
  (hC : μ.toFinslerSeminormField.IsBoundedBelowOn i C) (hCpos : 0 < C) {x₀ : M} {r : ℝ}
  (hball : Metric.closedBall (i.1 x₀) r ⊆ i.1.target)
include hC hCpos hball

/-- **A `C¹` arc cannot leave the ball cheaply.** If `γ a` lies in the chart, at distance
`ρ < r` from `φ x₀`, then either `r ≤ ρ + C L_b(γ|[a, b])`, or `γ b` is in the chart with
`‖φ(γ b) − φ x₀‖ ≤ ρ + C L_b(γ|[a, b])`. -/
theorem arc_exit {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b)
    (ha : γ a ∈ i.1.source) (hρ : ‖i.1 (γ a) - i.1 x₀‖ < r) :
    r ≤ ‖i.1 (γ a) - i.1 x₀‖ + C * μ.length γ a b ∨
      (γ b ∈ i.1.source ∧
        ‖i.1 (γ b) - i.1 x₀‖ ≤ ‖i.1 (γ a) - i.1 x₀‖ + C * μ.length γ a b) := by
  set ρ := ‖i.1 (γ a) - i.1 x₀‖
  set W := i.1.source ∩ i.1 ⁻¹' Metric.ball (i.1 x₀) r
  have hW : IsOpen W := i.1.isOpen_inter_preimage Metric.isOpen_ball
  have hlen_nonneg : ∀ {s t : ℝ}, s ≤ t → 0 ≤ μ.length γ s t := fun h ↦ μ.length_nonneg γ h
  have hnorm : ∀ τ, a ≤ τ → (∀ σ ∈ Icc a τ, γ σ ∈ i.1.source) →
      ‖i.1 (γ τ) - i.1 x₀‖ ≤ ρ + C * μ.length γ a τ := by
    intro τ haτ hin
    have h1 := μ.norm_chart_sub_le hC hγ haτ hin
    calc ‖i.1 (γ τ) - i.1 x₀‖ ≤ ‖i.1 (γ τ) - i.1 (γ a)‖ + ρ := by
          simpa [ρ] using norm_sub_le_norm_sub_add_norm_sub (i.1 (γ τ)) (i.1 (γ a)) (i.1 x₀)
      _ ≤ ρ + C * μ.length γ a τ := by linarith
  by_cases hall : ∀ τ ∈ Icc a b, γ τ ∈ W
  · exact Or.inr ⟨(hall b (right_mem_Icc.2 hab)).1,
      hnorm b hab fun σ hσ ↦ (hall σ hσ).1⟩
  simp only [not_forall, exists_prop] at hall
  obtain ⟨τ₁, hτ₁, hτ₁W⟩ := hall
  set S := Icc a b ∩ γ ⁻¹' Wᶜ
  have hSc : IsClosed S := isClosed_Icc.inter (hW.isClosed_compl.preimage hγ.1)
  have hSne : S.Nonempty := ⟨τ₁, hτ₁, hτ₁W⟩
  have hSbdd : BddBelow S := ⟨a, fun τ h ↦ h.1.1⟩
  set t₀ := sInf S
  have ht₀S : t₀ ∈ S := hSc.csInf_mem hSne hSbdd
  have haW : γ a ∈ W := ⟨ha, by simpa [Metric.mem_ball, dist_eq_norm] using hρ⟩
  have hat₀ : a < t₀ := by
    refine lt_of_le_of_ne ht₀S.1.1 fun h ↦ ?_
    have := ht₀S.2
    rw [← h] at this
    exact this haW
  have hbefore : ∀ τ, a ≤ τ → τ < t₀ → γ τ ∈ W := by
    intro τ haτ hτt₀
    by_contra hτW
    have : t₀ ≤ τ := csInf_le hSbdd ⟨⟨haτ, hτt₀.le.trans ht₀S.1.2⟩, hτW⟩
    linarith
  by_cases hlen : r ≤ ρ + C * μ.length γ a t₀
  · left
    have h1 := μ.length_add hγ a t₀ b
    have h2 := hlen_nonneg ht₀S.1.2
    nlinarith
  exfalso
  simp only [not_le] at hlen
  set R := ρ + C * μ.length γ a t₀
  -- points before `t₀` stay in the closed ball of radius `R`
  have hin_ball : ∀ τ, a ≤ τ → τ < t₀ → ‖i.1 (γ τ) - i.1 x₀‖ ≤ R := by
    intro τ haτ hτt₀
    have h1 := hnorm τ haτ fun σ hσ ↦ (hbefore σ hσ.1 (hσ.2.trans_lt hτt₀)).1
    have h2 := μ.length_add hγ a τ t₀
    have h3 := hlen_nonneg hτt₀.le
    nlinarith
  -- a sequence increasing to `t₀`
  set τ : ℕ → ℝ := fun n ↦ t₀ - (t₀ - a) * (1 / ((n : ℝ) + 1))
  have hτa : ∀ n, a ≤ τ n := fun n ↦ by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h2 : 0 ≤ t₀ - a := by linarith
    simp only [τ]; nlinarith
  have hτt₀ : ∀ n, τ n < t₀ := fun n ↦ by
    have : 0 < (t₀ - a) * (1 / ((n : ℝ) + 1)) := mul_pos (by linarith) (by positivity)
    simp only [τ]; linarith
  have hτmono : Monotone τ := fun m n hmn ↦ by
    have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    simp only [τ]
    nlinarith [show (0 : ℝ) ≤ t₀ - a by linarith]
  have hτlim : Tendsto τ atTop (𝓝 t₀) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (t₀ - a)
    rw [mul_zero] at h
    simpa [τ] using (tendsto_const_nhds (x := t₀)).sub h
  -- the chart images form a Cauchy sequence
  set u : ℕ → E := fun n ↦ i.1 (γ (τ n))
  have hL : Continuous fun t ↦ μ.length γ a t :=
    intervalIntegral.continuous_primitive
      (fun _ _ ↦ (μ.continuous_velocity hγ).intervalIntegrable _ _) a
  have hLc : CauchySeq fun n ↦ μ.length γ a (τ n) :=
    ((hL.tendsto t₀).comp hτlim).cauchySeq
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff'] at hLc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hLc (ε / C) (div_pos hε hCpos)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hle : τ N ≤ τ n := hτmono hn
    have hin : ∀ σ ∈ Icc (τ N) (τ n), γ σ ∈ i.1.source := fun σ hσ ↦
      (hbefore σ ((hτa N).trans hσ.1) (hσ.2.trans_lt (hτt₀ n))).1
    have h1 := μ.norm_chart_sub_le hC hγ hle hin
    have h2 := μ.length_add hγ a (τ N) (τ n)
    have h3 := hN n hn
    rw [Real.dist_eq] at h3
    rw [dist_eq_norm]
    have h4 : μ.length γ (τ N) (τ n) < ε / C := by
      have := abs_lt.mp h3
      linarith [this.2]
    calc ‖u n - u N‖ ≤ C * μ.length γ (τ N) (τ n) := h1
      _ < C * (ε / C) := mul_lt_mul_of_pos_left h4 hCpos
      _ = ε := by field_simp
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hu
  have hzR : z ∈ Metric.closedBall (i.1 x₀) R :=
    Metric.isClosed_closedBall.mem_of_tendsto hz (Eventually.of_forall fun n ↦ by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hin_ball (τ n) (hτa n) (hτt₀ n))
  have hzT : z ∈ i.1.target := hball (Metric.closedBall_subset_closedBall hlen.le hzR)
  have hγz : Tendsto (fun n ↦ γ (τ n)) atTop (𝓝 (i.1.symm z)) := by
    have := ((i.1.continuousAt_symm hzT).tendsto).comp hz
    refine this.congr fun n ↦ ?_
    simp [u, i.1.left_inv (hbefore (τ n) (hτa n) (hτt₀ n)).1]
  have hγt₀ : Tendsto (fun n ↦ γ (τ n)) atTop (𝓝 (γ t₀)) := (hγ.1.tendsto t₀).comp hτlim
  have heq : γ t₀ = i.1.symm z := tendsto_nhds_unique hγt₀ hγz
  apply ht₀S.2
  refine ⟨by rw [heq]; exact i.1.map_target hzT, ?_⟩
  rw [mem_preimage, heq, i.1.right_inv hzT, Metric.mem_ball]
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp hzR) hlen

/-- **A chain of `C¹` arcs cannot leave the ball cheaply.** -/
theorem reach_exit {x y : M} {L : ℝ} (h : μ.Reach x y L) (hx : x ∈ i.1.source)
    (hρ : ‖i.1 x - i.1 x₀‖ < r) :
    r ≤ ‖i.1 x - i.1 x₀‖ + C * L ∨
      (y ∈ i.1.source ∧ ‖i.1 y - i.1 x₀‖ ≤ ‖i.1 x - i.1 x₀‖ + C * L) := by
  induction h with
  | refl x => exact Or.inr ⟨hx, by simp⟩
  | @cons γ a b y L hγ hab hrest ih =>
    have hL := hrest.nonneg
    have hlab := μ.length_nonneg γ hab
    rcases μ.arc_exit hC hCpos hball hγ hab hx hρ with h1 | ⟨hb, h1⟩
    · left; nlinarith
    · by_cases hb' : ‖i.1 (γ b) - i.1 x₀‖ < r
      · rcases ih hb hb' with h2 | ⟨hy, h2⟩
        · left; nlinarith
        · right; exact ⟨hy, by nlinarith⟩
      · left; simp only [not_lt] at hb'; nlinarith

end Exit

/-! ### The distance near a point: Lema 9.1.8 -/

variable [CompleteSpace E] [T2Space M]

/-- **Lema 9.1.8**: if `μ` is bounded below, every point `x₀` has a chart `φ` and constants
`C, r > 0` such that the points at `d_b`-distance `< r / C` from `x₀` lie in the domain of `φ`,
with `‖φ y − φ x₀‖ ≤ C d_b(x₀, y)`. -/
theorem exists_chart_norm_le_dist (hb : μ.toFinslerSeminormField.IsBoundedBelow) (x₀ : M) :
    ∃ i : atlas E M, x₀ ∈ i.1.source ∧ ∃ C > 0, ∃ r > 0, ∀ y : M,
      μ.dist x₀ y < ENNReal.ofReal (r / C) →
        y ∈ i.1.source ∧ ‖i.1 y - i.1 x₀‖ ≤ C * (μ.dist x₀ y).toReal := by
  obtain ⟨i, hx₀, C, hCpos, hC⟩ := hb x₀
  obtain ⟨r', hr', hr'T⟩ := Metric.isOpen_iff.mp i.1.open_target (i.1 x₀) (i.1.map_source hx₀)
  set r := r' / 2
  have hr : 0 < r := half_pos hr'
  have hball : Metric.closedBall (i.1 x₀) r ⊆ i.1.target :=
    (Metric.closedBall_subset_ball (half_lt_self hr')).trans hr'T
  refine ⟨i, hx₀, C, hCpos, r, hr, fun y hy ↦ ?_⟩
  set D := μ.dist x₀ y
  have hDtop : D ≠ ⊤ := ne_top_of_lt hy
  -- every chain of length `< r / C` ends in the chart, with the norm bound
  have hchain : ∀ L, μ.Reach x₀ y L → L < r / C →
      y ∈ i.1.source ∧ ‖i.1 y - i.1 x₀‖ ≤ C * L := by
    intro L hL hLr
    have hCL : C * L < r := by rwa [lt_div_iff₀' hCpos] at hLr
    rcases μ.reach_exit hC hCpos hball hL hx₀ (by simpa using hr) with h | h
    · simp at h; linarith
    · simpa using h
  -- chains of length close to `D`
  have hex : ∀ ε > 0, ∃ L, μ.Reach x₀ y L ∧ L < r / C ∧ L < D.toReal + ε := by
    intro ε hε
    have hlt : D < min (ENNReal.ofReal (r / C)) (ENNReal.ofReal (D.toReal + ε)) := by
      refine lt_min hy ?_
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le, ENNReal.ofReal_toReal hDtop]
      exact ENNReal.lt_add_right hDtop (by simpa using hε)
    obtain ⟨⟨L, hL⟩, hLlt⟩ := iInf_lt_iff.mp hlt
    have hL0 := hL.nonneg
    refine ⟨L, hL, ?_, ?_⟩
    · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL0).mp (hLlt.trans_le (min_le_left _ _))
    · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL0).mp (hLlt.trans_le (min_le_right _ _))
  obtain ⟨L₀, hL₀, hL₀r, -⟩ := hex 1 one_pos
  refine ⟨(hchain L₀ hL₀ hL₀r).1, ?_⟩
  refine le_of_forall_pos_lt_add fun δ hδ ↦ ?_
  obtain ⟨L, hL, hLr, hLD⟩ := hex (δ / (2 * C)) (by positivity)
  have h1 := (hchain L hL hLr).2
  calc ‖i.1 y - i.1 x₀‖ ≤ C * L := h1
    _ < C * (D.toReal + δ / (2 * C)) := mul_lt_mul_of_pos_left hLD hCpos
    _ = C * D.toReal + δ / 2 := by field_simp
    _ < C * D.toReal + δ := by linarith

/-- **`d_b` separates points** when `μ` is bounded below (Lema 9.1.8). -/
theorem eq_of_dist_eq_zero (hb : μ.toFinslerSeminormField.IsBoundedBelow) {x y : M}
    (h : μ.dist x y = 0) : x = y := by
  obtain ⟨i, hx, C, hC, r, hr, hball⟩ := μ.exists_chart_norm_le_dist hb x
  have hlt : μ.dist x y < ENNReal.ofReal (r / C) := by
    rw [h]; exact ENNReal.ofReal_pos.mpr (div_pos hr hC)
  obtain ⟨hy, hnorm⟩ := hball y hlt
  rw [h, ENNReal.toReal_zero, mul_zero] at hnorm
  have : i.1 y = i.1 x := sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)
  exact (i.1.injOn hx hy this.symm)

/-- **Lema 9.1.8: every open set of `M` is open for `d_b`** (for a reversible `μ` bounded below):
the identity `(M, d_b) → M` is continuous. -/
theorem continuous_ofFinsler (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    [hrev : Fact μ.IsReversible] : Continuous μ.ofFinsler := by
  rw [continuous_iff_continuousAt]
  intro p
  set x₀ : M := μ.ofFinsler p
  obtain ⟨i, hx₀, C, hC, r, hr, hball⟩ := μ.exists_chart_norm_le_dist hb x₀
  rw [ContinuousAt, (Metric.nhds_basis_eball (x := p)).tendsto_left_iff]
  intro U hU
  have hU' : i.1.symm ⁻¹' U ∈ 𝓝 (i.1 x₀) := by
    have := (i.1.continuousAt_symm (i.1.map_source hx₀)).preimage_mem_nhds
      (by rwa [i.1.left_inv hx₀])
    exact this
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU'
  refine ⟨ENNReal.ofReal (min (r / C) (ε / C)), ENNReal.ofReal_pos.mpr
    (lt_min (div_pos hr hC) (div_pos hε hC)), fun q hq ↦ ?_⟩
  set y : M := μ.ofFinsler q
  have hd : μ.dist x₀ y < ENNReal.ofReal (min (r / C) (ε / C)) := by
    have : edist q p = μ.dist y x₀ := rfl
    rw [Metric.mem_eball, this, μ.dist_comm hrev.out] at hq
    exact hq
  have hdr : μ.dist x₀ y < ENNReal.ofReal (r / C) :=
    hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  obtain ⟨hy, hnorm⟩ := hball y hdr
  have hdε : (μ.dist x₀ y).toReal < ε / C := by
    have h' := hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    exact ENNReal.toReal_lt_of_lt_ofReal h'
  have hyU : i.1 y ∈ Metric.ball (i.1 x₀) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖i.1 y - i.1 x₀‖ ≤ C * (μ.dist x₀ y).toReal := hnorm
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hdε hC
      _ = ε := by field_simp
  have := hεU hyU
  rwa [mem_preimage, i.1.left_inv hy] at this

/-! ### Upper bounds: segments in a chart (Estructuras, (9.3)) -/

section Upper

variable {i : atlas E M} {m : ℝ}

omit [CompleteSpace E] [T2Space M] in
/-- **The distance is bounded by the chart distance** (*Estructuras*, (9.3)): if `μ` is bounded
above on the chart `i` with constant `m > 0`, and the segment from `φ x` to `φ y` lies in
`φ(U)`, then `d_b(x, y) ≤ ‖φ y − φ x‖ / m`. The segment is reparametrized by
`Real.smoothTransition`, so that it is a `C¹` curve defined on all of `ℝ`. -/
theorem dist_le_norm_chart (hm : μ.toFinslerSeminormField.IsBoundedAboveOn i m) (hmpos : 0 < m)
    {x y : M} (hx : x ∈ i.1.source) (hy : y ∈ i.1.source)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, i.1 x + s • (i.1 y - i.1 x) ∈ i.1.target) :
    μ.dist x y ≤ ENNReal.ofReal (‖i.1 y - i.1 x‖ / m) := by
  set w := i.1 y - i.1 x
  set σ := Real.smoothTransition
  set c : ℝ → E := fun t ↦ i.1 x + σ t • w
  have hσ01 : ∀ t, σ t ∈ Icc (0 : ℝ) 1 := fun t ↦
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hcT : ∀ t, c t ∈ i.1.target := fun t ↦ hseg _ (hσ01 t)
  have hσd : ContDiff ℝ 1 σ := Real.smoothTransition.contDiff (n := 1)
  have hcd : ContDiff ℝ 1 c :=
    contDiff_const.add (ContDiff.smul (f := σ) (g := fun _ ↦ w) hσd contDiff_const)
  have hcc : Continuous c := hcd.continuous
  set γ : ℝ → M := fun t ↦ i.1.symm (c t)
  have hγ : IsCkCurve E 1 γ := by
    refine ⟨i.1.continuousOn_symm.comp_continuous hcc hcT, fun j ↦ ?_⟩
    set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
    have hT : IsOpen T := isOpen_transition_domain i j
    have hpre : γ ⁻¹' j.1.source = c ⁻¹' T := by
      ext t; simp [γ, T, hcT t]
    rw [hpre]
    have hc1 : ContDiffMBOn 1 c (c ⁻¹' T) :=
      ContDiffOn.contDiffMBOn (hT.preimage hcc) hcd.contDiffOn
    have := ContDiffMBOn.comp (g := j.1 ∘ i.1.symm) (f := c) (hT.preimage hcc) hT
      (smoothMBOn_transition' i j 1) hc1 (fun t ht ↦ ht)
    exact this
  have hγ0 : γ 0 = x := by simp [γ, c, σ, Real.smoothTransition.zero, i.1.left_inv hx]
  have hγ1 : γ 1 = y := by simp [γ, c, σ, Real.smoothTransition.one, w, i.1.left_inv hy]
  have hdist := μ.dist_le hγ zero_le_one
  rw [hγ0, hγ1] at hdist
  refine hdist.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the velocity in the chart is `σ'(t) w`
  have hderiv : ∀ t, HasDerivAt c (deriv σ t • w) t := fun t ↦
    (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt.smul_const
      w).const_add _
  have hdMB : ∀ t, dMB (i.1 ∘ γ) (t, 1) = deriv σ t • w := by
    intro t
    have hfun : i.1 ∘ γ = c := funext fun t ↦ i.1.right_inv (hcT t)
    rw [hfun]
    have hd : HasDirDerivAt c t 1 (deriv σ t • w) := by
      simpa [HasDirDerivAt] using (hderiv t).tendsto_slope_zero
    exact hd.dMB_eq
  have hσ'nonneg : ∀ t, 0 ≤ deriv σ t := fun t ↦ Real.smoothTransition.monotone.deriv_nonneg
  have hσ'cont : Continuous (deriv σ) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      μ.toFun (velocity E γ t) ≤ deriv σ t * ‖w‖ / m := by
    intro t _
    have hγt : γ t ∈ i.1.source := i.1.map_target (hcT t)
    have h1 := hm (γ t) hγt (velocity E γ t).2
    have h2 : tangentCoordChange (prefAtlas E (γ t)) i (γ t) (velocity E γ t).2 =
        dMB (i.1 ∘ γ) (t, 1) := liftCoord_velocity hγ i hγt
    rw [h2, hdMB, norm_smul, Real.norm_of_nonneg (hσ'nonneg t)] at h1
    have h1' : m * μ.toFun (velocity E γ t) ≤ deriv σ t * ‖w‖ := h1
    rw [le_div_iff₀ hmpos]
    linarith
  calc μ.length γ 0 1 ≤ ∫ t in (0 : ℝ)..1, deriv σ t * ‖w‖ / m :=
        intervalIntegral.integral_mono_on zero_le_one
          ((μ.continuous_velocity hγ).intervalIntegrable _ _)
          (((hσ'cont.mul continuous_const).div_const m).intervalIntegrable _ _) hbound
    _ = (∫ t in (0 : ℝ)..1, deriv σ t) * ‖w‖ / m := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]
    _ = ‖w‖ / m := by
        rw [intervalIntegral.integral_deriv_eq_sub
          (fun t _ ↦ (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t)
          (hσ'cont.intervalIntegrable _ _), Real.smoothTransition.one,
          Real.smoothTransition.zero, sub_zero, one_mul]

omit [CompleteSpace E] [T2Space M] in
/-- **For a weak Finsler manifold the topology of `d_b` is coarser than that of `M`**
(*Estructuras*, (9.3)): if `μ` is reversible and bounded above, the identity `M → (M, d_b)` is
continuous. -/
theorem continuous_toFinsler_of_isBoundedAbove (ha : μ.toFinslerSeminormField.IsBoundedAbove)
    [hrev : Fact μ.IsReversible] : Continuous μ.toFinsler := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨i, hx₀, m, hmpos, hm⟩ := ha x₀
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp i.1.open_target (i.1 x₀) (i.1.map_source hx₀)
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  obtain ⟨ρ, hρ0, hρpos, hρε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hρ : 0 < ρ := ENNReal.ofReal_pos.mp hρpos
  have hev : ∀ᶠ y in 𝓝 x₀, y ∈ i.1.source ∧ ‖i.1 y - i.1 x₀‖ < min r (m * ρ) := by
    have h1 := i.1.open_source.mem_nhds hx₀
    have h2 := (i.1.continuousAt hx₀).eventually
      (Metric.ball_mem_nhds (i.1 x₀) (lt_min hr (mul_pos hmpos hρ)))
    filter_upwards [h1, h2] with y hy hy2
    exact ⟨hy, by simpa [dist_eq_norm] using hy2⟩
  filter_upwards [hev] with y ⟨hy, hyn⟩
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, i.1 y + s • (i.1 x₀ - i.1 y) ∈ i.1.target := by
    intro s hs
    apply hrT
    rw [Metric.mem_ball, dist_eq_norm]
    have : i.1 y + s • (i.1 x₀ - i.1 y) - i.1 x₀ = (1 - s) • (i.1 y - i.1 x₀) := by module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith [hs.2])]
    calc (1 - s) * ‖i.1 y - i.1 x₀‖ ≤ 1 * ‖i.1 y - i.1 x₀‖ := by
          gcongr; linarith [hs.1]
      _ < r := by rw [one_mul]; exact hyn.trans_le (min_le_left _ _)
  have hd := μ.dist_le_norm_chart hm hmpos hy hx₀ hseg
  change μ.dist y x₀ < ε
  refine hd.trans_lt (lt_of_lt_of_le ?_ hρε.le)
  rw [ENNReal.ofReal_lt_ofReal_iff hρ, div_lt_iff₀ hmpos, norm_sub_rev]
  linarith [hyn.trans_le (min_le_right _ _)]

end Upper

/-- **Corolario 9.1.9: for a strong Finsler manifold the two topologies coincide.** If `μ` is
reversible and bounded (above and below), with a complete model and a Hausdorff manifold, the
identity of `M` is a homeomorphism between the manifold topology and the topology of `d_b`. -/
def homeomorphFinsler (hb : μ.toFinslerSeminormField.IsBounded) [Fact μ.IsReversible] :
    M ≃ₜ FinslerSpace μ where
  toFun := μ.toFinsler
  invFun := μ.ofFinsler
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := μ.continuous_toFinsler_of_isBoundedAbove hb.isBoundedAbove
  continuous_invFun := μ.continuous_ofFinsler hb.isBoundedBelow

end FinslerLengthStructure

end LCManifolds
