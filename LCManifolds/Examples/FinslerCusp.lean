/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Metric.Finsler

/-!
# A Finsler length structure on `ℝ²` that is not a Finsler metric

This example shows that the two continuity conditions of `LCManifolds.Metric.Finsler` are really
different, already on `ℝ²` (with the sup norm). Let
`β (x, y) = max (0, x² - |y|) / (x² + |y|)` (and `β 0 = 0`), and
`μ_p (v) = ‖v‖ + β(p) |v₂|`.

* Each `μ_p` is a reversible Finsler norm (`CuspFinsler.isNondegenerate`,
  `CuspFinsler.isReversible`).
* `β` equals `1` on the `x`-axis minus the origin and `0` at the origin, so `μ` is **not
  continuous on the tangent bundle** at `(0, e₂)`: it is not a Finsler metric
  (`CuspFinsler.not_continuous`).
* `μ` **is continuous along every `C¹` curve** `γ`: it is a Finsler length structure
  (`CuspFinsler.lengthStructure`). Away from the origin `β` is continuous. If `γ(t₀) = 0` and
  `γ̇₂(t₀) ≠ 0`, then near `t₀` the curve leaves the cusp `{|y| < x²}` where `β ≠ 0`, because
  `|γ₂ t| ≥ c |t - t₀|` while `γ₁(t)² = O(|t - t₀|²)`. If `γ̇₂(t₀) = 0`, then
  `0 ≤ β(γ) |γ̇₂| ≤ |γ̇₂| → 0`.

So the phenomenon is not infinite dimensional: a `C¹` curve through `p` only sees the pairs
`(p, v)` that are compatible with the way it approaches `p`, and the pairs `((1/n, 0), e₂)`,
which converge in `TM` to `(0, e₂)`, are not of this kind. The natural examples in infinite
dimensions are the quotient metrics of homogeneous spaces (Larotonda, Forum Math. 31 (2019),
Lemma 3.19).
-/

open Set Filter Bundle Asymptotics
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

namespace CuspFinsler

/-- The plane `ℝ²`, with the sup norm. -/
abbrev P : Type := ℝ × ℝ

/-- The cusp weight `β (x, y) = max (0, x² - |y|) / (x² + |y|)`, supported in the cusp
`{|y| < x²}`; at the origin the quotient is `0 / 0 = 0`. -/
def β (p : P) : ℝ := max 0 (p.1 ^ 2 - |p.2|) / (p.1 ^ 2 + |p.2|)

theorem β_nonneg (p : P) : 0 ≤ β p := div_nonneg (le_max_left _ _) (by positivity)

theorem β_le_one (p : P) : β p ≤ 1 := by
  refine div_le_one_of_le₀ (max_le (by positivity) ?_) (by positivity)
  linarith [abs_nonneg p.2]

@[simp] theorem β_zero : β 0 = 0 := by simp [β]

theorem β_axis {t : ℝ} (ht : t ≠ 0) : β (t, 0) = 1 := by
  have : 0 < t ^ 2 := by positivity
  simp [β, max_eq_right this.le, this.ne']

theorem β_eq_zero {p : P} (hp : p.1 ^ 2 ≤ |p.2|) : β p = 0 := by
  simp [β, max_eq_left (sub_nonpos.mpr hp)]

theorem continuousAt_β {p : P} (hp : p ≠ 0) : ContinuousAt β p := by
  have hden : p.1 ^ 2 + |p.2| ≠ 0 := by
    intro h
    have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, abs_nonneg p.2]
    have h2 : p.2 = 0 := by
      rw [h1] at h
      simpa using h
    exact hp (Prod.ext h1 h2)
  unfold β
  fun_prop (disch := exact hden)

/-! ### The field of Finsler norms -/

/-- `μ_p (v) = ‖v‖ + β(p) |v₂|`, as a function on the tangent bundle of `ℝ²`. -/
def μ (q : TangentBundle P P) : ℝ := ‖(show P from q.2)‖ + β q.1 * |(show P from q.2).2|

theorem μ_mk (x v : P) : μ ⟨x, v⟩ = ‖v‖ + β x * |v.2| := rfl

/-- The field of Finsler norms `μ_p (v) = ‖v‖ + β(p) |v₂|`. -/
def field : FinslerSeminormField P P where
  toFun := μ
  nonneg' q := add_nonneg (norm_nonneg _) (mul_nonneg (β_nonneg _) (abs_nonneg _))
  add_le' x v w := by
    simp only [μ_mk, Prod.snd_add]
    have h1 := norm_add_le v w
    have h2 : β x * |v.2 + w.2| ≤ β x * (|v.2| + |w.2|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (β_nonneg x)
    nlinarith
  smul_eq' x c hc v := by
    simp only [μ_mk, Prod.smul_snd, smul_eq_mul, norm_smul, Real.norm_of_nonneg hc, abs_mul,
      abs_of_nonneg hc]
    ring
  continuous_fiber' x := by
    simp only [μ_mk]
    fun_prop

theorem isNondegenerate : field.IsNondegenerate := by
  intro x v hv
  change μ ⟨x, v⟩ = 0 at hv
  rw [μ_mk] at hv
  have := mul_nonneg (β_nonneg x) (abs_nonneg v.2)
  exact norm_eq_zero.mp (by linarith [norm_nonneg v])

theorem isReversible : field.IsReversible := by
  intro x v
  change μ ⟨x, -v⟩ = μ ⟨x, v⟩
  simp [μ_mk]

/-! ### `μ` is not continuous on the tangent bundle -/

/-- The chart of the tangent bundle of the model space. -/
def Φ : OpenPartialHomeomorph (TangentBundle P P) (P × P) :=
  tangentChart ⟨chartAt P (0 : P), chart_mem_atlas P _⟩ (chartAt P (0 : P))

theorem μ_Φ_symm (q : P × P) : μ (Φ.symm q) = ‖q.2‖ + β q.1 * |q.2.2| := by
  have h : ((Φ.symm q).2 : P) = q.2 := by
    rw [Φ, tangentChart_symm_snd]
    change dMB (fun z : P ↦ z) (q.1, q.2) = q.2
    exact ((ContinuousLinearMap.id ℝ P).hasDirDerivAt _ _).dMB_eq
  have h' : (Φ.symm q).proj = q.1 := tangentChart_symm_proj _ _ q
  simp only [μ, h, h']

/-- **`μ` is not a Finsler metric**: it is not continuous on the tangent bundle at `(0, e₂)`. -/
theorem not_continuous : ¬ Continuous μ := by
  intro hμ
  have hΦ : Continuous Φ.symm := by
    rw [← continuousOn_univ]
    refine Φ.continuousOn_symm.mono fun q _ ↦ ?_
    rw [Φ, mem_tangentChart_target]
    exact ⟨mem_univ _, mem_univ _⟩
  set h : ℝ → ℝ := fun t ↦ μ (Φ.symm ((t, 0), (0, 1)))
  have hh : Continuous h := hμ.comp (hΦ.comp (by fun_prop))
  have hval : ∀ t, h t = 1 + β (t, 0) := fun t ↦ by
    simp only [h, μ_Φ_symm]
    simp [Prod.norm_def]
  have h0 : h 0 = 1 := by
    rw [hval, show ((0 : ℝ), (0 : ℝ)) = (0 : P) from rfl, β_zero]
    norm_num
  have hlim : Tendsto h (𝓝[≠] 0) (𝓝 2) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hval, β_axis ht]
    norm_num
  have := tendsto_nhds_unique hlim ((hh.tendsto 0).mono_left nhdsWithin_le_nhds)
  rw [h0] at this
  norm_num at this

/-! ### `μ` is continuous along every `C¹` curve -/

/-- For the model space, the velocity of a curve is its derivative. -/
theorem velocity_eq (γ : ℝ → P) (t : ℝ) :
    velocity P γ t = ⟨γ t, dMB γ (t, 1)⟩ := rfl

/-- Near a time where `γ` passes through the origin with `γ̇₂ ≠ 0`, the curve is outside the
cusp `{|y| < x²}`. -/
theorem eventually_outside_cusp {γ : ℝ → P} {t₀ : ℝ} {D : P} (hD : HasDerivAt γ D t₀)
    (h0 : γ t₀ = 0) (hc : D.2 ≠ 0) : ∀ᶠ t in 𝓝 t₀, (γ t).1 ^ 2 ≤ |(γ t).2| := by
  set c := |D.2| with hc_def
  have hcpos : 0 < c := abs_pos.mpr hc
  set K := ‖D‖ + c
  have hKpos : 0 < K := by positivity
  have ho := hasDerivAt_iff_isLittleO.mp hD
  have hb := ho.bound (half_pos hcpos)
  have hball : ∀ᶠ t in 𝓝 t₀, |t - t₀| ≤ c / (2 * K ^ 2) := by
    have : (0 : ℝ) < c / (2 * K ^ 2) := by positivity
    filter_upwards [Metric.closedBall_mem_nhds t₀ this] with t ht
    simpa [Real.dist_eq] using ht
  filter_upwards [hb, hball] with t ht htb
  simp only [h0, sub_zero, Real.norm_eq_abs] at ht
  -- componentwise bounds
  have h2 : |(γ t).2 - (t - t₀) * D.2| ≤ c / 2 * |t - t₀| :=
    le_trans (by simpa using norm_snd_le (γ t - (t - t₀) • D)) ht
  have h1 : |(γ t).1 - (t - t₀) * D.1| ≤ c / 2 * |t - t₀| :=
    le_trans (by simpa using norm_fst_le (γ t - (t - t₀) • D)) ht
  have hD1 : |D.1| ≤ ‖D‖ := by simpa using norm_fst_le D
  have hlow : c / 2 * |t - t₀| ≤ |(γ t).2| := by
    have : |(t - t₀) * D.2| ≤ |(γ t).2| + |(γ t).2 - (t - t₀) * D.2| := by
      calc |(t - t₀) * D.2| = |(γ t).2 - ((γ t).2 - (t - t₀) * D.2)| := by ring_nf
        _ ≤ |(γ t).2| + |(γ t).2 - (t - t₀) * D.2| := abs_sub _ _
    rw [abs_mul] at this
    nlinarith [abs_nonneg (t - t₀)]
  have hup : |(γ t).1| ≤ K * |t - t₀| := by
    have : |(γ t).1| ≤ |(t - t₀) * D.1| + |(γ t).1 - (t - t₀) * D.1| := by
      calc |(γ t).1| = |(t - t₀) * D.1 + ((γ t).1 - (t - t₀) * D.1)| := by ring_nf
        _ ≤ |(t - t₀) * D.1| + |(γ t).1 - (t - t₀) * D.1| := abs_add_le _ _
    rw [abs_mul] at this
    have : |t - t₀| * |D.1| ≤ |t - t₀| * ‖D‖ :=
      mul_le_mul_of_nonneg_left hD1 (abs_nonneg _)
    nlinarith [abs_nonneg (t - t₀)]
  have hsq : (γ t).1 ^ 2 ≤ K ^ 2 * |t - t₀| ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hup 2
  have : K ^ 2 * |t - t₀| ^ 2 ≤ c / 2 * |t - t₀| := by
    have hK2 : 0 < K ^ 2 := by positivity
    have : K ^ 2 * |t - t₀| ≤ c / 2 := by
      calc K ^ 2 * |t - t₀| ≤ K ^ 2 * (c / (2 * K ^ 2)) :=
            mul_le_mul_of_nonneg_left htb hK2.le
        _ = c / 2 := by field_simp
    nlinarith [abs_nonneg (t - t₀)]
  linarith

/-- **`μ` is a Finsler length structure**: it is continuous along every `C¹` curve. -/
def lengthStructure : FinslerLengthStructure P P where
  toFinslerSeminormField := field
  continuous_velocity' γ hγ := by
    -- the curve is `C¹` in the (identity) chart
    have hc : ContDiffMBOn 1 γ univ := hγ.2 ⟨chartAt P (0 : P), chart_mem_atlas P _⟩
    set D : ℝ → P := fun t ↦ dMB γ (t, 1)
    have hDc : Continuous D := by
      have h := hc.2.2.continuousOn
      rw [univ_prod_univ, continuousOn_univ] at h
      exact h.comp (by fun_prop)
    have hder : ∀ t, HasDerivAt γ (D t) t := fun t ↦ by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have := hc.2.1 t (mem_univ t) 1
      simpa [HasDirDerivAt] using this
    have hfun : (fun t ↦ field.toFun (velocity P γ t)) =
        fun t ↦ ‖D t‖ + β (γ t) * |(D t).2| := rfl
    rw [hfun]
    refine (continuous_norm.comp hDc).add ?_
    rw [continuous_iff_continuousAt]
    intro t₀
    by_cases hp : γ t₀ = 0
    · -- through the origin: the term tends to `0 = β 0 * |·|`
      have hval : β (γ t₀) * |(D t₀).2| = 0 := by rw [hp, β_zero, zero_mul]
      rw [ContinuousAt, hval]
      by_cases hc2 : (D t₀).2 = 0
      · have hlim : Tendsto (fun t ↦ |(D t).2|) (𝓝 t₀) (𝓝 0) := by
          have := ((continuous_abs.comp (continuous_snd.comp hDc)).tendsto t₀)
          simp only [Function.comp_apply, hc2, abs_zero] at this
          exact this
        refine squeeze_zero (fun t ↦ mul_nonneg (β_nonneg _) (abs_nonneg _)) (fun t ↦ ?_) hlim
        exact mul_le_of_le_one_left (abs_nonneg _) (β_le_one _)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_outside_cusp (hder t₀) hp hc2] with t ht
        rw [β_eq_zero ht, zero_mul]
    · exact ((continuousAt_β hp).comp hγ.1.continuousAt).mul
        (continuous_abs.comp (continuous_snd.comp hDc)).continuousAt

/-- **The two notions differ**: `μ` is a Finsler length structure but not a Finsler metric. -/
theorem lengthStructure_not_finslerMetric :
    ¬ ∃ g : FinslerMetric P P, g.toFun = lengthStructure.toFun := by
  rintro ⟨g, hg⟩
  have : Continuous lengthStructure.toFun := hg ▸ g.continuous'
  exact not_continuous this

end CuspFinsler

end LCManifolds
