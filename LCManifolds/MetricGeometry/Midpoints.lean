/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.MetricGeometry.HopfRinow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Approximate midpoints and interior metric spaces

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 8,
§8.1 (Lema 8.1.9, Lema 8.1.10, Problemas 8.III and 8.IV).

Let `(X, d)` be a pseudometric space. We say that `X` has **approximate midpoints**
(`HasApproxMidpoints`) if for all `x, y` and `ε > 0` there is `z` with
`max (d(x, z), d(z, y)) ≤ d(x, y) / 2 + ε`, and that `X` satisfies the **ball condition**
(`HasBallCondition`) if, for `r₁, r₂ > 0` with `r₁ + r₂ ≤ d(x, y)`, the distance between the
closed balls `B̄_{r₁}(x)` and `B̄_{r₂}(y)` is at most `d(x, y) - r₁ - r₂`, that is, for every
`ε > 0` there are `p ∈ B̄_{r₁}(x)` and `q ∈ B̄_{r₂}(y)` with `d(p, q) ≤ d(x, y) - r₁ - r₂ + ε`.

## Main results

* `IsInterior.hasBallCondition`: an interior space satisfies the ball condition (Lema 8.1.10,
  first part);
* `HasBallCondition.hasApproxMidpoints`: the ball condition gives approximate midpoints
  (Problema 8.III);
* `HasApproxMidpoints.hasBallCondition`: approximate midpoints give the ball condition
  (Problema 8.IV), without any completeness assumption;
* `isInterior_of_approx_midpoint`: **a complete space with approximate midpoints is an interior
  space** (the converse part of Lema 8.1.10);
* `isInterior_iff_hasApproxMidpoints`, `isInterior_iff_hasBallCondition`: the resulting
  characterizations of complete interior spaces.

## Implementation notes

Given `x, y` with `δ = d(x, y)` and `ε > 0`, repeated choice of approximate midpoints with errors
`ε / 4ⁿ⁺¹` produces dyadic chains `Zₙ : ℕ → X` with `Zₙ 0 = x`, `Zₙ 2ⁿ = y`,
`Zₙ₊₁ (2j) = Zₙ j` and `d(Zₙ j, Zₙ (j + 1)) ≤ (δ + ε) / 2ⁿ` (`HasApproxMidpoints.exists_chain`);
this is the construction of the book, with the factors `∏ (1 + εₖ)` replaced by additive errors.
The chains alone give Problema 8.IV: take the points of index `⌊r₁ / c⌋` and `2ⁿ - ⌊r₂ / c⌋`, where
`c = (δ + ε) / 2ⁿ` is the step.

Instead of extending a Lipschitz map from the dyadic rationals to `[0, 1]` (Lema 8.1.9), the curve
is obtained as the pointwise limit of the step functions `fₙ t = Zₙ ⌊2ⁿ t⌋`: consecutive ones are
`(δ + ε) / 2ⁿ⁺¹`-close, so they converge by completeness, and the estimate
`d(fₙ s, fₙ t) ≤ (δ + ε) |s - t| + (δ + ε) / 2ⁿ` passes to the limit, which is therefore
`(δ + ε)`-Lipschitz, hence continuous and of length `≤ δ + ε`. Since `X` is only pseudometric, the
values of the limit at `0` and `1` are chosen to be `x` and `y`.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

noncomputable section

namespace LCManifolds

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Approximate midpoints and the ball condition -/

/-- `X` has **approximate midpoints**: for all `x, y` and `ε > 0` there is `z` with
`d(x, z) ≤ d(x, y) / 2 + ε` and `d(z, y) ≤ d(x, y) / 2 + ε`. -/
def HasApproxMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε > 0, ∃ z, dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε

/-- The **ball condition** of Lema 8.1.10: if `r₁, r₂ > 0` and `r₁ + r₂ ≤ d(x, y)`, then
`d(B̄_{r₁}(x), B̄_{r₂}(y)) ≤ d(x, y) - r₁ - r₂`, where the distance between two sets is the
infimum of the distances between their points. It is stated through the points that almost
realize the infimum. -/
def HasBallCondition (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (x y : X) (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ → r₁ + r₂ ≤ dist x y → ∀ ε > 0,
    ∃ p ∈ closedBall x r₁, ∃ q ∈ closedBall y r₂, dist p q ≤ dist x y - r₁ - r₂ + ε

/-- Interior spaces have approximate midpoints (Problema 8.III, through Lema 8.1.10). -/
theorem IsInterior.hasApproxMidpoints (h : IsInterior X) : HasApproxMidpoints X :=
  fun x y _ hε ↦ h.exists_approx_midpoint x y hε

/-- **The ball condition in interior spaces** (*Estructuras*, Lema 8.1.10, first part): if
`r₁, r₂ > 0` and `r₁ + r₂ ≤ d(x, y)`, then for every `ε > 0` there are `p ∈ B̄_{r₁}(x)` and
`q ∈ B̄_{r₂}(y)` with `d(p, q) ≤ d(x, y) - r₁ - r₂ + ε`. Take an approximate intermediate point
`p` at distance `r₁` from `x`, and then an approximate intermediate point `q` between `p` and `y`
at distance `r₂` from `y`. -/
theorem IsInterior.exists_dist_le_sub_sub (h : IsInterior X) {x y : X} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr : r₁ + r₂ ≤ dist x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ closedBall x r₁, ∃ q ∈ closedBall y r₂, dist p q ≤ dist x y - r₁ - r₂ + ε := by
  set η := min (ε / 4) (min r₁ r₂)
  have hη : 0 < η := lt_min (by positivity) (lt_min hr₁ hr₂)
  have hη1 : η ≤ ε / 4 := min_le_left _ _
  have hη2 : η ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p, hp1, hp2⟩ := h.exists_dist_le_add x y (a := r₁ - η) (b := dist x y - r₁ + η)
    (by linarith) (by linarith) (by ring) hη
  refine ⟨p, by rw [mem_closedBall, dist_comm]; linarith, ?_⟩
  by_cases hpy : dist p y ≤ r₂
  · exact ⟨p, hpy, by rw [dist_self]; linarith⟩
  replace hpy := not_le.mp hpy
  obtain ⟨q, hq1, hq2⟩ := h.exists_dist_le_add p y (a := dist p y - r₂ + η) (b := r₂ - η)
    (by linarith) (by linarith) (by ring) hη
  exact ⟨q, by rw [mem_closedBall]; linarith, by linarith⟩

/-- Interior spaces satisfy the ball condition (*Estructuras*, Lema 8.1.10, first part). -/
theorem IsInterior.hasBallCondition (h : IsInterior X) : HasBallCondition X :=
  fun _ _ _ _ hr₁ hr₂ hr _ hε ↦ h.exists_dist_le_sub_sub hr₁ hr₂ hr hε

/-- **The ball condition gives approximate midpoints** (*Estructuras*, Problema 8.III): apply it
with `r₁ = r₂ = d(x, y) / 2`. -/
theorem HasBallCondition.hasApproxMidpoints (h : HasBallCondition X) : HasApproxMidpoints X := by
  intro x y ε hε
  rcases (dist_nonneg (x := x) (y := y)).eq_or_lt with hd | hd
  · exact ⟨x, by rw [dist_self, ← hd]; linarith, by rw [← hd]; linarith⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := h x y (dist x y / 2) (dist x y / 2) (by positivity)
    (by positivity) (by linarith) ε hε
  rw [mem_closedBall] at hp hq
  refine ⟨p, by rw [dist_comm]; linarith, ?_⟩
  linarith [dist_triangle p q y]

/-! ### Dyadic chains -/

/-- The dyadic chains built from a choice `m n a b` of approximate midpoints of `a` and `b`:
`chain m x y 0` is `x` at `0` and `y` elsewhere, and `chain m x y (n + 1)` keeps the points of
`chain m x y n` at the even indices and inserts approximate midpoints at the odd ones. -/
private def chain (m : ℕ → X → X → X) (x y : X) : ℕ → ℕ → X
  | 0, j => if j = 0 then x else y
  | n + 1, j => if j % 2 = 0 then chain m x y n (j / 2)
      else m n (chain m x y n (j / 2)) (chain m x y n (j / 2 + 1))

omit [PseudoMetricSpace X] in
private theorem chain_zero (m : ℕ → X → X → X) (x y : X) (n : ℕ) : chain m x y n 0 = x := by
  induction n with
  | zero => simp [chain]
  | succ n ih => simp [chain, ih]

omit [PseudoMetricSpace X] in
private theorem chain_two_mul (m : ℕ → X → X → X) (x y : X) (n j : ℕ) :
    chain m x y (n + 1) (2 * j) = chain m x y n j := by
  simp [chain]

omit [PseudoMetricSpace X] in
private theorem chain_two_mul_add_one (m : ℕ → X → X → X) (x y : X) (n j : ℕ) :
    chain m x y (n + 1) (2 * j + 1) = m n (chain m x y n j) (chain m x y n (j + 1)) := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [chain, h1, h2]

omit [PseudoMetricSpace X] in
private theorem chain_two_pow (m : ℕ → X → X → X) (x y : X) (n : ℕ) :
    chain m x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [chain]
  | succ n ih => rw [pow_succ', chain_two_mul, ih]

/-- **Dyadic chains of approximate midpoints.** In a space with approximate midpoints, for
`x, y` and `ε > 0` there are chains `Zₙ : ℕ → X` with `Zₙ 0 = x`, `Zₙ 2ⁿ = y`,
`Zₙ₊₁ (2j) = Zₙ j` and steps `d(Zₙ j, Zₙ (j + 1)) ≤ (d(x, y) + ε) / 2ⁿ` (*Estructuras*, proof of
Lema 8.1.10). The midpoints of the `n`-th step are chosen with error `ε / 4ⁿ⁺¹`, and the steps
are bounded by `(d(x, y) + ε) / 2ⁿ - ε / 4ⁿ`. -/
theorem HasApproxMidpoints.exists_chain (h : HasApproxMidpoints X) (x y : X) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Z : ℕ → ℕ → X, (∀ n, Z n 0 = x) ∧ (∀ n, Z n (2 ^ n) = y) ∧
      (∀ n j, Z (n + 1) (2 * j) = Z n j) ∧
      ∀ n j, dist (Z n j) (Z n (j + 1)) ≤ (dist x y + ε) / 2 ^ n := by
  have hm : ∀ (n : ℕ) (a b : X), ∃ z, dist a z ≤ dist a b / 2 + ε / 4 ^ (n + 1) ∧
      dist z b ≤ dist a b / 2 + ε / 4 ^ (n + 1) := fun n a b ↦ h a b _ (by positivity)
  choose m hm1 hm2 using hm
  set D : ℕ → ℝ := fun n ↦ (dist x y + ε) / 2 ^ n - ε / 4 ^ n
  have hD : ∀ n, D n / 2 + ε / 4 ^ (n + 1) = D (n + 1) := fun n ↦ by
    simp only [D, pow_succ]; field_simp; ring
  have hstep : ∀ n j, dist (chain m x y n j) (chain m x y n (j + 1)) ≤ D n := by
    intro n
    induction n with
    | zero =>
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [chain, D]
      · simp [chain, D, hj.ne', dist_nonneg]
    | succ n ih =>
      intro j
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
      · rw [chain_two_mul, chain_two_mul_add_one, ← hD]
        linarith [hm1 n (chain m x y n k) (chain m x y n (k + 1)), ih k]
      · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, chain_two_mul, chain_two_mul_add_one,
          ← hD]
        linarith [hm2 n (chain m x y n k) (chain m x y n (k + 1)), ih k]
  refine ⟨chain m x y, chain_zero m x y, chain_two_pow m x y, chain_two_mul m x y,
    fun n j ↦ (hstep n j).trans ?_⟩
  have : 0 ≤ ε / 4 ^ n := by positivity
  linarith

/-- In a chain with steps `≤ c`, the points of indices `i, j` are `|i - j| c`-close. -/
theorem dist_le_of_dist_succ_le {Z : ℕ → X} {c : ℝ} (hZ : ∀ j, dist (Z j) (Z (j + 1)) ≤ c)
    (i j : ℕ) : dist (Z i) (Z j) ≤ |(i : ℝ) - j| * c := by
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm, abs_sub_comm]
    exact this j i (le_of_not_ge hij)
  refine (dist_le_Ico_sum_dist Z hij).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ c fun k _ ↦ hZ k).trans_eq ?_
  rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hij, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hij))]

/-- **Approximate midpoints give the ball condition** (*Estructuras*, Problema 8.IV), in any
pseudometric space. In a dyadic chain from `x` to `y` with step `c = (d(x, y) + ε / 2) / 2ⁿ`, take
the points of indices `⌊r₁ / c⌋` and `2ⁿ - ⌊r₂ / c⌋`; they are at distance
`≤ d(x, y) - r₁ - r₂ + ε / 2 + 2c`. -/
theorem HasApproxMidpoints.hasBallCondition (h : HasApproxMidpoints X) : HasBallCondition X := by
  intro x y r₁ r₂ hr₁ hr₂ hr ε hε
  obtain ⟨Z, hZ0, hZ1, -, hZd⟩ := h.exists_chain x y (ε := ε / 2) (by positivity)
  set C := dist x y + ε / 2 with hCd
  have hC : 0 < C := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 * C / ε) (one_lt_two (α := ℝ))
  set c := C / 2 ^ n
  have hc : 0 < c := by positivity
  have hcC : 2 ^ n * c = C := by simp only [c]; field_simp
  have hcε : c ≤ ε / 4 := by
    rw [div_lt_iff₀ hε] at hn
    simp only [c]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set i := ⌊r₁ / c⌋₊
  set k := ⌊r₂ / c⌋₊
  have hi1 : (i : ℝ) * c ≤ r₁ := (le_div_iff₀ hc).mp (Nat.floor_le (by positivity))
  have hi2 : r₁ < (i + 1) * c := (div_lt_iff₀ hc).mp (Nat.lt_floor_add_one _)
  have hk1 : (k : ℝ) * c ≤ r₂ := (le_div_iff₀ hc).mp (Nat.floor_le (by positivity))
  have hk2 : r₂ < (k + 1) * c := (div_lt_iff₀ hc).mp (Nat.lt_floor_add_one _)
  have hk : k ≤ 2 ^ n := by
    have : (k : ℝ) ≤ 2 ^ n := by
      by_contra hlt
      have := mul_lt_mul_of_pos_right (not_le.mp hlt) hc
      linarith [dist_nonneg (x := x) (y := y)]
    exact_mod_cast this
  have hj : ((2 ^ n - k : ℕ) : ℝ) = 2 ^ n - k := by rw [Nat.cast_sub hk]; push_cast; ring
  have hD := dist_le_of_dist_succ_le (c := c) (hZd n)
  refine ⟨Z n i, ?_, Z n (2 ^ n - k), ?_, ?_⟩
  · rw [mem_closedBall, ← hZ0 n]
    refine (hD i 0).trans ?_
    rw [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hi1
  · rw [mem_closedBall, ← hZ1 n]
    refine (hD _ _).trans ?_
    rw [hj, Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ) ^ n - k - 2 ^ n = -k by ring, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact hk1
  · refine (hD _ _).trans ?_
    rw [hj, ← abs_of_pos hc, ← abs_mul]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith

/-- Problemas 8.III and 8.IV: approximate midpoints are equivalent to the ball condition. -/
theorem hasApproxMidpoints_iff_hasBallCondition : HasApproxMidpoints X ↔ HasBallCondition X :=
  ⟨HasApproxMidpoints.hasBallCondition, HasBallCondition.hasApproxMidpoints⟩

/-! ### Complete spaces with approximate midpoints are interior -/

/-- `⌊2a⌋₊` is `2⌊a⌋₊` or `2⌊a⌋₊ + 1`. -/
private theorem floor_two_mul (a : ℝ) : ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ ∨ ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ + 1 := by
  rcases le_or_gt a 0 with ha | ha
  · left
    rw [Nat.floor_of_nonpos ha, Nat.floor_of_nonpos (by linarith)]
  have h1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha.le
  have h2 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
  by_cases hlt : 2 * a < 2 * ⌊a⌋₊ + 1
  · left
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith
  · right
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith

/-- `|⌊s⌋₊ - ⌊t⌋₊| ≤ |s - t| + 1`. -/
private theorem abs_floor_sub_floor_le (s t : ℝ) : |(⌊s⌋₊ : ℝ) - ⌊t⌋₊| ≤ |s - t| + 1 := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s]
    exact this t s (le_of_not_ge hst)
  have hmono : (⌊s⌋₊ : ℝ) ≤ ⌊t⌋₊ := Nat.cast_le.mpr (Nat.floor_le_floor hst)
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  rcases le_or_gt t 0 with ht | ht
  · rw [Nat.floor_of_nonpos ht, Nat.floor_of_nonpos (hst.trans ht)]
    simp only [Nat.cast_zero, sub_zero, neg_zero]
    linarith
  · linarith [Nat.floor_le ht.le, Nat.sub_one_lt_floor s]

/-- **Curves of almost minimal length from approximate midpoints** (*Estructuras*, proof of
Lema 8.1.10): in a complete space with approximate midpoints, for `x, y` and `ε > 0` there is a
continuous curve from `x` to `y` of length `≤ d(x, y) + ε`; it is `(d(x, y) + ε)`-Lipschitz on
`[0, 1]`. It is the pointwise limit of the step functions `t ↦ Zₙ ⌊2ⁿ t⌋` given by the dyadic
chains `HasApproxMidpoints.exists_chain`. -/
theorem HasApproxMidpoints.exists_rectPath_length_le [CompleteSpace X] (h : HasApproxMidpoints X)
    (x y : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : RectPath x y, p.length ≤ ENNReal.ofReal (dist x y + ε) := by
  obtain ⟨Z, hZ0, hZ1, hZ2, hZd⟩ := h.exists_chain x y hε
  set C := dist x y + ε
  have hC : 0 < C := by positivity
  set f : ℕ → ℝ → X := fun n t ↦ Z n ⌊t * 2 ^ n⌋₊
  have hstep : ∀ n t, dist (f n t) (f (n + 1) t) ≤ C / 2 / 2 ^ n := by
    intro n t
    have ht : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
    simp only [f, ht]
    rcases floor_two_mul (t * 2 ^ n) with h' | h'
    · rw [h', hZ2, dist_self]
      positivity
    · rw [h', ← hZ2]
      refine (hZd _ _).trans_eq ?_
      rw [pow_succ]
      ring
  have hlim : ∀ t, ∃ a, Tendsto (fun n ↦ f n t) atTop (𝓝 a) := fun t ↦
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (C := C) (hstep · t))
  choose g hg using hlim
  set γ : ℝ → X := fun t ↦ if t = 0 then x else if t = 1 then y else g t
  have hf0 : ∀ n, f n 0 = x := fun n ↦ by simp [f, hZ0]
  have hf1 : ∀ n, f n 1 = y := fun n ↦ by
    have : ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) := by push_cast; rfl
    simp only [f, one_mul, this, Nat.floor_natCast, hZ1]
  have hγ : ∀ t, Tendsto (fun n ↦ f n t) atTop (𝓝 (γ t)) := by
    intro t
    by_cases h0 : t = 0
    · simp only [γ, h0, ite_true, hf0]
      exact tendsto_const_nhds
    by_cases h1 : t = 1
    · simp only [γ, h1, one_ne_zero, ite_true, ite_false, hf1]
      exact tendsto_const_nhds
    simp only [γ, h0, h1, ite_false]
    exact hg t
  have hfγ : ∀ n t, dist (f n t) (γ t) ≤ C / 2 ^ n := fun n t ↦
    dist_le_of_le_geometric_two_of_tendsto (C := C) (hstep · t) (hγ t) n
  have hf : ∀ n s t, dist (f n s) (f n t) ≤ C * |s - t| + C / 2 ^ n := by
    intro n s t
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    refine (dist_le_of_dist_succ_le (hZd n) _ _).trans ?_
    have habs := abs_floor_sub_floor_le (s * 2 ^ n) (t * 2 ^ n)
    rw [← sub_mul, abs_mul, abs_of_pos h2] at habs
    calc |(⌊s * 2 ^ n⌋₊ : ℝ) - ⌊t * 2 ^ n⌋₊| * (C / 2 ^ n)
        ≤ (|s - t| * 2 ^ n + 1) * (C / 2 ^ n) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ = C * |s - t| + C / 2 ^ n := by field_simp
  have hlip : ∀ s t, dist (γ s) (γ t) ≤ C * |s - t| := by
    intro s t
    refine le_of_forall_pos_lt_add fun η hη ↦ ?_
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 * C / η) (one_lt_two (α := ℝ))
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have h3 : C / 2 ^ n + C / 2 ^ n + C / 2 ^ n < η := by
      rw [div_lt_iff₀ hη] at hn
      have : C / 2 ^ n + C / 2 ^ n + C / 2 ^ n = 3 * C / 2 ^ n := by ring
      rw [this, div_lt_iff₀ h2]
      linarith
    calc dist (γ s) (γ t) ≤ dist (γ s) (f n s) + dist (f n s) (f n t) + dist (f n t) (γ t) :=
          dist_triangle4 _ _ _ _
      _ ≤ C / 2 ^ n + (C * |s - t| + C / 2 ^ n) + C / 2 ^ n := by
          rw [dist_comm (γ s)]
          gcongr
          · exact hfγ n s
          · exact hf n s t
          · exact hfγ n t
      _ < C * |s - t| + η := by linarith
  have hL : LipschitzWith (Real.toNNReal C) γ := LipschitzWith.of_dist_le_mul fun s t ↦ by
    rw [Real.coe_toNNReal _ hC.le, Real.dist_eq]
    exact hlip s t
  let p : RectPath x y :=
    { toFun := γ
      a := 0
      b := 1
      le := zero_le_one
      continuousOn := hL.continuous.continuousOn
      source := by simp [γ]
      target := by simp [γ] }
  refine ⟨p, ?_⟩
  have := (hL.lipschitzOnWith (s := Icc (0 : ℝ) 1)).comp_eVariationOn_le (g := id)
    (s := Icc (0 : ℝ) 1) (mapsTo_id _)
  change eVariationOn γ (Icc 0 1) ≤ _
  rw [Function.comp_id, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at this
  exact this

/-- **A complete space with approximate midpoints is an interior space** (*Estructuras*,
Lema 8.1.10, converse part, through Problema 8.III): if for all `x, y` and `ε > 0` there is `z`
with `max (d(x, z), d(z, y)) ≤ d(x, y) / 2 + ε`, then `d = d_ℓ`. -/
theorem isInterior_of_approx_midpoint [CompleteSpace X]
    (h : ∀ x y : X, ∀ ε > 0, ∃ z, dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε) :
    IsInterior X := by
  intro x y
  refine le_antisymm ?_ (edist_le_lengthDist x y)
  rw [edist_dist]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨p, hp⟩ := HasApproxMidpoints.exists_rectPath_length_le h x y (ε := ε)
    (by exact_mod_cast hε)
  refine (lengthDist_le p).trans (hp.trans_eq ?_)
  rw [ENNReal.ofReal_add dist_nonneg (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]

/-- A complete space with approximate midpoints is an interior space. -/
theorem HasApproxMidpoints.isInterior [CompleteSpace X] (h : HasApproxMidpoints X) :
    IsInterior X :=
  isInterior_of_approx_midpoint h

/-- **A complete space satisfying the ball condition is an interior space** (*Estructuras*,
Lema 8.1.10, converse part). -/
theorem HasBallCondition.isInterior [CompleteSpace X] (h : HasBallCondition X) : IsInterior X :=
  h.hasApproxMidpoints.isInterior

/-- A complete space is interior iff it has approximate midpoints (*Estructuras*, Lema 8.1.10 and
Problema 8.III). -/
theorem isInterior_iff_hasApproxMidpoints [CompleteSpace X] :
    IsInterior X ↔ HasApproxMidpoints X :=
  ⟨IsInterior.hasApproxMidpoints, HasApproxMidpoints.isInterior⟩

/-- **Lema 8.1.10**: a complete space is interior iff it satisfies the ball condition. -/
theorem isInterior_iff_hasBallCondition [CompleteSpace X] : IsInterior X ↔ HasBallCondition X :=
  ⟨IsInterior.hasBallCondition, HasBallCondition.isInterior⟩

end LCManifolds
