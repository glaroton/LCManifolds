/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Examples.Subspace

/-!
# Counterexample: `c₀ ⊆ ℓ^∞` is embedded but not split (Phillips' lemma)

References: R. S. Phillips, *On linear transformations*, Trans. Amer. Math. Soc. 48 (1940);
R. Whitley, *Projecting m onto c₀*, Amer. Math. Monthly 73 (1966).

We realize `ℓ^∞` as the Banach space `ℕ →ᵇ ℝ` of bounded sequences and `c₀` as the closed
subspace of sequences tending to `0` (`LCManifolds.Phillips.c0`).

* **Phillips' lemma** (`Phillips.not_closedComplemented_c0`): there is no continuous linear
  projection of `ℓ^∞` onto `c₀`.
* Hence `c₀` is an embedded submanifold of `ℓ^∞` that is not split
  (`Phillips.isEmbeddedSubmanifold_c0`, `Phillips.not_isSplitSubmanifold_c0`), and the linear
  inclusion `c₀ → ℓ^∞` is an immersion (closed range, topological isomorphism onto it) that is not
  a split immersion (`Phillips.isImmersion_c0`, `Phillips.not_isSplitImmersion_c0`). This
  separates `IsImmersion` from `IsSplitImmersion` already between Banach spaces.

**Proof (Whitley).** There is an uncountable family `(N_A)` of infinite subsets of `ℕ`, any two of
which have finite intersection: index the finite binary words by `ℕ`, and let `N_A` be the set of
indices of the initial segments of the indicator of `A ⊆ ℕ` (`Phillips.N`). Let `χ_A ∈ ℓ^∞` be the
indicator of `N_A`; it is not in `c₀`.

1. A continuous functional `f` on `ℓ^∞` that vanishes on `c₀` satisfies `|f x| ≤ ‖f‖` as soon as
   `|x k| ≤ 1` for all but finitely many `k`: modify `x` on a finite set
   (`Phillips.abs_le_of_eventually`).
2. For such an `f`, only countably many `A` have `f χ_A ≠ 0`. If `|f χ_A| > 1/m` for `A` in a
   finite set `F`, then `x = Σ_{A ∈ F} ± χ_A` has `|x k| ≤ 1` off the finite set where two of the
   `N_A` meet, and `f x = Σ_{A ∈ F} |f χ_A| > #F / m`; so `#F < m ‖f‖`
   (`Phillips.countable_ne_zero`).
3. If `P` were a projection onto `c₀`, apply 2 to the coordinates `f_n = e_n ∘ (1 - P)`. Some `A`
   avoids the countable union of the exceptional sets, so `(1 - P) χ_A = 0` and `χ_A = P χ_A ∈ c₀`,
   a contradiction.
-/

open Set Filter Function BoundedContinuousFunction
open scoped Topology BoundedContinuousFunction
open LCAnalysis

noncomputable section

namespace LCManifolds

namespace Phillips

/-- `ℓ^∞`, realized as the bounded sequences `ℕ →ᵇ ℝ`. -/
abbrev Linf : Type := ℕ →ᵇ ℝ

/-- `c₀`: the sequences tending to `0`. -/
def c0 : Submodule ℝ Linf where
  carrier := {x | Tendsto (⇑x) cofinite (𝓝 0)}
  add_mem' {x y} hx hy := by
    change Tendsto (fun k ↦ (x + y) k) _ _
    simpa using hx.add hy
  zero_mem' := by
    change Tendsto (fun k ↦ (0 : Linf) k) _ _
    simp
  smul_mem' c x hx := by
    change Tendsto (fun k ↦ (c • x) k) _ _
    simpa using hx.const_smul c

theorem mem_c0 {x : Linf} : x ∈ c0 ↔ Tendsto (⇑x) cofinite (𝓝 0) := Iff.rfl

/-- `c₀` is closed in `ℓ^∞`. -/
theorem isClosed_c0 : IsClosed (c0 : Set Linf) := by
  refine isClosed_of_closure_subset fun x hx ↦ ?_
  rw [SetLike.mem_coe, mem_c0, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.mp (mem_c0.mp hy) (ε / 2) (half_pos hε)] with k hk
  have h1 := (x - y).norm_coe_le_norm k
  rw [← dist_eq_norm] at h1
  simp only [FunLike.coe_sub, Pi.sub_apply, Real.dist_eq, Real.norm_eq_abs, sub_zero] at hk h1 ⊢
  calc |x k| ≤ |x k - y k| + |y k| := by
        simpa using abs_add_le (x k - y k) (y k)
    _ < ε := by linarith

/-! ### Step 1: functionals vanishing on `c₀` -/

/-- A functional vanishing on `c₀` only sees a sequence outside a finite set: if `|x k| ≤ 1` for
all but finitely many `k`, then `|f x| ≤ ‖f‖`. -/
theorem abs_le_of_eventually {f : Linf →L[ℝ] ℝ} (hf : ∀ x ∈ c0, f x = 0) {x : Linf}
    (hx : ∀ᶠ k in cofinite, |x k| ≤ 1) : |f x| ≤ ‖f‖ := by
  classical
  set B := {k | ¬ |x k| ≤ 1}
  let y : Linf := ofNormedAddCommGroupDiscrete (fun k ↦ if k ∈ B then 0 else x k) 1 fun k ↦ by
    by_cases hk : k ∈ B
    · simp [hk]
    · simp only [hk, ite_false, Real.norm_eq_abs]
      simpa [B] using hk
  have hy : ‖y‖ ≤ 1 := by
    refine (norm_le zero_le_one).mpr fun k ↦ ?_
    by_cases hk : k ∈ B
    · simp [y, hk]
    · simp only [y, coe_ofNormedAddCommGroupDiscrete, hk, ite_false, Real.norm_eq_abs]
      simpa [B] using hk
  have hxy : x - y ∈ c0 := by
    rw [mem_c0]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with k hk
    have : k ∉ B := by simpa [B] using hk
    simp [y, this]
  have hfx : f x = f y := by
    have := hf _ hxy
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [hfx, ← Real.norm_eq_abs]
  calc ‖f y‖ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
    _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg f)
    _ = ‖f‖ := mul_one _

/-! ### An uncountable almost disjoint family of subsets of `ℕ` -/

attribute [local instance] Classical.propDecidable

/-- The initial segment of length `n` of the indicator of `A`, as a binary word. -/
def word (A : Set ℕ) (n : ℕ) : List Bool := (List.range n).map fun i ↦ decide (i ∈ A)

/-- The index of the initial segment of length `n`. -/
def code (A : Set ℕ) (n : ℕ) : ℕ := Encodable.encode (word A n)

/-- `N_A`: the indices of the initial segments of the indicator of `A`. -/
def N (A : Set ℕ) : Set ℕ := range (code A)

theorem length_word (A : Set ℕ) (n : ℕ) : (word A n).length = n := by simp [word]

theorem code_eq_code {A B : Set ℕ} {n m : ℕ} (h : code A n = code B m) :
    n = m ∧ ∀ i < n, (i ∈ A ↔ i ∈ B) := by
  have hw : word A n = word B m := Encodable.encode_injective h
  have hnm : n = m := by rw [← length_word A n, ← length_word B m, hw]
  subst hnm
  refine ⟨rfl, fun i hi ↦ ?_⟩
  have := (List.map_inj_left.mp hw) i (List.mem_range.mpr hi)
  simpa using this

theorem infinite_N (A : Set ℕ) : (N A).Infinite :=
  infinite_range_of_injective fun _ _ h ↦ (code_eq_code h).1

/-- Two different `N_A` meet in a finite set. -/
theorem finite_N_inter {A B : Set ℕ} (hAB : A ≠ B) : (N A ∩ N B).Finite := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
    by_contra h
    push Not at h
    exact hAB (Set.ext h)
  refine ((finite_Iic i₀).image (code A)).subset ?_
  rintro k ⟨⟨n, rfl⟩, ⟨m, hm⟩⟩
  refine ⟨n, ?_, rfl⟩
  by_contra hn
  exact hi₀ ((code_eq_code hm.symm).2 i₀ (not_le.mp hn))

theorem not_countable_univ : ¬ (univ : Set (Set ℕ)).Countable := by
  intro h
  have := countable_univ_iff.mp h
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set ℕ)
  exact cantor_surjective f hf

/-- The indicator `χ_A` of `N_A`, as an element of `ℓ^∞`. -/
def ind (A : Set ℕ) : Linf :=
  ofNormedAddCommGroupDiscrete ((N A).indicator 1) 1 fun k ↦ by
    by_cases hk : k ∈ N A <;> simp [hk]

theorem ind_apply (A : Set ℕ) (k : ℕ) : ind A k = if k ∈ N A then 1 else 0 := by
  simp [ind, Set.indicator_apply]

theorem ind_not_mem_c0 (A : Set ℕ) : ind A ∉ c0 := by
  intro h
  have hev := (mem_c0.mp h).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine infinite_N A ((eventually_cofinite.mp hev).subset fun k hk ↦ ?_)
  simp [ind_apply, hk]

/-! ### Step 2: countably many `χ_A` are seen by a functional vanishing on `c₀` -/

theorem finite_lt_abs {f : Linf →L[ℝ] ℝ} (hf : ∀ x ∈ c0, f x = 0) (m : ℕ) :
    {A : Set ℕ | 1 / ((m : ℝ) + 1) < |f (ind A)|}.Finite := by
  by_contra hinf
  set K := ⌈((m : ℝ) + 1) * ‖f‖⌉₊ + 1
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf K
  set a : Set ℕ → ℝ := fun A ↦ f (ind A)
  set ε : Set ℕ → ℝ := fun A ↦ if 0 ≤ a A then 1 else -1
  set x : Linf := ∑ A ∈ F, ε A • ind A
  have hεa : ∀ A, ε A * a A = |a A| := fun A ↦ by
    by_cases h : 0 ≤ a A
    · simp [ε, h, abs_of_nonneg h]
    · simp [ε, h, abs_of_neg (not_le.mp h)]
  have hεabs : ∀ A, |ε A| = 1 := fun A ↦ by by_cases h : 0 ≤ a A <;> simp [ε, h]
  -- `f x = Σ |f χ_A|`
  have hfx : f x = ∑ A ∈ F, |a A| := by
    simp only [x, map_sum, map_smul, smul_eq_mul, hεa, a]
  -- `|x k| ≤ 1` off the finite set where two of the `N_A` meet
  have hev : ∀ᶠ k in cofinite, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ (k ∈ N A ∧ k ∈ N B) := by
    simp only [eventually_all_finset]
    intro A _ B _
    by_cases hAB : A = B
    · exact Eventually.of_forall fun _ h ↦ absurd hAB h
    · refine eventually_cofinite.mpr ((finite_N_inter hAB).subset fun k hk ↦ ?_)
      simp only [mem_ofPred_eq, not_imp, not_not] at hk
      exact hk.2
  have hx : ∀ᶠ k in cofinite, |x k| ≤ 1 := by
    filter_upwards [hev] with k hk
    have hxk : x k = ∑ A ∈ F, ε A * (if k ∈ N A then 1 else 0) := by
      simp [x, ind_apply]
    have hcard : (F.filter fun A ↦ k ∈ N A).card ≤ 1 :=
      Finset.card_le_one.mpr fun A hA B hB ↦ by
        by_contra hAB
        simp only [Finset.mem_filter] at hA hB
        exact hk A hA.1 B hB.1 hAB ⟨hA.2, hB.2⟩
    rw [hxk]
    calc |∑ A ∈ F, ε A * (if k ∈ N A then 1 else 0)|
        ≤ ∑ A ∈ F, |ε A * (if k ∈ N A then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ A ∈ F, (if k ∈ N A then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun A _ ↦ ?_
          by_cases h : k ∈ N A <;> simp [h, hεabs]
      _ = ((F.filter fun A ↦ k ∈ N A).card : ℝ) := by rw [Finset.sum_boole]
      _ ≤ 1 := by exact_mod_cast hcard
  have hbound := abs_le_of_eventually hf hx
  rw [hfx, abs_of_nonneg (Finset.sum_nonneg fun A _ ↦ abs_nonneg _)] at hbound
  have hlow : (K : ℝ) * (1 / ((m : ℝ) + 1)) ≤ ∑ A ∈ F, |a A| := by
    have := Finset.card_nsmul_le_sum F (fun A ↦ |a A|) (1 / ((m : ℝ) + 1))
      fun A hA ↦ (hFsub hA).le
    rwa [hFcard, nsmul_eq_mul] at this
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hK : ((m : ℝ) + 1) * ‖f‖ < K := by
    have := Nat.le_ceil (((m : ℝ) + 1) * ‖f‖)
    push_cast [K]
    linarith
  have : (K : ℝ) * (1 / ((m : ℝ) + 1)) ≤ ‖f‖ := hlow.trans hbound
  rw [mul_one_div, div_le_iff₀ hm] at this
  linarith

/-- **Whitley's lemma**: a continuous functional on `ℓ^∞` vanishing on `c₀` vanishes on all but
countably many `χ_A`. -/
theorem countable_ne_zero {f : Linf →L[ℝ] ℝ} (hf : ∀ x ∈ c0, f x = 0) :
    {A : Set ℕ | f (ind A) ≠ 0}.Countable := by
  have : {A : Set ℕ | f (ind A) ≠ 0} = ⋃ m : ℕ, {A | 1 / ((m : ℝ) + 1) < |f (ind A)|} := by
    ext A
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact exists_nat_one_div_lt (abs_pos.mpr h)
    · rintro ⟨m, hm⟩ h
      rw [h, abs_zero] at hm
      exact absurd hm (not_lt.mpr (by positivity))
  rw [this]
  exact countable_iUnion fun m ↦ (finite_lt_abs hf m).countable

/-! ### Step 3: Phillips' lemma -/

/-- **Phillips' lemma**: `c₀` is not complemented in `ℓ^∞`. -/
theorem not_closedComplemented_c0 : ¬ c0.ClosedComplemented := by
  rintro ⟨P, hP⟩
  set Q : Linf →L[ℝ] Linf := ContinuousLinearMap.id ℝ Linf - c0.subtypeL.comp P
  have hQ : ∀ x ∈ c0, Q x = 0 := fun x hx ↦ by
    simp [Q, hP ⟨x, hx⟩]
  set g : ℕ → Linf →L[ℝ] ℝ := fun n ↦ (evalCLM ℝ n).comp Q
  have hcount : (⋃ n, {A : Set ℕ | g n (ind A) ≠ 0}).Countable :=
    countable_iUnion fun n ↦ countable_ne_zero fun x hx ↦ by simp [g, hQ x hx]
  obtain ⟨A, hA⟩ : ∃ A, A ∉ ⋃ n, {A : Set ℕ | g n (ind A) ≠ 0} := by
    by_contra h
    push Not at h
    exact not_countable_univ (hcount.mono fun A _ ↦ h A)
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hA
  have hQA : Q (ind A) = 0 := by
    ext n
    simpa [g] using hA n
  have hmem : ind A ∈ c0 := by
    have : ind A = (P (ind A) : Linf) := by
      simpa [Q, sub_eq_zero] using hQA
    rw [this]
    exact (P (ind A)).2
  exact ind_not_mem_c0 A hmem

/-! ### Consequences for submanifolds and immersions -/

/-- `c₀` is an embedded submanifold of `ℓ^∞` (a closed subspace). -/
theorem isEmbeddedSubmanifold_c0 : IsEmbeddedSubmanifold (c0 : Set Linf) c0 :=
  isEmbeddedSubmanifold_subspace isClosed_c0

/-- **`c₀` is not a split submanifold of `ℓ^∞`** (with model `c₀`). -/
theorem not_isSplitSubmanifold_c0 : ¬ IsSplitSubmanifold (c0 : Set Linf) c0 :=
  fun h ↦ not_closedComplemented_c0 h.closedComplemented

/-- **The inclusion `c₀ → ℓ^∞` is an immersion**: its differential is a topological isomorphism
onto the closed subspace `c₀`. -/
theorem isImmersion_c0 : IsImmersion c0 Linf c0.subtypeL :=
  isImmersion_subtypeL isClosed_c0

/-- **The inclusion `c₀ → ℓ^∞` is not a split immersion** (Phillips' lemma). -/
theorem not_isSplitImmersion_c0 : ¬ IsSplitImmersion c0 Linf c0.subtypeL :=
  fun h ↦ not_closedComplemented_c0 (isSplitImmersion_subtypeL_iff.mp h)

end Phillips

end LCManifolds
