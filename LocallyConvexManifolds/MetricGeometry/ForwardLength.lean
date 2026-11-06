/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.MetricGeometry.AsymmDist
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.IntermediateValue

/-!
# Forward lengths of curves in asymmetric spaces

Reference: A. C. G. Mennucci, *On asymmetric distances*, Anal. Geom. Metr. Spaces 1 (2013),
200–231, §1.1, §2.2 and §3.2–3.4; the asymmetric counterpart of G. Larotonda, *Estructuras
geométricas para las variedades de Banach*, Cap. 8, §8.1 (see `LengthMetric.lean` and
`HopfRinow.lean` for the symmetric theory).

Let `(X, b)` be an asymmetric pseudo-(extended) metric space (`AsymmPseudoEMetricSpace`, see
`AsymmDist.lean`), with the topology of the symmetrized distance `d = max (b, b̄)`, where
`b̄(x, y) = b(y, x)` is the conjugate distance. The **forward length** of a curve
`γ : [a, b] → X` is the total variation of Mennucci, (1.1), taken with forward sums:
`sup Σ b(γ tᵢ, γ tᵢ₊₁)` over the partitions `a ≤ t₀ ≤ ⋯ ≤ tₙ ≤ b`. It is in general different
from the forward length of the reversed curve (Mennucci, Remark 3.5).

## Main definitions and results

* `fwdVar f s`, `bwdVar f s`: the forward and backward variations of `f` on `s`, with the
  basic API (`fwdVar.sum_le`, `fwdVar.mono`, `fwdVar.bdist_le`, `fwdVar.eq_of_eqOn`,
  `fwdVar.subsingleton`), additivity (`fwdVar.union`, `fwdVar.Icc_add_Icc`,
  `fwdVar.Icc_add_Icc'`), invariance under monotone reparametrizations
  (`fwdVar.comp_eq_of_monotoneOn`, Mennucci, Prop. 2.7), the comparison with the variation of the
  symmetrized distance (`fwdVar_le_eVariationOn`) and reversal (`fwdVar_comp_neg`: reversing the
  curve exchanges `b` and `b̄`, Mennucci, Remark 3.3);
* `fwdVar.continuousOn_Icc`, `fwdVar.continuousOn_toReal_Icc`: **continuity of the running
  length** `t ↦ ℓ(t) = fwdVar γ (Icc a t)` of a continuous curve of finite forward length
  (Mennucci, Prop. 3.9), and `fwdVar.bdist_le_ofReal_sub`: `b(γ u, γ v) ≤ ℓ(v) - ℓ(u)`
  (Mennucci, (3.5));
* `FwdPath x y`: curves from `x` to `y`, continuous for the symmetrized topology, with
  `FwdPath.length`, `FwdPath.const`, `FwdPath.concat` and `FwdPath.length_concat`;
* `fwdLengthDist`: the induced asymmetric distance `b_g(x, y) = inf ℓ(γ)` (Mennucci, §3.4), with
  `fwdLengthDist_self`, `fwdLengthDist_triangle` and `b ≤ b_g` (`bdist_le_fwdLengthDist`,
  Mennucci, Prop. 3.10, (3.6));
* `IsFwdInterior X`: `b = b_g`, that is, `X` is g-intrinsic (Mennucci, Def. 3.16), with
  `IsFwdInterior.exists_fwdPath` and approximate intermediate points
  (`IsFwdInterior.exists_bdist_le_add`, `IsFwdInterior.exists_bdist_toReal_le_add`);
* `FwdPath.exists_lipschitz_reparam`: a curve of finite forward length `ℓ` has a
  reparametrization `η` on `[0, 1]` with `b(η u, η v) ≤ ℓ (v - u)` for `u ≤ v`.

## Implementation notes

* Mathlib's `eVariationOn` uses the backward sums `Σ edist (f uᵢ₊₁) (f uᵢ)`; for an asymmetric
  distance the order matters, and `fwdVar` uses the forward sums `Σ b(f uᵢ, f uᵢ₊₁)`.
* The additivity is proved by splitting a sequence `u` at the junction point `x` through
  `min (uᵢ, x)` and `max (uᵢ, x)`, which needs only the triangle inequality in the forward
  direction.
* For the continuity of the running length we follow the idea of Mennucci, Appendix B.2: if `γ`
  is continuous from the right at `a`, a partition of `[a, b]` starting at `a` can be modified by
  inserting a point `y` close to `a`, at the cost of `b(γ a, γ y)`, which is small; so the
  forward variation on `[a, b]` is the supremum of those on `[y, b]`, `y > a`
  (`fwdVar.Icc_eq_iSup_Icc_right`), and symmetrically on the left
  (`fwdVar.Icc_eq_iSup_Icc_left`). Only `b ≤ d` is used, so continuity for the symmetrized
  topology is what is needed.
* The reparametrization `η` of `FwdPath.exists_lipschitz_reparam` controls only the forward
  distances `b(η u, η v)`, `u ≤ v`; it need not be continuous for the symmetrized topology.
-/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Manifolds

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {X : Type*} [AsymmPseudoEMetricSpace X]

/-! ### Forward and backward variation -/

/-- The **forward variation** of `f` on `s`: the supremum, over the finite increasing sequences
`u₀ ≤ ⋯ ≤ uₙ` in `s`, of the forward sums `Σ b(f uᵢ, f uᵢ₊₁)`. Note the order of the arguments
of `bdist`: the curve travels from `f uᵢ` to `f uᵢ₊₁`. -/
def fwdVar (f : α → X) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, bdist (f (p.2.1 i)) (f (p.2.1 (i + 1)))

/-- The **backward variation** of `f` on `s`: as `fwdVar`, with the backward sums
`Σ b(f uᵢ₊₁, f uᵢ)`, that is, the forward variation for the conjugate distance
`(x, y) ↦ b(y, x)`. -/
def bwdVar (f : α → X) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, bdist (f (p.2.1 (i + 1))) (f (p.2.1 i))

namespace fwdVar

theorem sum_le {f : α → X} {s : Set α} {n : ℕ} {u : ℕ → α} (hu : Monotone u)
    (us : ∀ i, u i ∈ s) :
    ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1))) ≤ fwdVar f s :=
  le_iSup_of_le (⟨n, u, hu, us⟩ : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s }) le_rfl

/-- A sequence that is only monotone on `{0, …, n}` and lies in `s` there also gives a lower bound
for the forward variation. -/
theorem sum_le_of_monotoneOn_Iic {f : α → X} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1))) ≤ fwdVar f s := by
  set v : ℕ → α := fun i ↦ u (min i n)
  have hv : Monotone v := fun i j hij ↦
    hu (mem_Iic.2 (min_le_right _ _)) (mem_Iic.2 (min_le_right _ _)) (min_le_min hij le_rfl)
  have vs : ∀ i, v i ∈ s := fun i ↦ us _ (min_le_right _ _)
  calc ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1)))
      = ∑ i ∈ Finset.range n, bdist (f (v i)) (f (v (i + 1))) := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have := Finset.mem_range.mp hi
        simp only [v, min_eq_left this.le, min_eq_left (Nat.succ_le_of_lt this)]
    _ ≤ fwdVar f s := sum_le hv vs

theorem mono (f : α → X) {s t : Set α} (hst : t ⊆ s) : fwdVar f t ≤ fwdVar f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  exact sum_le hu fun i ↦ hst (ut i)

theorem eq_of_eqOn {f f' : α → X} {s : Set α} (h : EqOn f f' s) : fwdVar f s = fwdVar f' s := by
  unfold fwdVar
  congr 1 with p : 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h (p.2.2.2 i), h (p.2.2.2 (i + 1))]

/-- The trivial partition: for `x ≤ y` in `s`, `b(f x, f y)` is bounded by the forward
variation. -/
theorem bdist_le (f : α → X) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
    bdist (f x) (f y) ≤ fwdVar f s := by
  set u : ℕ → α := fun n ↦ if n = 0 then x else y
  have hu : Monotone u := monotone_nat_of_le_succ fun
    | 0 => by simpa [u] using hxy
    | (_ + 1) => by simp [u]
  have us : ∀ i, u i ∈ s := fun
    | 0 => by simpa [u] using hx
    | (_ + 1) => by simpa [u] using hy
  simpa [u] using sum_le (f := f) (n := 1) hu us

@[simp]
protected theorem subsingleton (f : α → X) {s : Set α} (hs : s.Subsingleton) :
    fwdVar f s = 0 := by
  refine le_antisymm (iSup_le ?_) bot_le
  rintro ⟨n, u, hu, us⟩
  refine (Finset.sum_eq_zero fun i _ ↦ ?_).le
  dsimp only
  rw [hs (us i) (us (i + 1)), bdist_self]

/-- Every monotone sequence can be replaced by a strictly monotone one (on `{0, …, m}`) with the
same values in `s`, the same last point and the same forward sum. -/
theorem exists_strictMonoOn (f : α → X) {s : Set α} {u : ℕ → α} (hu : Monotone u)
    (us : ∀ i, u i ∈ s) (n : ℕ) :
    ∃ (m : ℕ) (v : ℕ → α), StrictMonoOn v (Iic m) ∧ (∀ i ≤ m, v i ∈ s) ∧ v m = u n ∧
      ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1))) =
        ∑ i ∈ Finset.range m, bdist (f (v i)) (f (v (i + 1))) := by
  induction n with
  | zero =>
    refine ⟨0, u, fun i hi j hj hij ↦ ?_, fun i _ ↦ us i, rfl, by simp⟩
    simp only [mem_Iic, nonpos_iff_eq_zero] at hi hj
    omega
  | succ n ih =>
    obtain ⟨m, v, hv, vs, hvm, hsum⟩ := ih
    rcases (hu (Nat.le_succ n)).eq_or_lt with heq | hlt
    · refine ⟨m, v, hv, vs, hvm.trans heq, ?_⟩
      rw [Finset.sum_range_succ, ← heq, bdist_self, add_zero, hsum]
    · refine ⟨m + 1, fun i ↦ if i ≤ m then v i else u (n + 1), ?_, ?_, by simp, ?_⟩
      · intro i hi j hj hij
        simp only [mem_Iic] at hi hj
        have hi' : i ≤ m := by omega
        simp only [ite_eq_left hi']
        by_cases hjm : j ≤ m
        · simp only [ite_eq_left hjm]
          exact hv (mem_Iic.2 hi') (mem_Iic.2 hjm) hij
        · simp only [ite_eq_right hjm]
          refine (hv.monotoneOn (mem_Iic.2 hi') (mem_Iic.2 le_rfl) hi').trans_lt ?_
          rw [hvm]
          exact hlt
      · intro i hi
        dsimp only
        split_ifs with h
        exacts [vs i h, us _]
      · rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum]
        congr 1
        · refine Finset.sum_congr rfl fun i hi ↦ ?_
          have := Finset.mem_range.mp hi
          simp only [ite_eq_left this.le, ite_eq_left (Nat.succ_le_of_lt this)]
        · simp [hvm]

/-- To bound the forward variation it suffices to bound the forward sums along strictly
monotone sequences. -/
theorem le_of_strictMonoOn {f : α → X} {s : Set α} {c : ℝ≥0∞}
    (h : ∀ (m : ℕ) (v : ℕ → α), StrictMonoOn v (Iic m) → (∀ i ≤ m, v i ∈ s) →
      ∑ i ∈ Finset.range m, bdist (f (v i)) (f (v (i + 1))) ≤ c) :
    fwdVar f s ≤ c := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  obtain ⟨m, v, hv, vs, -, hsum⟩ := exists_strictMonoOn f hu us n
  rw [hsum]
  exact h m v hv vs

/-- If `s` lies to the left of `t`, the forward variations on `s` and on `t` add up to at most the
forward variation on `s ∪ t`. -/
theorem add_le_union (f : α → X) {s t : Set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    fwdVar f s + fwdVar f t ≤ fwdVar f (s ∪ t) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  have : Nonempty { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s } :=
    ⟨⟨fun _ ↦ x₀, monotone_const, fun _ ↦ hx₀⟩⟩
  have : Nonempty { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ t } :=
    ⟨⟨fun _ ↦ y₀, monotone_const, fun _ ↦ hy₀⟩⟩
  refine ENNReal.iSup_add_iSup_le ?_
  rintro ⟨n, u, hu, us⟩ ⟨m, v, hv, vt⟩
  set w : ℕ → α := fun i ↦ if i ≤ n then u i else v (i - (n + 1))
  have hw : Monotone w := by
    refine monotone_nat_of_le_succ fun i ↦ ?_
    simp only [w]
    split_ifs with h1 h2 h2
    · exact hu (Nat.le_succ i)
    · exact h _ (us i) _ (vt _)
    · omega
    · exact hv (by omega)
  have hwst : ∀ i, w i ∈ s ∪ t := fun i ↦ by
    simp only [w]
    split_ifs
    exacts [Or.inl (us i), Or.inr (vt _)]
  calc ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1))) +
        ∑ i ∈ Finset.range m, bdist (f (v i)) (f (v (i + 1)))
      = ∑ i ∈ Finset.range n, bdist (f (w i)) (f (w (i + 1))) +
        ∑ i ∈ Finset.range m, bdist (f (w (n + 1 + i))) (f (w (n + 1 + i + 1))) := by
        congr 1
        · refine Finset.sum_congr rfl fun i hi ↦ ?_
          have hi := Finset.mem_range.mp hi
          simp only [w, ite_eq_left hi.le, ite_eq_left (Nat.succ_le_of_lt hi)]
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [w, ite_eq_right (by omega : ¬ n + 1 + i ≤ n),
            ite_eq_right (by omega : ¬ n + 1 + i + 1 ≤ n)]
          rw [show n + 1 + i - (n + 1) = i by omega, show n + 1 + i + 1 - (n + 1) = i + 1 by omega]
    _ ≤ ∑ i ∈ Finset.range (n + 1 + m), bdist (f (w i)) (f (w (i + 1))) := by
        rw [Finset.sum_range_add, Finset.sum_range_succ]
        gcongr
        exact le_self_add
    _ ≤ fwdVar f (s ∪ t) := sum_le hw hwst

/-- If `x` is the greatest element of `s` and the least element of `t`, the forward variation
on `s ∪ t` is at most the sum of the forward variations: split every sequence at `x`, through
`min (uᵢ, x)` and `max (uᵢ, x)`. -/
theorem union_le (f : α → X) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    fwdVar f (s ∪ t) ≤ fwdVar f s + fwdVar f t := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ust⟩
  have hs' : ∀ i, min (u i) x ∈ s := fun i ↦ by
    rcases ust i with h | h
    · rw [min_eq_left (hs.2 h)]; exact h
    · rw [min_eq_right (ht.2 h)]; exact hs.1
  have ht' : ∀ i, max (u i) x ∈ t := fun i ↦ by
    rcases ust i with h | h
    · rw [max_eq_right (hs.2 h)]; exact ht.1
    · rw [max_eq_left (ht.2 h)]; exact h
  calc ∑ i ∈ Finset.range n, bdist (f (u i)) (f (u (i + 1)))
      ≤ ∑ i ∈ Finset.range n, (bdist (f (min (u i) x)) (f (min (u (i + 1)) x)) +
          bdist (f (max (u i) x)) (f (max (u (i + 1)) x))) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hi := hu (Nat.le_succ i)
        rcases le_total (u (i + 1)) x with h1 | h1
        · rw [min_eq_left h1, min_eq_left (hi.trans h1), max_eq_right h1,
            max_eq_right (hi.trans h1), bdist_self, add_zero]
        · rcases le_total (u i) x with h2 | h2
          · rw [min_eq_left h2, min_eq_right h1, max_eq_right h2, max_eq_left h1]
            exact bdist_triangle _ _ _
          · rw [min_eq_right h2, min_eq_right h1, max_eq_left h2, max_eq_left h1, bdist_self,
              zero_add]
    _ = ∑ i ∈ Finset.range n, bdist (f (min (u i) x)) (f (min (u (i + 1)) x)) +
          ∑ i ∈ Finset.range n, bdist (f (max (u i) x)) (f (max (u (i + 1)) x)) :=
        Finset.sum_add_distrib
    _ ≤ fwdVar f s + fwdVar f t :=
        add_le_add (sum_le (fun i j h ↦ min_le_min (hu h) le_rfl) hs')
          (sum_le (fun i j h ↦ max_le_max (hu h) le_rfl) ht')

/-- If `x` is the greatest element of `s` and the least element of `t`, the forward variation
on `s ∪ t` is the sum of the forward variations. -/
theorem union (f : α → X) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    fwdVar f (s ∪ t) = fwdVar f s + fwdVar f t :=
  le_antisymm (union_le f hs ht) (add_le_union f fun _ ha _ hb ↦ (hs.2 ha).trans (ht.2 hb))

/-- **Additivity** of the forward variation (relative to a set `s`). -/
theorem Icc_add_Icc (f : α → X) {s : Set α} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c)
    (hb : b ∈ s) :
    fwdVar f (s ∩ Icc a b) + fwdVar f (s ∩ Icc b c) = fwdVar f (s ∩ Icc a c) := by
  have A : IsGreatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]

/-- **Additivity** of the forward variation on intervals: `ℓ[a, b] + ℓ[b, c] = ℓ[a, c]`. -/
theorem Icc_add_Icc' (f : α → X) {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    fwdVar f (Icc a b) + fwdVar f (Icc b c) = fwdVar f (Icc a c) := by
  rw [← union f (isGreatest_Icc hab) (isLeast_Icc hbc), Icc_union_Icc_eq_Icc hab hbc]

theorem comp_le_of_monotoneOn (f : α → X) {s : Set α} {t : Set β} (φ : β → α)
    (hφ : MonotoneOn φ t) (φst : MapsTo φ t s) : fwdVar (f ∘ φ) t ≤ fwdVar f s :=
  iSup_le fun ⟨n, u, hu, ut⟩ ↦
    le_iSup_of_le (⟨n, φ ∘ u, fun x y xy ↦ hφ (ut x) (ut y) (hu xy), fun i ↦ φst (ut i)⟩ :
      ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s }) le_rfl

/-- **Invariance under monotone reparametrizations** (Mennucci, Prop. 2.7). -/
theorem comp_eq_of_monotoneOn (f : α → X) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t) :
    fwdVar (f ∘ φ) t = fwdVar f (φ '' t) := by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : MonotoneOn ψ (φ '' t) := Function.monotoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change fwdVar (f ∘ id) (φ '' t) ≤ fwdVar (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_monotoneOn (f ∘ φ) ψ hψ ψts

/-- An antitone reparametrization turns the forward variation into (at most) the backward
variation. -/
theorem comp_le_bwdVar_of_antitoneOn (f : α → X) {s : Set α} {t : Set β} (φ : β → α)
    (hφ : AntitoneOn φ t) (φst : MapsTo φ t s) : fwdVar (f ∘ φ) t ≤ bwdVar f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
  refine (Finset.sum_congr rfl fun x hx ↦ ?_).trans_le <| le_iSup_of_le
    (⟨n, fun i ↦ φ (u (n - i)), fun x y xy ↦ hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i ↦ φst (ut _)⟩ : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s }) le_rfl
  rw [Finset.mem_range] at hx
  dsimp only [Function.comp_apply]
  rw [show n - 1 - x = n - (x + 1) by omega, show n - (x + 1) + 1 = n - x by omega]

end fwdVar

namespace bwdVar

/-- An antitone reparametrization turns the backward variation into (at most) the forward
variation. -/
theorem comp_le_fwdVar_of_antitoneOn (f : α → X) {s : Set α} {t : Set β} (φ : β → α)
    (hφ : AntitoneOn φ t) (φst : MapsTo φ t s) : bwdVar (f ∘ φ) t ≤ fwdVar f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
  refine (Finset.sum_congr rfl fun x hx ↦ ?_).trans_le <| le_iSup_of_le
    (⟨n, fun i ↦ φ (u (n - i)), fun x y xy ↦ hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i ↦ φst (ut _)⟩ : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s }) le_rfl
  rw [Finset.mem_range] at hx
  dsimp only [Function.comp_apply]
  rw [show n - 1 - x = n - (x + 1) by omega, show n - (x + 1) + 1 = n - x by omega]

end bwdVar

/-- The forward variation is bounded by the total variation for the symmetrized distance
`d = max (b, b̄)`. -/
theorem fwdVar_le_eVariationOn (f : α → X) (s : Set α) : fwdVar f s ≤ eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  exact (Finset.sum_le_sum fun i _ ↦ bdist_le_edist' _ _).trans (eVariationOn.sum_le hu us)

/-- The backward variation is bounded by the total variation for the symmetrized distance. -/
theorem bwdVar_le_eVariationOn (f : α → X) (s : Set α) : bwdVar f s ≤ eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  exact (Finset.sum_le_sum fun i _ ↦ bdist_le_edist _ _).trans (eVariationOn.sum_le hu us)

/-- **Reversal** (Mennucci, Remark 3.3): the forward variation of the reversed curve
`t ↦ f (-t)` on `-s` is the backward variation of `f` on `s`, that is, the forward variation
of `f` for the conjugate distance `(x, y) ↦ b(y, x)`. -/
theorem fwdVar_comp_neg (f : ℝ → X) (s : Set ℝ) :
    fwdVar (f ∘ Neg.neg) (Neg.neg ⁻¹' s) = bwdVar f s := by
  refine le_antisymm (fwdVar.comp_le_bwdVar_of_antitoneOn f _ (fun _ _ _ _ h ↦ neg_le_neg h)
    fun _ h ↦ h) ?_
  have := bwdVar.comp_le_fwdVar_of_antitoneOn (f ∘ Neg.neg) (s := Neg.neg ⁻¹' s) (t := s)
    Neg.neg (fun _ _ _ _ h ↦ neg_le_neg h) fun x hx ↦ by simpa using hx
  have hf : (f ∘ Neg.neg) ∘ Neg.neg = f := by ext; simp
  rwa [hf] at this

/-! ### Continuity of the running length -/

namespace fwdVar

variable {f : ℝ → X} {a b : ℝ}

/-- The forward variation on `[a, b)` is the supremum of the forward variations on `[a, y]`,
`a ≤ y < b`. -/
theorem Ico_le_iSup (f : ℝ → X) (a b : ℝ) :
    fwdVar f (Ico a b) ≤ ⨆ y ∈ Ico a b, fwdVar f (Icc a y) := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  exact le_iSup₂_of_le (u n) (us n)
    (sum_le_of_monotoneOn_Iic (hu.monotoneOn _) fun i hi ↦ ⟨(us i).1, hu hi⟩)

/-- The forward variation on `(a, b]` is the supremum of the forward variations on `[y, b]`,
`a < y ≤ b`. -/
theorem Ioc_le_iSup (f : ℝ → X) (a b : ℝ) :
    fwdVar f (Ioc a b) ≤ ⨆ y ∈ Ioc a b, fwdVar f (Icc y b) := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  exact le_iSup₂_of_le (u 0) (us 0) (sum_le hu fun i ↦ ⟨hu (Nat.zero_le i), (us i).2⟩)

/-- If `f` is continuous from the left at `b` (for the symmetrized topology), its forward
variations on `[a, b]` and on `[a, b)` agree. A strictly monotone sequence ending at `b` is
modified by inserting a point `y` close to `b`, with `b(f y, f b)` small. -/
theorem Icc_le_Ico (hf : ContinuousWithinAt f (Icc a b) b) :
    fwdVar f (Icc a b) ≤ fwdVar f (Ico a b) := by
  refine le_of_strictMonoOn fun m v hv vs ↦ ?_
  rcases (vs m le_rfl).2.lt_or_eq with hlt | heq
  · exact sum_le_of_monotoneOn_Iic hv.monotoneOn fun i hi ↦
      ⟨(vs i hi).1, (hv.monotoneOn (mem_Iic.2 hi) (mem_Iic.2 le_rfl) hi).trans_lt hlt⟩
  cases m with
  | zero => simp
  | succ m =>
    have hvm : v m < b := heq ▸ hv (mem_Iic.2 (Nat.le_succ m)) (mem_Iic.2 le_rfl)
      (Nat.lt_succ_self m)
    have ham : a ≤ v m := (vs m (Nat.le_succ m)).1
    have key : ∀ y ∈ Ioo (v m) b, ∑ i ∈ Finset.range (m + 1), bdist (f (v i)) (f (v (i + 1))) ≤
        fwdVar f (Ico a b) + edist (f y) (f b) := by
      intro y hy
      set w : ℕ → ℝ := fun i ↦ if i ≤ m then v i else y
      have hw : MonotoneOn w (Iic (m + 1)) := by
        intro i hi j hj hij
        simp only [mem_Iic] at hi hj
        simp only [w]
        split_ifs with h1 h2 h2
        · exact hv.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) hij
        · exact (hv.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) h1).trans hy.1.le
        · omega
        · exact le_rfl
      have ws : ∀ i ≤ m + 1, w i ∈ Ico a b := by
        intro i hi
        simp only [w]
        split_ifs with h1
        · exact ⟨(vs i (by omega)).1,
            (hv.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) h1).trans_lt hvm⟩
        · exact ⟨ham.trans hy.1.le, hy.2⟩
      calc ∑ i ∈ Finset.range (m + 1), bdist (f (v i)) (f (v (i + 1)))
          = ∑ i ∈ Finset.range m, bdist (f (w i)) (f (w (i + 1))) + bdist (f (v m)) (f b) := by
            rw [Finset.sum_range_succ, heq]
            congr 1
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            have := Finset.mem_range.mp hi
            simp only [w, ite_eq_left this.le, ite_eq_left (Nat.succ_le_of_lt this)]
        _ ≤ ∑ i ∈ Finset.range m, bdist (f (w i)) (f (w (i + 1))) +
            (bdist (f (w m)) (f (w (m + 1))) + bdist (f y) (f b)) := by
            gcongr
            simpa [w] using bdist_triangle (f (v m)) (f y) (f b)
        _ = ∑ i ∈ Finset.range (m + 1), bdist (f (w i)) (f (w (i + 1))) + bdist (f y) (f b) := by
            rw [Finset.sum_range_succ, add_assoc]
        _ ≤ fwdVar f (Ico a b) + edist (f y) (f b) :=
            add_le_add (sum_le_of_monotoneOn_Iic hw ws) (bdist_le_edist _ _)
    have h1 : Tendsto f (𝓝[Ioo (v m) b] b) (𝓝 (f b)) :=
      (hf.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_left ham))).tendsto
    have h2 : Tendsto (fun y ↦ fwdVar f (Ico a b) + edist (f y) (f b)) (𝓝[Ioo (v m) b] b)
        (𝓝 (fwdVar f (Ico a b))) := by
      simpa using (h1.edist (tendsto_const_nhds (x := f b))).const_add (fwdVar f (Ico a b))
    have : (𝓝[Ioo (v m) b] b).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsLT hvm]; infer_instance
    exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall key)

/-- If `f` is continuous from the right at `a` (for the symmetrized topology), its forward
variations on `[a, b]` and on `(a, b]` agree. A strictly monotone sequence starting at `a` is
modified by inserting a point `y` close to `a`, with `b(f a, f y)` small. -/
theorem Icc_le_Ioc (hf : ContinuousWithinAt f (Icc a b) a) :
    fwdVar f (Icc a b) ≤ fwdVar f (Ioc a b) := by
  refine le_of_strictMonoOn fun m v hv vs ↦ ?_
  have hv0 : ∀ i ≤ m, v 0 ≤ v i := fun i hi ↦
    hv.monotoneOn (mem_Iic.2 (Nat.zero_le _)) (mem_Iic.2 hi) (Nat.zero_le _)
  rcases (vs 0 (Nat.zero_le _)).1.lt_or_eq with hlt | heq
  · exact sum_le_of_monotoneOn_Iic hv.monotoneOn fun i hi ↦
      ⟨hlt.trans_le (hv0 i hi), (vs i hi).2⟩
  cases m with
  | zero => simp
  | succ m =>
    have hv1 : a < v 1 := heq ▸ hv (mem_Iic.2 (Nat.zero_le _)) (mem_Iic.2 (by omega)) zero_lt_one
    have hv1i : ∀ i, 1 ≤ i → i ≤ m + 1 → v 1 ≤ v i := fun i h1 h2 ↦
      hv.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 h2) h1
    have hb1 : v 1 ≤ b := (vs 1 (by omega)).2
    have key : ∀ y ∈ Ioo a (v 1), ∑ i ∈ Finset.range (m + 1), bdist (f (v i)) (f (v (i + 1))) ≤
        fwdVar f (Ioc a b) + edist (f a) (f y) := by
      intro y hy
      set w : ℕ → ℝ := fun i ↦ if i = 0 then y else v i
      have hw : MonotoneOn w (Iic (m + 1)) := by
        intro i hi j hj hij
        simp only [mem_Iic] at hi hj
        simp only [w]
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact hy.2.le.trans (hv1i j (by omega) hj)
        · omega
        · exact hv.monotoneOn (mem_Iic.2 hi) (mem_Iic.2 hj) hij
      have ws : ∀ i ≤ m + 1, w i ∈ Ioc a b := by
        intro i hi
        simp only [w]
        split_ifs with h1
        · exact ⟨hy.1, hy.2.le.trans hb1⟩
        · exact ⟨hv1.trans_le (hv1i i (by omega) hi), (vs i hi).2⟩
      calc ∑ i ∈ Finset.range (m + 1), bdist (f (v i)) (f (v (i + 1)))
          = ∑ i ∈ Finset.range m, bdist (f (w (i + 1))) (f (w (i + 1 + 1))) +
              bdist (f a) (f (w 1)) := by
            rw [Finset.sum_range_succ', heq]
            simp [w]
        _ ≤ ∑ i ∈ Finset.range m, bdist (f (w (i + 1))) (f (w (i + 1 + 1))) +
            (bdist (f a) (f y) + bdist (f (w 0)) (f (w 1))) := by
            gcongr
            simpa [w] using bdist_triangle (f a) (f y) (f (v 1))
        _ = ∑ i ∈ Finset.range (m + 1), bdist (f (w i)) (f (w (i + 1))) + bdist (f a) (f y) := by
            rw [Finset.sum_range_succ' (fun i ↦ bdist (f (w i)) (f (w (i + 1)))), add_comm
              (bdist (f a) (f y)), add_assoc]
        _ ≤ fwdVar f (Ioc a b) + edist (f a) (f y) :=
            add_le_add (sum_le_of_monotoneOn_Iic hw ws) (bdist_le_edist _ _)
    have h1 : Tendsto f (𝓝[Ioo a (v 1)] a) (𝓝 (f a)) :=
      (hf.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hb1))).tendsto
    have h2 : Tendsto (fun y ↦ fwdVar f (Ioc a b) + edist (f a) (f y)) (𝓝[Ioo a (v 1)] a)
        (𝓝 (fwdVar f (Ioc a b))) := by
      simpa using ((tendsto_const_nhds (x := f a)).edist h1).const_add (fwdVar f (Ioc a b))
    have : (𝓝[Ioo a (v 1)] a).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hv1]; infer_instance
    exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall key)

/-- Left continuity of the running length, in terms of suprema. -/
theorem Icc_eq_iSup_Icc_left (hf : ContinuousWithinAt f (Icc a b) b) :
    fwdVar f (Icc a b) = ⨆ y ∈ Ico a b, fwdVar f (Icc a y) :=
  le_antisymm ((Icc_le_Ico hf).trans (Ico_le_iSup f a b))
    (iSup₂_le fun _ hy ↦ mono f (Icc_subset_Icc_right hy.2.le))

/-- Right continuity of the remaining length, in terms of suprema. -/
theorem Icc_eq_iSup_Icc_right (hf : ContinuousWithinAt f (Icc a b) a) :
    fwdVar f (Icc a b) = ⨆ y ∈ Ioc a b, fwdVar f (Icc y b) :=
  le_antisymm ((Icc_le_Ioc hf).trans (Ioc_le_iSup f a b))
    (iSup₂_le fun _ hy ↦ mono f (Icc_subset_Icc_left hy.1.le))

/-- Additivity of the forward variation, in real numbers, on subintervals of an interval
`[a, b]` where it is finite. -/
theorem toReal_Icc_add_toReal_Icc (hfin : fwdVar f (Icc a b) ≠ ⊤) {u v w : ℝ} (hu : a ≤ u)
    (huv : u ≤ v) (hvw : v ≤ w) (hw : w ≤ b) :
    (fwdVar f (Icc u v)).toReal + (fwdVar f (Icc v w)).toReal = (fwdVar f (Icc u w)).toReal := by
  rw [← ENNReal.toReal_add (ne_top_of_le_ne_top hfin (mono f (Icc_subset_Icc hu (hvw.trans hw))))
    (ne_top_of_le_ne_top hfin (mono f (Icc_subset_Icc (hu.trans huv) hw))), Icc_add_Icc' f huv hvw]

/-- The running length controls the asymmetric distance: if the forward variation on `[a, b]` is
finite, then `b(f u, f v) ≤ ℓ(v) - ℓ(u)` for `a ≤ u ≤ v ≤ b`, where `ℓ(t)` is the forward
variation on `[a, t]` (Mennucci, (3.5)). -/
theorem bdist_le_ofReal_sub (hfin : fwdVar f (Icc a b) ≠ ⊤) {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v)
    (hv : v ≤ b) :
    bdist (f u) (f v) ≤
      ENNReal.ofReal ((fwdVar f (Icc a v)).toReal - (fwdVar f (Icc a u)).toReal) := by
  rw [← toReal_Icc_add_toReal_Icc hfin le_rfl hu huv hv, add_sub_cancel_left,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin (mono f (Icc_subset_Icc hu hv)))]
  exact bdist_le f ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv

/-- **Continuity of the running length** (Mennucci, Prop. 3.9), real-valued version: if `f` is
continuous on `[a, b]` for the symmetrized topology and its forward variation there is finite,
then `t ↦ ℓ(t)`, the forward variation on `[a, t]`, is continuous on `[a, b]`. The left and the
right continuity come from `fwdVar.Icc_eq_iSup_Icc_left` and `fwdVar.Icc_eq_iSup_Icc_right`. -/
theorem continuousOn_toReal_Icc (hf : ContinuousOn f (Icc a b)) (hfin : fwdVar f (Icc a b) ≠ ⊤) :
    ContinuousOn (fun t ↦ (fwdVar f (Icc a t)).toReal) (Icc a b) := by
  set G : ℝ → ℝ := fun t ↦ (fwdVar f (Icc a t)).toReal with hG
  have hfin' : ∀ {u v : ℝ}, a ≤ u → v ≤ b → fwdVar f (Icc u v) ≠ ⊤ := fun hu hv ↦
    ne_top_of_le_ne_top hfin (mono f (Icc_subset_Icc hu hv))
  have hadd : ∀ {v w : ℝ}, a ≤ v → v ≤ w → w ≤ b → G v + (fwdVar f (Icc v w)).toReal = G w :=
    fun hv hvw hw ↦ toReal_Icc_add_toReal_Icc hfin le_rfl hv hvw hw
  have hmono : MonotoneOn G (Icc a b) := fun v hv w hw hvw ↦ by
    have := hadd hv.1 hvw hw.2
    have : 0 ≤ (fwdVar f (Icc v w)).toReal := ENNReal.toReal_nonneg
    linarith
  have hG0 : ∀ t, 0 ≤ G t := fun _ ↦ ENNReal.toReal_nonneg
  intro t₀ ht₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hleft⟩ : ∃ δ₁ > 0, ∀ t ∈ Icc a b, t₀ - δ₁ < t → t ≤ t₀ → G t₀ - G t < ε := by
    rcases ht₀.1.lt_or_eq with hat | hat
    · have hsup := Icc_eq_iSup_Icc_left (f := f) (a := a)
        (hf.mono (Icc_subset_Icc_right ht₀.2) t₀ ⟨ht₀.1, le_rfl⟩)
      by_cases hneg : G t₀ - ε < 0
      · exact ⟨1, one_pos, fun t _ _ _ ↦ by linarith [hG0 t]⟩
      rw [not_lt] at hneg
      have hlt : ENNReal.ofReal (G t₀ - ε) < fwdVar f (Icc a t₀) := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal hneg (hfin' le_rfl ht₀.2)]
        linarith
      rw [hsup] at hlt
      obtain ⟨y, hy, hlty⟩ := lt_biSup_iff.mp hlt
      have hyt : G t₀ - ε < G y := by
        rwa [ENNReal.ofReal_lt_iff_lt_toReal hneg (hfin' le_rfl (hy.2.le.trans ht₀.2))] at hlty
      refine ⟨t₀ - y, by linarith [hy.2], fun t ht hyt' htt₀ ↦ ?_⟩
      have := hmono ⟨hy.1, hy.2.le.trans ht₀.2⟩ ht (by linarith)
      linarith
    · refine ⟨1, one_pos, fun t ht _ htt₀ ↦ ?_⟩
      rw [le_antisymm htt₀ (hat ▸ ht.1)]
      simpa using hε
  obtain ⟨δ₂, hδ₂, hright⟩ : ∃ δ₂ > 0, ∀ t ∈ Icc a b, t₀ ≤ t → t < t₀ + δ₂ → G t - G t₀ < ε := by
    rcases ht₀.2.lt_or_eq with htb | htb
    · have hsup := Icc_eq_iSup_Icc_right (f := f) (b := b)
        (hf.mono (Icc_subset_Icc_left ht₀.1) t₀ ⟨le_rfl, ht₀.2⟩)
      set V := (fwdVar f (Icc t₀ b)).toReal
      have hV : G t₀ + V = G b := hadd ht₀.1 ht₀.2 le_rfl
      by_cases hneg : V - ε < 0
      · refine ⟨1, one_pos, fun t ht htt₀ _ ↦ ?_⟩
        have h1 := hadd ht₀.1 htt₀ ht.2
        have h2 := hadd ht.1 ht.2 le_rfl
        have h3 := hadd ht₀.1 (htt₀.trans ht.2) le_rfl
        have : 0 ≤ (fwdVar f (Icc t b)).toReal := ENNReal.toReal_nonneg
        linarith
      rw [not_lt] at hneg
      have hlt : ENNReal.ofReal (V - ε) < fwdVar f (Icc t₀ b) := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal hneg (hfin' ht₀.1 le_rfl)]
        linarith
      rw [hsup] at hlt
      obtain ⟨y, hy, hlty⟩ := lt_biSup_iff.mp hlt
      have hyV : V - ε < (fwdVar f (Icc y b)).toReal := by
        rwa [ENNReal.ofReal_lt_iff_lt_toReal hneg (hfin' (ht₀.1.trans hy.1.le) le_rfl)] at hlty
      have hy' := hadd (ht₀.1.trans hy.1.le) hy.2 le_rfl
      refine ⟨y - t₀, by linarith [hy.1], fun t ht htt₀ hty ↦ ?_⟩
      have := hmono ht ⟨ht₀.1.trans hy.1.le, hy.2⟩ (by linarith)
      linarith
    · refine ⟨1, one_pos, fun t ht htt₀ _ ↦ ?_⟩
      rw [le_antisymm (htb ▸ ht.2) htt₀]
      simpa using hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have h1 := min_le_left δ₁ δ₂
  have h2 := min_le_right δ₁ δ₂
  rcases le_total t t₀ with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hmono ht ht₀ h))]
    exact hleft t ht (by linarith [(abs_lt.mp hdist).1]) h
  · rw [abs_of_nonneg (sub_nonneg.2 (hmono ht₀ ht h))]
    exact hright t ht h (by linarith [(abs_lt.mp hdist).2])

/-- **Continuity of the running length** (Mennucci, Prop. 3.9): if `f` is continuous on `[a, b]`
for the symmetrized topology and its forward variation there is finite, then the running length
`t ↦ fwdVar f (Icc a t)` is continuous on `[a, b]`. -/
theorem continuousOn_Icc (hf : ContinuousOn f (Icc a b)) (hfin : fwdVar f (Icc a b) ≠ ⊤) :
    ContinuousOn (fun t ↦ fwdVar f (Icc a t)) (Icc a b) := by
  refine (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_toReal_Icc hf hfin)).congr
    fun t ht ↦ ?_
  exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin (mono f (Icc_subset_Icc_right ht.2)))).symm

end fwdVar

/-! ### Continuous curves and the induced asymmetric distance -/

/-- A curve `γ : [a, b] → X` from `x` to `y`, continuous for the symmetrized topology. Its
forward length may be infinite. -/
structure FwdPath (x y : X) where
  /-- The curve (only its values on `[a, b]` matter). -/
  toFun : ℝ → X
  /-- The initial time. -/
  a : ℝ
  /-- The final time. -/
  b : ℝ
  le : a ≤ b
  continuousOn : ContinuousOn toFun (Icc a b)
  source : toFun a = x
  target : toFun b = y

namespace FwdPath

variable {x y z : X}

/-- The forward length of a curve: the supremum of the forward sums `Σ b(γ tᵢ, γ tᵢ₊₁)` over the
partitions of `[a, b]`. -/
def length (p : FwdPath x y) : ℝ≥0∞ := fwdVar p.toFun (Icc p.a p.b)

/-- The constant curve. -/
def const (x : X) : FwdPath x x where
  toFun _ := x
  a := 0
  b := 0
  le := le_rfl
  continuousOn := continuousOn_const
  source := rfl
  target := rfl

@[simp] theorem length_const (x : X) : (const x).length = 0 :=
  fwdVar.subsingleton _ (by simp [const])

/-- The trivial partition: `b(x, y) ≤ ℓ(γ)`. -/
theorem bdist_le_length (p : FwdPath x y) : bdist x y ≤ p.length := by
  have := fwdVar.bdist_le p.toFun (left_mem_Icc.2 p.le) (right_mem_Icc.2 p.le) p.le
  rwa [p.source, p.target] at this

/-- The concatenation of a curve from `x` to `y` and a curve from `y` to `z`: the second one is
translated so that it starts at the final time of the first. -/
def concat (p : FwdPath x y) (q : FwdPath y z) : FwdPath x z where
  toFun t := if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b))
  a := p.a
  b := p.b + (q.b - q.a)
  le := p.le.trans (le_add_of_nonneg_right (sub_nonneg.mpr q.le))
  continuousOn := by
    have h1 : ContinuousOn (fun t ↦ if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b)))
        (Icc p.a p.b) :=
      p.continuousOn.congr fun t ht ↦ by simp [ht.2]
    have h2 : ContinuousOn (fun t ↦ if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b)))
        (Icc p.b (p.b + (q.b - q.a))) := by
      have hq : ContinuousOn (fun t ↦ q.toFun (t + (q.a - p.b))) (Icc p.b (p.b + (q.b - q.a))) :=
        q.continuousOn.comp (continuous_id.add continuous_const).continuousOn fun t ht ↦
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine hq.congr fun t ht ↦ ?_
      by_cases htb : t ≤ p.b
      · have : t = p.b := le_antisymm htb ht.1
        subst this
        simp [p.target, q.source]
      · simp [htb]
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc p.le (le_add_of_nonneg_right (sub_nonneg.mpr q.le))] at this
  source := by simp [p.le, p.source]
  target := by
    by_cases h : p.b + (q.b - q.a) ≤ p.b
    · have hqb : q.b = q.a := le_antisymm (by linarith) q.le
      simp only [h, ite_true]
      have : p.b + (q.b - q.a) = p.b := by rw [hqb, sub_self, add_zero]
      rw [this, p.target, ← q.source, ← hqb, q.target]
    · simp only [h, ite_false]
      rw [show p.b + (q.b - q.a) + (q.a - p.b) = q.b by ring, q.target]

/-- **Forward lengths add under concatenation.** -/
theorem length_concat (p : FwdPath x y) (q : FwdPath y z) :
    (p.concat q).length = p.length + q.length := by
  set f := (p.concat q).toFun
  have hb : p.b ≤ p.b + (q.b - q.a) := le_add_of_nonneg_right (sub_nonneg.mpr q.le)
  change fwdVar f (Icc p.a (p.b + (q.b - q.a))) = _
  rw [← fwdVar.Icc_add_Icc' f p.le hb]
  congr 1
  · refine fwdVar.eq_of_eqOn fun t ht ↦ ?_
    simp [f, concat, ht.2]
  · have heq : EqOn f (q.toFun ∘ fun t ↦ t + (q.a - p.b)) (Icc p.b (p.b + (q.b - q.a))) := by
      intro t ht
      by_cases htb : t ≤ p.b
      · have : t = p.b := le_antisymm htb ht.1
        subst this
        simp [f, concat, p.target, q.source]
      · simp [f, concat, htb]
    rw [fwdVar.eq_of_eqOn heq, fwdVar.comp_eq_of_monotoneOn q.toFun
      (fun t ↦ t + (q.a - p.b)) (fun _ _ _ _ h ↦ by simpa using h), image_add_const_Icc]
    congr 2 <;> ring

end FwdPath

/-- The **induced asymmetric distance** `b_g(x, y)`: the infimum of the forward lengths of the
curves from `x` to `y` that are continuous for the symmetrized topology, and `∞` if there is
none (Mennucci, §3.4, for the class of continuous curves). -/
def fwdLengthDist (x y : X) : ℝ≥0∞ := ⨅ p : FwdPath x y, p.length

theorem fwdLengthDist_le {x y : X} (p : FwdPath x y) : fwdLengthDist x y ≤ p.length :=
  iInf_le _ p

/-- **`b ≤ b_g`** (Mennucci, Prop. 3.10, (3.6)). -/
theorem bdist_le_fwdLengthDist (x y : X) : bdist x y ≤ fwdLengthDist x y :=
  le_iInf fun p ↦ p.bdist_le_length

@[simp] theorem fwdLengthDist_self (x : X) : fwdLengthDist x x = 0 :=
  le_antisymm ((fwdLengthDist_le (FwdPath.const x)).trans_eq (FwdPath.length_const x)) bot_le

/-- The triangle inequality for `b_g`, by concatenation of curves. -/
theorem fwdLengthDist_triangle (x y z : X) :
    fwdLengthDist x z ≤ fwdLengthDist x y + fwdLengthDist y z := by
  rcases isEmpty_or_nonempty (FwdPath x y) with hxy | hxy
  · simp [fwdLengthDist]
  rcases isEmpty_or_nonempty (FwdPath y z) with hyz | hyz
  · simp [fwdLengthDist]
  refine ENNReal.le_iInf_add_iInf fun p q ↦ ?_
  rw [← FwdPath.length_concat]
  exact fwdLengthDist_le _

/-- An asymmetric space is **g-intrinsic** (Mennucci, Def. 3.16) if the asymmetric distance
between two points is the infimum of the forward lengths of the curves joining them that are
continuous for the symmetrized topology. -/
def IsFwdInterior (X : Type*) [AsymmPseudoEMetricSpace X] : Prop :=
  ∀ x y : X, fwdLengthDist x y = bdist x y

/-- In a g-intrinsic space, curves of forward length arbitrarily close to `b(x, y)` exist. -/
theorem IsFwdInterior.exists_fwdPath (h : IsFwdInterior X) {x y : X} {ε : ℝ≥0∞}
    (hxy : bdist x y < ε) : ∃ p : FwdPath x y, p.length < ε := by
  rw [← h x y] at hxy
  exact iInf_lt_iff.mp hxy

/-! ### Intermediate points and reparametrization -/

namespace FwdPath

variable {x y : X}

/-- Every intermediate value of the forward length is attained by the running length of a
curve of finite forward length (Mennucci, Prop. 3.9, and the intermediate value theorem). -/
theorem exists_runLength_eq (p : FwdPath x y) (hp : p.length ≠ ⊤) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ p.length.toReal) :
    ∃ t ∈ Icc p.a p.b, (fwdVar p.toFun (Icc p.a t)).toReal = c := by
  have hcont := fwdVar.continuousOn_toReal_Icc p.continuousOn hp
  have := intermediate_value_Icc p.le hcont
  rw [Icc_self, fwdVar.subsingleton _ subsingleton_singleton, ENNReal.toReal_zero] at this
  exact this ⟨hc0, hc⟩

/-- **Forward Lipschitz reparametrization**: a curve of finite forward length `ℓ` from `x` to
`y` can be reparametrized on `[0, 1]` (through its running length, by Mennucci, Prop. 3.9, and
the intermediate value theorem) as a map `η` with `η 0 = x`, `η 1 = y` and
`b(η u, η v) ≤ ℓ (v - u)` for `0 ≤ u ≤ v ≤ 1`. Only the values on `[0, 1]` matter.

The map `η` is `γ ∘ σ` for a monotone choice `σ` of times with running length `u ℓ` at `σ u`
(when `ℓ = 0`, `σ` is affine). Nothing is claimed about `b(η v, η u)`, and `η` need not be
continuous for the symmetrized topology. -/
theorem exists_lipschitz_reparam (p : FwdPath x y) (hp : p.length ≠ ⊤) :
    ∃ η : ℝ → X, η 0 = x ∧ η 1 = y ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, u ≤ v →
      bdist (η u) (η v) ≤ ENNReal.ofReal (p.length.toReal * (v - u)) := by
  set L := p.length
  set F : ℝ → ℝ := fun t ↦ (fwdVar p.toFun (Icc p.a t)).toReal
  have hFa : F p.a = 0 := by simp [F]
  have hFb : F p.b = L.toReal := rfl
  have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  have hmono : MonotoneOn F (Icc p.a p.b) := fun u hu v hv huv ↦
    ENNReal.toReal_mono (ne_top_of_le_ne_top hp (fwdVar.mono _ (Icc_subset_Icc_right hv.2)))
      (fwdVar.mono _ (Icc_subset_Icc_right huv))
  obtain ⟨σ, hσ0, hσ1, hσI, hσF, hσm⟩ : ∃ σ : ℝ → ℝ, σ 0 = p.a ∧ σ 1 = p.b ∧
      (∀ u ∈ Icc (0 : ℝ) 1, σ u ∈ Icc p.a p.b) ∧ (∀ u ∈ Icc (0 : ℝ) 1, F (σ u) = u * L.toReal) ∧
      MonotoneOn σ (Icc (0 : ℝ) 1) := by
    rcases hL0.lt_or_eq with hL | hL
    · have hex : ∀ u ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc p.a p.b, F t = u * L.toReal := fun u hu ↦
        p.exists_runLength_eq hp (mul_nonneg hu.1 hL0) (mul_le_of_le_one_left hL0 hu.2)
      choose! τ hτs hτF using hex
      set σ : ℝ → ℝ := fun u ↦ if u = 0 then p.a else if u = 1 then p.b else τ u
      have hσ : ∀ u ∈ Icc (0 : ℝ) 1, σ u ∈ Icc p.a p.b ∧ F (σ u) = u * L.toReal := by
        intro u hu
        by_cases h0 : u = 0
        · simp [σ, h0, p.le, hFa]
        by_cases h1 : u = 1
        · simp [σ, h1, p.le, hFb]
        simp only [σ, h0, h1, ite_false]
        exact ⟨hτs u hu, hτF u hu⟩
      refine ⟨σ, by simp [σ], by simp [σ], fun u hu ↦ (hσ u hu).1, fun u hu ↦ (hσ u hu).2,
        fun u hu v hv huv ↦ ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have := hmono (hσ v hv).1 (hσ u hu).1 hlt.le
      rw [(hσ u hu).2, (hσ v hv).2] at this
      have hvu : v ≤ u := le_of_mul_le_mul_right this hL
      rw [le_antisymm huv hvu] at hlt
      exact lt_irrefl _ hlt
    · have hF0 : ∀ t ∈ Icc p.a p.b, F t = 0 := fun t ht ↦
        le_antisymm ((hmono ht (right_mem_Icc.2 p.le) ht.2).trans_eq (hFb.trans hL.symm))
          ENNReal.toReal_nonneg
      have hσI : ∀ u ∈ Icc (0 : ℝ) 1, p.a + u * (p.b - p.a) ∈ Icc p.a p.b := fun u hu ↦
        ⟨le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.2 p.le)), by
          nlinarith [hu.2, sub_nonneg.2 p.le]⟩
      refine ⟨fun u ↦ p.a + u * (p.b - p.a), by simp, by simp, hσI, fun u hu ↦ ?_,
        fun u _ v _ huv ↦ ?_⟩
      · rw [hF0 _ (hσI u hu), ← hL, mul_zero]
      · simp only
        nlinarith [sub_nonneg.2 p.le]
  refine ⟨fun u ↦ p.toFun (σ u), by simp [hσ0, p.source], by simp [hσ1, p.target], ?_⟩
  intro u hu v hv huv
  refine (fwdVar.bdist_le_ofReal_sub hp (hσI u hu).1 (hσm hu hv huv) (hσI v hv).2).trans_eq ?_
  change ENNReal.ofReal (F (σ v) - F (σ u)) = _
  rw [hσF u hu, hσF v hv]
  ring_nf

end FwdPath

/-- **Approximate intermediate points at prescribed asymmetric distances.** In a g-intrinsic
space, if `b(x, y) < ∞`, `a, c ≥ 0` and `a + c = b(x, y)`, then for every `ε > 0` there is `z`
with `b(x, z) ≤ a` and `b(z, y) ≤ c + ε`. Take a curve of forward length `< b(x, y) + ε` and
its point at running length `a`, which exists by the continuity of the running length
(Mennucci, Prop. 3.9) and the intermediate value theorem. -/
theorem IsFwdInterior.exists_bdist_le_add (h : IsFwdInterior X) (x y : X) (hxy : bdist x y ≠ ⊤)
    {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = (bdist x y).toReal) (hε : 0 < ε) :
    ∃ z, bdist x z ≤ ENNReal.ofReal a ∧ bdist z y ≤ ENNReal.ofReal (c + ε) := by
  have hlt : bdist x y < ENNReal.ofReal ((bdist x y).toReal + ε) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hxy]
    linarith
  obtain ⟨p, hp⟩ := h.exists_fwdPath hlt
  set L := p.length
  have hLtop : L ≠ ⊤ := ne_top_of_lt hp
  have hdL : (bdist x y).toReal ≤ L.toReal := ENNReal.toReal_mono hLtop p.bdist_le_length
  have hLlt : L.toReal < (bdist x y).toReal + ε := ENNReal.toReal_lt_of_lt_ofReal hp
  obtain ⟨t, ht, hFt⟩ := p.exists_runLength_eq hLtop ha (by linarith)
  refine ⟨p.toFun t, ?_, ?_⟩
  · have := fwdVar.bdist_le_ofReal_sub hLtop le_rfl ht.1 ht.2
    rwa [p.source, Icc_self, fwdVar.subsingleton _ subsingleton_singleton, ENNReal.toReal_zero,
      sub_zero, hFt] at this
  · have := fwdVar.bdist_le_ofReal_sub hLtop ht.1 ht.2 le_rfl
    rw [p.target, hFt] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    change L.toReal - a ≤ c + ε
    linarith

/-- **Approximate intermediate points**, real-valued form: in a g-intrinsic space with
`b(x, y) < ∞`, for `a, c ≥ 0` with `a + c = b(x, y)` and `ε > 0` there is `z` with `b(x, z)`
and `b(z, y)` finite, `b(x, z) ≤ a + ε` and `b(z, y) ≤ c + ε`. -/
theorem IsFwdInterior.exists_bdist_toReal_le_add (h : IsFwdInterior X) (x y : X)
    (hxy : bdist x y ≠ ⊤) {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a + c = (bdist x y).toReal) (hε : 0 < ε) :
    ∃ z, bdist x z ≠ ⊤ ∧ (bdist x z).toReal ≤ a + ε ∧ bdist z y ≠ ⊤ ∧
      (bdist z y).toReal ≤ c + ε := by
  obtain ⟨z, h1, h2⟩ := h.exists_bdist_le_add x y hxy ha hc hac hε
  refine ⟨z, ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1, ?_,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2, ?_⟩
  · exact (ENNReal.toReal_le_of_le_ofReal ha h1).trans (by linarith)
  · exact ENNReal.toReal_le_of_le_ofReal (by linarith) h2

end LocallyConvex.Manifolds
