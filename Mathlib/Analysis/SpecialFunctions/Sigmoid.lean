/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Sigmoid function

In this file we define the sigmoid function `x : ℝ ↦ (1 + exp (-x))⁻¹` and prove some of
its analytic properties.

We then show that the sigmoid function can be seen as an order embedding from `ℝ` to `I = [0, 1]`
and that this embedding is both a topological embedding and a measurable embedding. We also prove
that the composition of this embedding with the measurable embedding from a standard Borel space
`α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

### Sigmoid as a function from `ℝ` to `ℝ`
* `Real.sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `Real.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `Real.continuous_sigmoid` : the sigmoid function is continuous.
* `Real.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `Real.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.
* `Real.hasDerivAt_sigmoid` : the derivative of the sigmoid function.
* `Real.deriv_sigmoid` : formula for the derivative of the sigmoid function.
* `Real.iter_deriv_sigmoid` : formula for the n-th derivative of the sigmoid function.
* `Real.analyticAt_sigmoid` : the sigmoid function is analytic at every point.

### Sigmoid as a function from `ℝ` to `I`
* `unitInterval.sigmoid` : the sigmoid function from `ℝ` to `I`.
* `unitInterval.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `unitInterval.continuous_sigmoid` : the sigmoid function is continuous.
* `unitInterval.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `unitInterval.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `OrderEmbedding.sigmoid` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `OrderEmbedding.isEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a topological
  embedding.
* `OrderEmbedding.measurableEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a
  measurable embedding.
* `OrderEmbedding.measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of the
  sigmoid function from `ℝ` to `I` with the measurable embedding from a standard Borel
  space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/

@[expose] public section

namespace Real

/-- The sigmoid function from `ℝ` to `ℝ`. -/
noncomputable def sigmoid (x : ℝ) := (1 + exp (-x))⁻¹

lemma sigmoid_def (x : ℝ) : sigmoid x = (1 + exp (-x))⁻¹ := rfl

@[simp]
lemma sigmoid_zero : sigmoid 0 = 2⁻¹ := by norm_num [sigmoid]

@[bound]
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]
lemma sigmoid_nonneg (x : ℝ) : 0 ≤ sigmoid x := (sigmoid_pos x).le

@[bound]
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 :=
  inv_lt_one_of_one_lt₀ <| (lt_add_iff_pos_right 1).mpr <| exp_pos _

@[bound]
lemma sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 := (sigmoid_lt_one x).le

@[gcongr, mono]
lemma sigmoid_strictMono : StrictMono sigmoid := fun a b hab ↦ by
  simp only [sigmoid]
  gcongr

lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := sigmoid_strictMono.le_iff_le

@[gcongr]
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr

lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := sigmoid_strictMono.lt_iff_lt

@[gcongr]
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = 1 - sigmoid x := by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : ℝ)]

lemma sigmoid_mul_rexp_neg (x : ℝ) : sigmoid x * exp (-x) = sigmoid (-x) := by
  rw [sigmoid_neg, sigmoid_def]
  field

open Set in
lemma range_sigmoid : range Real.sigmoid = Ioo 0 1 := by
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro - ⟨x, rfl⟩
    simp only [mem_Ioo]
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

open Topology Filter

lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) := by
  simpa using Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot |>.const_add 1 |>.inv₀ <|
    by norm_num

lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
    |>.inv_tendsto_atTop

lemma hasDerivAt_sigmoid (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  convert! (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg x, sigmoid_def]
  field [sq]

lemma deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) :=
  funext fun x => (hasDerivAt_sigmoid x).deriv

end Real

section AnalyticProperties

open Set Real

variable {x : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E}

@[fun_prop]
lemma analyticAt_sigmoid : AnalyticAt ℝ sigmoid x :=
  AnalyticAt.fun_inv (by fun_prop) (by positivity)

@[fun_prop]
lemma AnalyticAt.sigmoid {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (sigmoid ∘ f) x :=
  analyticAt_sigmoid.comp fa

@[fun_prop]
lemma AnalyticAt.sigmoid' {x : E} (fa : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun z ↦ Real.sigmoid (f z)) x := fa.sigmoid

lemma analyticOnNhd_sigmoid : AnalyticOnNhd ℝ sigmoid Set.univ :=
  fun _ _ ↦ analyticAt_sigmoid

lemma AnalyticOnNhd.sigmoid (fs : AnalyticOnNhd ℝ f s) : AnalyticOnNhd ℝ (sigmoid ∘ f) s :=
  fun z n ↦ analyticAt_sigmoid.comp (fs z n)

lemma analyticOn_sigmoid : AnalyticOn ℝ sigmoid Set.univ :=
  analyticOnNhd_sigmoid.analyticOn

lemma AnalyticOn.sigmoid (fs : AnalyticOn ℝ f s) : AnalyticOn ℝ (sigmoid ∘ f) s :=
  analyticOnNhd_sigmoid.comp_analyticOn fs (mapsTo_univ _ _)

lemma analyticWithinAt_sigmoid {s : Set ℝ} : AnalyticWithinAt ℝ sigmoid s x :=
  analyticAt_sigmoid.analyticWithinAt

lemma AnalyticWithinAt.sigmoid {x : E} (fa : AnalyticWithinAt ℝ f s x) :
  AnalyticWithinAt ℝ (sigmoid ∘ f) s x := analyticAt_sigmoid.comp_analyticWithinAt fa

open ContDiff in
@[fun_prop]
lemma contDiff_sigmoid : ContDiff ℝ ω sigmoid := analyticOn_sigmoid.contDiff

open ContDiff in
@[fun_prop]
lemma ContDiff.sigmoid (hf : ContDiff ℝ ω f) : ContDiff ℝ ω (sigmoid ∘ f) :=
  contDiff_sigmoid.comp hf

@[fun_prop]
lemma differentiable_sigmoid : Differentiable ℝ sigmoid :=
   contDiff_sigmoid.of_le le_top |>.differentiable_one

@[fun_prop]
lemma Differentiable.sigmoid (hf : Differentiable ℝ f) : Differentiable ℝ (sigmoid ∘ f) :=
  differentiable_sigmoid.comp hf

@[fun_prop]
lemma differentiableAt_sigmoid : DifferentiableAt ℝ sigmoid x :=
  differentiable_sigmoid x

@[fun_prop]
lemma DifferentiableAt.sigmoid {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (sigmoid ∘ f) x := differentiableAt_sigmoid.comp x hf

@[fun_prop]
lemma continuous_sigmoid : Continuous sigmoid := by fun_prop

omit [NormedSpace ℝ E] in
@[fun_prop]
lemma Continuous.sigmoid (hf : Continuous f) : Continuous (sigmoid ∘ f) :=
  continuous_sigmoid.comp hf

end AnalyticProperties

open Nat Function Finset in
lemma Real.iter_deriv_sigmoid (n : ℕ) : deriv^[n] sigmoid = ∑ k ∈ range (n + 1),
    fun x => (-1)^k * k ! * (n + 1).stirlingSecond (k + 1) * (sigmoid x)^(k + 1) := by
  induction n with
  | zero => simp [stirlingSecond_self]
  | succ n ih =>
    nth_rw 1 [add_comm n 1]
    rw [Function.iterate_add]
    simp only [iterate_one, comp_apply, ih]
    ext x
    rw [deriv_sum (by fun_prop)]
    let a_n_k : ℕ → ℕ → ℝ := fun n k => (-1) ^ k * k ! * (n + 1).stirlingSecond (k + 1)
    let c_n_k : ℕ → ℕ → ℝ := fun n k =>
      if k = 0 then a_n_k n 0
      else a_n_k n k * (k + 1) - a_n_k n (k - 1) * k
    simp only [deriv_const_mul_field', sum_apply]
    calc
    _ = ∑ k ∈ range (n + 1), a_n_k n k * deriv (sigmoid ^ (k + 1)) x := by
      congr
    _ = ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * deriv sigmoid x * x.sigmoid^k := by
      congr with k
      suffices deriv (sigmoid ^ (k + 1)) x = (k + 1) * x.sigmoid^k * deriv sigmoid x by
        rw [this]
        ring
      rw [deriv_pow (by fun_prop)]
      simp
    _ = ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * (x.sigmoid^(k + 1) - x.sigmoid^(k + 2)) := by
      congr with k
      rw [deriv_sigmoid]
      ring
    _ = ∑ k ∈ range (n + 1), (a_n_k n k * (k + 1) * x.sigmoid^(k + 1) -
          a_n_k n k * (k + 1) * x.sigmoid^(k + 2)) := by
        congr with k
        ring
    _ = ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * x.sigmoid^(k + 1) -
        ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * x.sigmoid^(k + 2) := sum_sub_distrib _ _
    _ = ∑ k ∈ range (n + 2), c_n_k n k * x.sigmoid^(k + 1) := by
      -- First sum transformation
      let g : ℕ → ℝ := fun k =>
        if k = n + 1 then 0
        else a_n_k n k * (k + 1) * x.sigmoid ^ (k + 1)
      have : ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * x.sigmoid ^ (k + 1) =
          g (n + 1) + ∑ k ∈ range (n + 1), g k := by
        simp only [↓reduceIte, zero_add, g]
        refine sum_congr rfl fun k hk => ?_
        simp_all only [mem_range, right_eq_ite_iff, cast_add, cast_one,
          _root_.mul_eq_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self,
          not_false_eq_true, pow_eq_zero_iff]
        intro _
        linarith
      rw [this]
      clear this
      rw [← Finset.sum_insert notMem_range_self]
      have : insert (n + 1) (range (n + 1)) = range (n + 2) := by
        grind
      rw [this]
      clear this
      -- Second sum transformation
      let m : ℕ ↪ ℕ := ⟨fun n => n + 1, by simp [Injective]⟩
      let f : ℕ → ℝ := fun k =>
        if k = 0 then 0
        else a_n_k n (k - 1) * k * x.sigmoid ^ (k + 1)
      have : ∑ k ∈ range (n + 1), a_n_k n k * (k + 1) * x.sigmoid ^ (k + 2) =
          ∑ k ∈ range (n + 1), f (m k) := by
        congr with k
        simp [m, f]
      rw [this, ← Finset.sum_map]
      clear this
      have : ∑ k ∈ map m (range (n + 1)), f k = f 0 + ∑ k ∈ map m (range (n + 1)), f k := by
        simp [f]
      rw [this]
      clear this
      rw [← Finset.sum_insert (by simp [m])]
      have : insert 0 (map m (range (n + 1))) = range (n + 2) := by
        ext a
        simp only [mem_insert, mem_map, mem_range]
        constructor
        · rintro (h | ⟨b, hb, h⟩)
          · simp [h]
          · rw [← h]
            exact b.add_lt_add_right hb 1
        · intro h
          by_cases h0 : a = 0
          · left; exact h0
          right
          refine ⟨a - 1, ?_, ?_⟩
          · exact sub_one_lt_of_le (zero_lt_of_ne_zero h0) (le_of_lt_succ h)
          · exact succ_pred_eq_of_ne_zero h0
      rw [this, ← sum_sub_distrib]
      clear this
      -- Combining both transformations
      refine sum_congr rfl fun k hk => ?_
      simp [g, f, c_n_k]
      by_cases h : k = 0
      · simp [h]
      by_cases h' : k = n + 1
      · simp only [h', ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, add_tsub_cancel_right, cast_add, cast_one, zero_sub]
        have : a_n_k n (n + 1) = 0 := by
          simp only [a_n_k]
          rw [stirlingSecond_eq_zero_of_lt (lt_add_one _)]
          simp
        simp [this]
      simp only [h', ↓reduceIte, h]
      ring
    _ = ∑ k ∈ range (n + 2), a_n_k (n + 1) k * (sigmoid x)^(k + 1) := by
      congr with k
      congr
      simp only [a_n_k, c_n_k]
      by_cases h : k = 0
      · simp_all [stirlingSecond_one_right]
      simp only [h, ↓reduceIte]
      calc
      _ = (-1 : ℝ) ^ k * k ! * (n + 1).stirlingSecond (k + 1) * (k + 1) -
          (-1) ^ (k - 1) * (k - 1)! * (n + 1).stirlingSecond k * k := by
        rw [← ne_eq, ← one_le_iff_ne_zero] at h
        rw [k.sub_add_cancel h]
      _ = (-1 : ℝ) ^ k * k ! * (n + 1).stirlingSecond (k + 1) * (k + 1) -
          (-1) ^ (k - 1) * (k * (k - 1)!) * (n + 1).stirlingSecond k := by ring
      _ = (-1 : ℝ) ^ k * k ! * (n + 1).stirlingSecond (k + 1) * (k + 1) -
          (-1) ^ (k - 1) * k ! * (n + 1).stirlingSecond k := by
        suffices (k : ℝ) * ((k - 1)! : ℝ) = (k ! : ℝ) by
          rw [this]
        norm_cast
        rw [mul_factorial_pred h]
      _ = (-1 : ℝ) ^ k * k ! * (n + 1).stirlingSecond (k + 1) * (k + 1) -
          (-1) ^ k * (-1) * k ! * (n + 1).stirlingSecond k := by
        congr
        rw [← ne_eq, ← one_le_iff_ne_zero] at h
        rw [← k.sub_add_cancel h, pow_succ]
        grind
      _ = (-1 : ℝ) ^ k * k ! * ((k + 1) * (n + 1).stirlingSecond (k + 1) +
          (n + 1).stirlingSecond k) := by ring
      _ = (-1) ^ k * k ! * (n + 1 + 1).stirlingSecond (k + 1) := by
        congr
        norm_cast

namespace unitInterval

/-- The sigmoid function from `ℝ` to `I`. -/
noncomputable def sigmoid : ℝ → I := Subtype.coind Real.sigmoid (fun _ ↦ ⟨by bound, by bound⟩)

@[bound]
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := Real.sigmoid_pos x

@[bound]
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := Real.sigmoid_lt_one x

@[gcongr, mono]
lemma sigmoid_strictMono : StrictMono sigmoid := Real.sigmoid_strictMono

lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := Real.sigmoid_le_iff

@[gcongr]
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr

lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := Real.sigmoid_lt_iff

@[gcongr]
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[fun_prop]
lemma continuous_sigmoid : Continuous sigmoid := _root_.continuous_sigmoid.subtype_mk _

lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = σ (sigmoid x) := by
  ext
  exact Real.sigmoid_neg x

open Set in
lemma range_sigmoid : range unitInterval.sigmoid = Ioo 0 1 := by
  rw [sigmoid, Subtype.range_coind, Real.range_sigmoid]
  ext
  simp

open Topology Filter

lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop

lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

end unitInterval

section Embedding

open unitInterval Function Set

/-- The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`. -/
noncomputable def OrderEmbedding.sigmoid : ℝ ↪o I :=
  OrderEmbedding.ofStrictMono unitInterval.sigmoid unitInterval.sigmoid_strictMono

lemma Topology.isEmbedding_sigmoid : IsEmbedding unitInterval.sigmoid :=
  OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => unitInterval.range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

lemma measurableEmbedding_sigmoid : MeasurableEmbedding unitInterval.sigmoid :=
  Topology.isEmbedding_sigmoid.measurableEmbedding <| unitInterval.range_sigmoid ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

lemma measurableEmbedding_sigmoid_comp_embeddingReal :
    MeasurableEmbedding (unitInterval.sigmoid ∘ MeasureTheory.embeddingReal α) :=
  measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end Embedding
