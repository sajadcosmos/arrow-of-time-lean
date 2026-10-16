/-
  Arrow of time paper (`main.tex`): complete Lean 4 formalization in a single file.

  Requirements: Lean 4 (toolchain `leanprover/lean4:v4.28.0`) and Mathlib (`v4.28.0`).
  The only import is `import Mathlib`; no other project files are needed.
  The file contains no `sorry` and no `axiom`.

  The sections below appear in dependency order; each corresponds to one part of
  the paper (see `VERIFICATION.md` for the claim-by-claim map).
-/
import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option autoImplicit false


/-! ════════════════════════════════════════════════════════════════════
    Part: Basic
    ════════════════════════════════════════════════════════════════════ -/

section BasicPart

/-!
# Finite probability laws, relative entropy, total variation and tests

This file sets up the statistical vocabulary of Section 2 of the paper
("Path laws, observations, and computational resources") for *finite* record spaces.

* A law on a finite type `α` is a function `P : α → ℝ` (`IsProb P`).
* `expect P f` is the expectation, `push f P` the push-forward `f_* P`,
  `chan K P` the image of `P` under a stochastic channel (Markov kernel) `K`.
* `KL P Q` is the relative entropy `D_KL(P ‖ Q)` (natural logarithm, nats),
  `TV P Q` is the total-variation distance `½ ∑ |P - Q|`.
* A (randomised) test is a function `A : α → [0,1]` (its acceptance probability);
  `adv P Q A = |E_P A - E_Q A|` is its distinguishing advantage.

Main results: Gibbs' inequality, the log-sum inequality, the data-processing inequality
(Eq. (dpi)) for deterministic maps and for channels, invariance under bijections,
the chain rule (Eq. (chain)), and the variational characterisation of total variation
(Eq. (tv)) together with the optimal equal-prior error `(1 - TV)/2`.
-/


open Finset Real

namespace Arrow

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- `P` is a probability law on the finite type `α`. -/
structure IsProb (P : α → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ P x
  sum_one : ∑ x, P x = 1

/-- Expectation of `f` under the (finite) law `P`. -/
def expect (P : α → ℝ) (f : α → ℝ) : ℝ := ∑ x, P x * f x

/-- Push-forward `f_* P` of a law along a deterministic map. -/
def push [DecidableEq β] (f : α → β) (P : α → ℝ) : β → ℝ :=
  fun y => ∑ x ∈ univ.filter (fun x => f x = y), P x

/-- Image of a law under a stochastic channel `K x y = Prob(output y | input x)`. -/
def chan (K : α → β → ℝ) (P : α → ℝ) : β → ℝ := fun y => ∑ x, P x * K x y

/-- `K` is a stochastic channel (Markov kernel) between finite types. -/
structure IsChannel (K : α → β → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ K x y
  sum_one : ∀ x, ∑ y, K x y = 1

/-- Relative entropy (Kullback–Leibler divergence) in nats. -/
noncomputable def KL (P Q : α → ℝ) : ℝ := ∑ x, P x * Real.log (P x / Q x)

/-- Total-variation distance `½ ∑ |P - Q|`. -/
noncomputable def TV (P Q : α → ℝ) : ℝ := (1 / 2) * ∑ x, |P x - Q x|

/-- Absolute continuity `P ≪ Q` on a finite space. -/
def AbsCont (P Q : α → ℝ) : Prop := ∀ x, Q x = 0 → P x = 0

/-- A randomised test: its acceptance probability lies in `[0,1]`. -/
def IsTest (A : α → ℝ) : Prop := ∀ x, 0 ≤ A x ∧ A x ≤ 1

/-- Distinguishing advantage `|P[A=1] - Q[A=1]|` of a (randomised) test `A`. -/
noncomputable def adv (P Q : α → ℝ) (A : α → ℝ) : ℝ := |expect P A - expect Q A|

/-! ### Basic algebra of expectations and push-forwards -/

lemma expect_add (P f g : α → ℝ) : expect P (fun x => f x + g x) = expect P f + expect P g := by
  simp [expect, mul_add, sum_add_distrib]

lemma expect_const (P : α → ℝ) (hP : IsProb P) (c : ℝ) : expect P (fun _ => c) = c := by
  simp [expect, ← sum_mul, hP.sum_one]

lemma expect_mono {P f g : α → ℝ} (hP : ∀ x, 0 ≤ P x) (h : ∀ x, f x ≤ g x) :
    expect P f ≤ expect P g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hP x)

lemma expect_push [DecidableEq β] (f : α → β) (P : α → ℝ) (g : β → ℝ) :
    expect (push f P) g = expect P (fun x => g (f x)) := by
  unfold expect push
  simp_rw [sum_mul]
  rw [← sum_fiberwise univ f (fun x => P x * g (f x))]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x hx => ?_
  simp only [mem_filter] at hx
  rw [hx.2]

lemma IsProb.push [DecidableEq β] {P : α → ℝ} (hP : IsProb P) (f : α → β) :
    IsProb (push f P) where
  nonneg y := sum_nonneg fun x _ => hP.nonneg x
  sum_one := by
    unfold Arrow.push
    rw [sum_fiberwise univ f P, hP.sum_one]

lemma sum_push [DecidableEq β] (f : α → β) (P : α → ℝ) : ∑ y, push f P y = ∑ x, P x := by
  unfold push; rw [sum_fiberwise univ f P]

omit [Fintype β] in
/-- Push-forward along a bijection is precomposition with the inverse. -/
lemma push_equiv [DecidableEq β] (e : α ≃ β) (P : α → ℝ) : push e P = fun y => P (e.symm y) := by
  funext y
  unfold push
  rw [sum_eq_single (e.symm y)]
  · intro x hx hne
    simp only [mem_filter, mem_univ, true_and] at hx
    exact absurd (by rw [← hx]; simp) hne
  · simp

lemma IsProb.chan {P : α → ℝ} (hP : IsProb P) {K : α → β → ℝ} (hK : IsChannel K) :
    IsProb (chan K P) where
  nonneg y := sum_nonneg fun x _ => mul_nonneg (hP.nonneg x) (hK.nonneg x y)
  sum_one := by
    unfold Arrow.chan
    rw [sum_comm]
    simp_rw [← mul_sum, hK.sum_one, mul_one, hP.sum_one]

lemma expect_chan (K : α → β → ℝ) (P : α → ℝ) (g : β → ℝ) :
    expect (chan K P) g = expect P (fun x => ∑ y, K x y * g y) := by
  unfold expect chan
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

omit [Fintype γ] in
lemma push_push [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (P : α → ℝ) :
    push g (push f P) = push (fun x => g (f x)) P := by
  funext z
  unfold push
  rw [← sum_fiberwise (univ.filter fun x => g (f x) = z) f P]
  rw [sum_filter]
  refine sum_congr rfl fun y _ => ?_
  split_ifs with hy
  · refine sum_congr ?_ fun _ _ => rfl
    ext x; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hx; exact ⟨hx ▸ hy, hx⟩
    · intro hx; exact hx.2
  · symm
    refine sum_eq_zero fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    exact absurd (hx.2 ▸ hx.1) hy

end Arrow

end BasicPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Divergence
    ════════════════════════════════════════════════════════════════════ -/

section DivergencePart

/-!
# Gibbs, log-sum and data-processing inequalities

Eq. (dpi) of the paper: `D(C_* P ‖ C_* Q) ≤ D(P ‖ Q)` for deterministic and stochastic
observation channels, and equality for bijective observations.
-/


open Finset Real

namespace Arrow

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Termwise Gibbs inequality `p log(p/q) ≥ p - q`. -/
lemma mul_log_div_ge_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    p - q ≤ p * Real.log (p / q) := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp [hq]
  · have hq' : 0 < q := lt_of_le_of_ne hq (fun h' => (ne_of_gt h) (hpq h'.symm))
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq' h)
    have h2 : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have : p * (q / p - 1) = q - p := by field_simp
    nlinarith

omit [Fintype α] in
/-- Generalised Gibbs inequality on a finite set of records. -/
lemma gibbs_finset (s : Finset α) {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, q x = 0 → p x = 0) :
    ∑ x ∈ s, p x - ∑ x ∈ s, q x ≤ ∑ x ∈ s, p x * Real.log (p x / q x) := by
  rw [← sum_sub_distrib]
  exact sum_le_sum fun x _ => mul_log_div_ge_sub (hp x) (hq x) (hpq x)

/-- **Gibbs' inequality**: relative entropy is nonnegative. -/
theorem KL_nonneg {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q) :
    0 ≤ KL P Q := by
  have := gibbs_finset univ hP.nonneg hQ.nonneg hPQ
  rw [hP.sum_one, hQ.sum_one, sub_self] at this
  exact this

omit [Fintype α] in
/-- **Log-sum inequality.** -/
lemma log_sum_ineq (s : Finset α) {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, q x = 0 → p x = 0) :
    (∑ x ∈ s, p x) * Real.log ((∑ x ∈ s, p x) / ∑ x ∈ s, q x) ≤
      ∑ x ∈ s, p x * Real.log (p x / q x) := by
  set Ps := ∑ x ∈ s, p x
  set Qs := ∑ x ∈ s, q x
  rcases (sum_nonneg fun x (_ : x ∈ s) => hp x).eq_or_lt with h0 | hPs
  · have hz : ∀ x ∈ s, p x = 0 := (sum_eq_zero_iff_of_nonneg fun x _ => hp x).mp h0.symm
    have hPs0 : Ps = 0 := h0.symm
    rw [hPs0, zero_mul, sum_eq_zero fun x hx => by rw [hz x hx, zero_mul]]
  · have hQs : 0 < Qs := by
      obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, 0 < p x := by
        by_contra hcon
        push_neg at hcon
        have : Ps ≤ 0 := sum_nonpos fun x hx => hcon x hx
        linarith
      have hqx : 0 < q x := lt_of_le_of_ne (hq x) (fun h => (ne_of_gt hx) (hpq x h.symm))
      exact lt_of_lt_of_le hqx (single_le_sum (fun y _ => hq y) hxs)
    set c := Ps / Qs with hc
    have hcpos : 0 < c := div_pos hPs hQs
    have hg := gibbs_finset s hp (q := fun x => q x * c) (fun x => mul_nonneg (hq x) hcpos.le)
      (fun x hx => hpq x (by
        rcases mul_eq_zero.mp hx with h | h
        · exact h
        · exact absurd h (ne_of_gt hcpos)))
    have hsum : ∑ x ∈ s, q x * c = Ps := by
      rw [← sum_mul]; show Qs * (Ps / Qs) = Ps; field_simp
    rw [hsum, sub_self] at hg
    have key : ∀ x ∈ s, p x * Real.log (p x / (q x * c)) =
        p x * Real.log (p x / q x) - p x * Real.log c := by
      intro x _
      rcases (hp x).eq_or_lt with h | h
      · rw [← h]; simp
      · have hqx : 0 < q x := lt_of_le_of_ne (hq x) (fun h' => (ne_of_gt h) (hpq x h'.symm))
        rw [← mul_sub, ← Real.log_div (by positivity) hcpos.ne', div_div]
    rw [sum_congr rfl key, sum_sub_distrib, ← sum_mul] at hg
    linarith

/-- **Data-processing inequality** (Eq. (dpi)) for a deterministic observation `f`. -/
theorem KL_push_le [DecidableEq β] {P Q : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPQ : AbsCont P Q) (f : α → β) :
    KL (push f P) (push f Q) ≤ KL P Q := by
  unfold KL push
  rw [← sum_fiberwise univ f (fun x => P x * Real.log (P x / Q x))]
  exact sum_le_sum fun y _ => log_sum_ineq _ hP hQ hPQ

omit [Fintype β] in
lemma AbsCont.push [DecidableEq β] {P Q : α → ℝ} (hQ : ∀ x, 0 ≤ Q x)
    (hPQ : AbsCont P Q) (f : α → β) : AbsCont (push f P) (push f Q) := by
  intro y hy
  unfold Arrow.push at *
  have : ∀ x ∈ univ.filter (fun x => f x = y), Q x = 0 :=
    (sum_eq_zero_iff_of_nonneg fun x _ => hQ x).mp hy
  exact sum_eq_zero fun x hx => hPQ x (this x hx)

/-- Relative entropy is invariant under a bijective observation. -/
theorem KL_push_equiv [DecidableEq β] (e : α ≃ β) (P Q : α → ℝ) :
    KL (push e P) (push e Q) = KL P Q := by
  rw [push_equiv, push_equiv]
  unfold KL
  exact Fintype.sum_equiv e.symm _ _ (fun y => rfl)

/-- Total variation is invariant under a bijective observation. -/
theorem TV_push_equiv [DecidableEq β] (e : α ≃ β) (P Q : α → ℝ) :
    TV (push e P) (push e Q) = TV P Q := by
  rw [push_equiv, push_equiv]
  unfold TV
  congr 1
  exact Fintype.sum_equiv e.symm _ _ (fun y => rfl)

/-- Total variation cannot increase under a deterministic observation. -/
theorem TV_push_le [DecidableEq β] (f : α → β) (P Q : α → ℝ) :
    TV (push f P) (push f Q) ≤ TV P Q := by
  unfold TV push
  gcongr
  rw [← sum_fiberwise univ f (fun x => |P x - Q x|)]
  refine sum_le_sum fun y _ => ?_
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-! ### Joint laws and the channel data-processing inequality -/

/-- Joint law of input and channel output. -/
def joint (K : α → β → ℝ) (P : α → ℝ) : α × β → ℝ := fun z => P z.1 * K z.1 z.2

lemma chan_eq_push_joint (K : α → β → ℝ) (P : α → ℝ) [DecidableEq β] :
    chan K P = push Prod.snd (joint K P) := by
  funext y
  unfold chan push joint
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq']; simp

lemma KL_joint {P Q : α → ℝ} {K : α → β → ℝ} (hK : IsChannel K) : KL (joint K P) (joint K Q) = KL P Q := by
  unfold KL joint
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  have : ∀ y, P x * K x y * Real.log (P x * K x y / (Q x * K x y)) =
      K x y * (P x * Real.log (P x / Q x)) := by
    intro y
    rcases (hK.nonneg x y).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [mul_div_mul_right _ _ h.ne']; ring
  simp_rw [this, ← sum_mul, hK.sum_one, one_mul]

/-- **Data-processing inequality for stochastic channels** (Eq. (dpi)). -/
theorem KL_chan_le {P Q : α → ℝ} {K : α → β → ℝ} (hK : IsChannel K) (hP : ∀ x, 0 ≤ P x)
    (hQ : ∀ x, 0 ≤ Q x) (hPQ : AbsCont P Q) : KL (chan K P) (chan K Q) ≤ KL P Q := by
  classical
  rw [chan_eq_push_joint, chan_eq_push_joint, ← KL_joint hK]
  refine KL_push_le (fun z => mul_nonneg (hP _) (hK.nonneg _ _))
    (fun z => mul_nonneg (hQ _) (hK.nonneg _ _)) ?_ _
  intro z hz
  simp only at hz ⊢
  rcases mul_eq_zero.mp hz with h | h
  · rw [hPQ _ h, zero_mul]
  · rw [h, mul_zero]

lemma AbsCont.chan {P Q : α → ℝ} {K : α → β → ℝ} (hK : IsChannel K)
    (hQ : ∀ x, 0 ≤ Q x) (hPQ : AbsCont P Q) : AbsCont (chan K P) (chan K Q) := by
  intro y hy
  unfold Arrow.chan at *
  have := (sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (hQ x) (hK.nonneg x y)).mp hy
  refine sum_eq_zero fun x _ => ?_
  rcases mul_eq_zero.mp (this x (mem_univ _)) with h | h
  · rw [hPQ x h, zero_mul]
  · rw [h, mul_zero]

/-- Total variation cannot increase under a stochastic channel. -/
theorem TV_chan_le {P Q : α → ℝ} {K : α → β → ℝ} (hK : IsChannel K) :
    TV (chan K P) (chan K Q) ≤ TV P Q := by
  unfold TV chan
  gcongr
  calc ∑ y, |∑ x, P x * K x y - ∑ x, Q x * K x y|
      ≤ ∑ y, ∑ x, |P x - Q x| * K x y := sum_le_sum fun y _ => by
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
        rw [← sub_mul, abs_mul, abs_of_nonneg (hK.nonneg x y)]
    _ = ∑ x, |P x - Q x| := by
        rw [sum_comm]; simp_rw [← mul_sum, hK.sum_one, mul_one]

/-! ### The chain rule, Eq. (chain) -/

/-- **Chain rule for relative entropy** (Eq. (chain)) for a deterministic observation,
for laws of full support: the divergence of the microscopic laws is the divergence of the
recorded laws plus the average divergence of the conditional laws given the record. -/
theorem KL_chain [DecidableEq β] {P Q : α → ℝ} (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x)
    (f : α → β) :
    KL P Q = KL (push f P) (push f Q) +
      ∑ y, push f P y * ∑ x ∈ univ.filter (fun x => f x = y),
        (P x / push f P y) * Real.log ((P x / push f P y) / (Q x / push f Q y)) := by
  unfold KL
  rw [← sum_fiberwise univ f (fun x => P x * Real.log (P x / Q x)), ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rcases (univ.filter (fun x => f x = y)).eq_empty_or_nonempty with he | hne
  · simp [push, he]
  have hPy : 0 < push f P y := sum_pos (fun x _ => hP x) hne
  have hQy : 0 < push f Q y := sum_pos (fun x _ => hQ x) hne
  rw [mul_sum, ← sum_congr rfl (fun x _ => rfl), show push f P y * Real.log (push f P y / push f Q y)
    = ∑ x ∈ univ.filter (fun x => f x = y), P x * Real.log (push f P y / push f Q y) by
      rw [← sum_mul]; rfl, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  have hPx := hP x; have hQx := hQ x
  rw [← mul_assoc, mul_div_cancel₀ _ hPy.ne', ← mul_add, ← Real.log_mul (by positivity)
    (by positivity)]
  congr 2
  field_simp

end Arrow

end DivergencePart


/-! ════════════════════════════════════════════════════════════════════
    Part: Tests
    ════════════════════════════════════════════════════════════════════ -/

section TestsPart

/-!
# Tests, total variation and likelihood-ratio decisions

* Eq. (tv): `TV(P,Q) = sup_A |P(A=1) - Q(A=1)|`, attained by the likelihood-ratio test,
  and the optimal equal-prior error `(1 - TV)/2`.
* Proposition `prop:approx` (approximate likelihood decision).
* Likelihood identities for reversal-related laws (Eqs. (encodedift), (encodeddft)).
-/


open Finset Real

namespace Arrow

variable {α β : Type*} [Fintype α] [Fintype β]

lemma expect_sub_expect (P Q A : α → ℝ) :
    expect P A - expect Q A = ∑ x, (P x - Q x) * A x := by
  unfold expect; rw [← sum_sub_distrib]; simp [sub_mul]

/-- Every randomised test has advantage at most the total variation. -/
theorem adv_le_TV {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) {A : α → ℝ} (hA : IsTest A) :
    adv P Q A ≤ TV P Q := by
  unfold adv TV
  have h0 : ∑ x, (P x - Q x) = 0 := by rw [sum_sub_distrib, hP.sum_one, hQ.sum_one, sub_self]
  have : expect P A - expect Q A = ∑ x, (P x - Q x) * (A x - 1 / 2) := by
    rw [expect_sub_expect]
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, h0, zero_mul, sub_zero]
  rw [this, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  have : |A x - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [(hA x).1], by linarith [(hA x).2]⟩
  nlinarith [abs_nonneg (P x - Q x)]

/-- The likelihood-ratio (Neyman–Pearson) test: accept "forward" iff `P > Q`. -/
noncomputable def lrTest (P Q : α → ℝ) : α → ℝ := fun x => if Q x < P x then 1 else 0

omit [Fintype α] in
lemma lrTest_isTest (P Q : α → ℝ) : IsTest (lrTest P Q) := fun x => by
  unfold lrTest; split_ifs <;> norm_num

/-- The likelihood-ratio test attains the total variation. -/
theorem expect_lrTest {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    expect P (lrTest P Q) - expect Q (lrTest P Q) = TV P Q := by
  rw [expect_sub_expect]
  have h0 : ∑ x, (P x - Q x) = 0 := by rw [sum_sub_distrib, hP.sum_one, hQ.sum_one, sub_self]
  have key : ∀ x, |P x - Q x| = 2 * ((P x - Q x) * lrTest P Q x) - (P x - Q x) := by
    intro x; unfold lrTest
    split_ifs with h
    · rw [abs_of_pos (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith)]; ring
  unfold TV
  rw [sum_congr rfl (fun x _ => key x), sum_sub_distrib, ← mul_sum, h0]
  ring

/-- **Eq. (tv)**: total variation is the largest advantage of a randomised test. -/
theorem TV_isGreatest {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    IsGreatest {a | ∃ A, IsTest A ∧ a = adv P Q A} (TV P Q) := by
  refine ⟨⟨lrTest P Q, lrTest_isTest P Q, ?_⟩, ?_⟩
  · unfold adv; rw [expect_lrTest hP hQ, abs_of_nonneg]
    unfold TV; positivity
  · rintro a ⟨A, hA, rfl⟩; exact adv_le_TV hP hQ hA

/-- Equal-prior orientation error of a test that declares "forward" with probability `A`. -/
noncomputable def bayesErr (P Q A : α → ℝ) : ℝ :=
  (expect P (fun x => 1 - A x) + expect Q A) / 2

/-- The optimal equal-prior orientation error is `(1 - TV(P,Q))/2`. -/
theorem bayesErr_optimal {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    (∀ A, IsTest A → (1 - TV P Q) / 2 ≤ bayesErr P Q A) ∧
      bayesErr P Q (lrTest P Q) = (1 - TV P Q) / 2 := by
  have e : ∀ A, bayesErr P Q A = (1 - (expect P A - expect Q A)) / 2 := by
    intro A; unfold bayesErr
    have : expect P (fun x => 1 - A x) = 1 - expect P A := by
      unfold expect; simp [mul_sub, sum_sub_distrib, hP.sum_one]
    rw [this]; ring
  refine ⟨fun A hA => ?_, by rw [e, expect_lrTest hP hQ]⟩
  rw [e]
  have := adv_le_TV hP hQ hA
  unfold adv at this
  linarith [le_abs_self (expect P A - expect Q A)]

/-! ### Proposition `prop:approx`: approximate likelihood decision -/

/-- **Proposition (approximate likelihood decision).** If an efficiently computable statistic
`lhat` approximates the log-likelihood ratio `log(P/Q)` to within `δ` on every record,
then its sign test has advantage at least `TV(P,Q) - (e^δ - 1)`. -/
theorem approx_likelihood_decision {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q)
    (hPpos : ∀ x, 0 < P x) (hQpos : ∀ x, 0 < Q x) (lhat : α → ℝ) (δ : ℝ)
    (hδ : ∀ x, |lhat x - Real.log (P x / Q x)| ≤ δ) :
    TV P Q - (Real.exp δ - 1) ≤ adv P Q (fun x => if 0 < lhat x then 1 else 0) := by
  set A : α → ℝ := fun x => if 0 < lhat x then 1 else 0
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.sum_one
    simp at this
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ hne.some)
  refine le_trans ?_ (le_abs_self _)
  rw [← expect_lrTest hP hQ, expect_sub_expect, expect_sub_expect, sub_le_iff_le_add,
    ← sub_le_iff_le_add', ← sum_sub_distrib]
  have hterm : ∀ x, (P x - Q x) * lrTest P Q x - (P x - Q x) * A x ≤ (Real.exp δ - 1) * Q x := by
    intro x
    have hP' := hPpos x; have hQ' := hQpos x
    have hl := hδ x
    rw [abs_le] at hl
    have hlog : Real.log (P x / Q x) = Real.log (P x) - Real.log (Q x) :=
      Real.log_div hP'.ne' hQ'.ne'
    have hed : 1 ≤ Real.exp δ := Real.one_le_exp hδ0
    unfold lrTest
    simp only [A]
    split_ifs with h1 h2 h2
    · nlinarith
    · -- `P > Q` but `lhat ≤ 0`: then `log(P/Q) ≤ δ`
      have : Real.log (P x / Q x) ≤ δ := by linarith
      have h3 : P x / Q x ≤ Real.exp δ := by
        rw [← Real.exp_log (div_pos hP' hQ')]; exact Real.exp_le_exp.mpr this
      rw [div_le_iff₀ hQ'] at h3
      nlinarith
    · -- `P ≤ Q` but `lhat > 0`: then `log(P/Q) > -δ`
      have : -δ ≤ Real.log (P x / Q x) := by linarith
      have h3 : Real.exp (-δ) ≤ P x / Q x := by
        rw [← Real.exp_log (div_pos hP' hQ')]; exact Real.exp_le_exp.mpr this
      rw [le_div_iff₀ hQ'] at h3
      have h4 : 1 - Real.exp (-δ) ≤ Real.exp δ - 1 := by
        have : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-δ)]
      nlinarith
    · nlinarith
  calc ∑ x, ((P x - Q x) * lrTest P Q x - (P x - Q x) * A x)
      ≤ ∑ x, (Real.exp δ - 1) * Q x := sum_le_sum fun x _ => hterm x
    _ = Real.exp δ - 1 := by rw [← mul_sum, hQ.sum_one, mul_one]

end Arrow

end TestsPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Likelihood
    ════════════════════════════════════════════════════════════════════ -/

section LikelihoodPart

/-!
# Likelihood identities, variational formulas and binary certificates

* Reversal-related laws `Q = P ∘ τ` with an involution `τ`:
  antisymmetry of the log-likelihood, the integral fluctuation identity `E_P e^{-ℓ} = 1`
  and the detailed fluctuation relation (Eqs. (encodedift), (encodeddft)); equality of the
  laws of time-reversal-even statistics.
* Donsker–Varadhan variational formula (Eq. (dv)) and Jensen's inequality.
* Binary data processing (Eq. (binarydpi)) and the binary lower bound (Eq. (binarylower)).
-/


open Finset Real

namespace Arrow

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Reversal-related laws -/

/-- Log-likelihood ratio `ℓ = log(P/Q)`. -/
noncomputable def llr (P Q : α → ℝ) : α → ℝ := fun x => Real.log (P x / Q x)

omit [Fintype α] in
/-- For `Q = P ∘ τ` with `τ` an involution, the log-likelihood ratio is odd under `τ`. -/
theorem llr_reversal (P : α → ℝ) (τ : α → α) (hτ : Function.Involutive τ) (x : α) :
    llr P (fun y => P (τ y)) (τ x) = - llr P (fun y => P (τ y)) x := by
  unfold llr
  show Real.log (P (τ x) / P (τ (τ x))) = -Real.log (P x / P (τ x))
  rw [hτ x, ← Real.log_inv, inv_div]

/-- **Integral fluctuation identity** `E_P e^{-ℓ} = 1` for `Q = P ∘ τ`, `P > 0`. -/
theorem integral_fluctuation {P : α → ℝ} (hP : IsProb P) (hpos : ∀ x, 0 < P x) (τ : α → α)
    (hτ : Function.Involutive τ) :
    expect P (fun x => Real.exp (- llr P (fun y => P (τ y)) x)) = 1 := by
  unfold expect llr
  have : ∀ x, P x * Real.exp (- Real.log (P x / P (τ x))) = P (τ x) := by
    intro x
    rw [Real.exp_neg, Real.exp_log (div_pos (hpos x) (hpos (τ x)))]
    field_simp [(hpos x).ne']
  simp_rw [this]
  rw [Fintype.sum_equiv (Function.Involutive.toPerm τ hτ) (fun x => P (τ x)) P (fun x => rfl),
    hP.sum_one]

/-- **Detailed fluctuation relation** `P(ℓ = u) = e^u P(ℓ = -u)` for `Q = P ∘ τ`, `P > 0`. -/
theorem detailed_fluctuation {P : α → ℝ} (hpos : ∀ x, 0 < P x) (τ : α → α)
    (hτ : Function.Involutive τ) (u : ℝ) :
    ∑ x ∈ univ.filter (fun x => llr P (fun y => P (τ y)) x = u), P x =
      Real.exp u * ∑ x ∈ univ.filter (fun x => llr P (fun y => P (τ y)) x = -u), P x := by
  set ℓ := llr P (fun y => P (τ y))
  rw [mul_sum]
  -- reindex the right-hand side by `τ`
  have hre : ∑ x ∈ univ.filter (fun x => ℓ x = -u), Real.exp u * P x =
      ∑ x ∈ univ.filter (fun x => ℓ x = u), Real.exp u * P (τ x) := by
    refine Finset.sum_nbij' τ τ ?_ ?_ (fun x _ => hτ x) (fun x _ => hτ x) ?_
    · intro x hx
      have hx' : ℓ x = -u := by simpa using hx
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [show ℓ (τ x) = -ℓ x from llr_reversal P τ hτ x, hx', neg_neg]
    · intro x hx
      have hx' : ℓ x = u := by simpa using hx
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [show ℓ (τ x) = -ℓ x from llr_reversal P τ hτ x, hx']
    · intro x _; rw [hτ x]
  rw [hre]
  refine sum_congr rfl fun x hx => ?_
  simp only [mem_filter, mem_univ, true_and] at hx
  rw [← hx]
  simp only [ℓ, llr]
  rw [Real.exp_log (div_pos (hpos x) (hpos (τ x)))]
  field_simp [(hpos (τ x)).ne']

omit [Fintype β] in
/-- A time-reversal-even statistic (`g ∘ τ = g`) has the same law under `P` and `P ∘ τ`;
e.g. the absolute current `|2|Z| - m|` of the ring record. -/
theorem push_even_statistic [DecidableEq β] (P : α → ℝ) (τ : α → α) (hτ : Function.Involutive τ)
    (g : α → β) (hg : ∀ x, g (τ x) = g x) : push g (fun y => P (τ y)) = push g P := by
  funext b
  unfold push
  refine Finset.sum_nbij' τ τ ?_ ?_ (fun x _ => hτ x) (fun x _ => hτ x) (fun x _ => rfl)
  · intro x hx
    have hx' : g x = b := by simpa using hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [hg, hx']
  · intro x hx
    have hx' : g x = b := by simpa using hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [hg, hx']

omit [Fintype α] in
/-- For an involution, the push-forward along `τ` is precomposition with `τ`. -/
lemma push_involutive [DecidableEq α] [Fintype α] (P : α → ℝ) (τ : α → α)
    (hτ : Function.Involutive τ) : push τ P = fun y => P (τ y) := by
  have := push_equiv (Function.Involutive.toPerm τ hτ) P
  simpa using this

/-! ### Jensen and the Donsker–Varadhan formula -/

/-- Jensen's inequality `E_Q f ≤ log E_Q e^f`. -/
theorem expect_le_log_expect_exp {Q : α → ℝ} (hQ : IsProb Q) (f : α → ℝ) :
    expect Q f ≤ Real.log (expect Q (fun x => Real.exp (f x))) := by
  set c := expect Q f
  have h : Real.exp c ≤ expect Q (fun x => Real.exp (f x)) := by
    have : ∀ x, Real.exp c * (f x - c + 1) ≤ Real.exp (f x) := by
      intro x
      have := Real.add_one_le_exp (f x - c)
      rw [Real.exp_sub] at this
      have hc := Real.exp_pos c
      rw [le_div_iff₀ hc] at this
      linarith
    calc Real.exp c = expect Q (fun x => Real.exp c * (f x - c + 1)) := by
          unfold expect
          simp_rw [mul_add, mul_sub, mul_one, mul_left_comm _ (Real.exp c),
            sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hQ.sum_one]
          simp only [c, expect]; ring
      _ ≤ _ := expect_mono hQ.nonneg this
  calc c = Real.log (Real.exp c) := (Real.log_exp c).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos c) h

/-- Donsker–Varadhan objective `E_P f - log E_Q e^f`. -/
noncomputable def dvObj (P Q f : α → ℝ) : ℝ :=
  expect P f - Real.log (expect Q (fun x => Real.exp (f x)))

/-- **Donsker–Varadhan upper bound** (Eq. (dv)): every score gives a lower bound on KL. -/
theorem dvObj_le_KL {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q)
    (f : α → ℝ) : dvObj P Q f ≤ KL P Q := by
  set Z := expect Q (fun x => Real.exp (f x))
  have hne : Nonempty α := by
    by_contra h; rw [not_nonempty_iff] at h; have := hP.sum_one; simp at this
  have hZ : 0 < Z := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < Q x := by
      by_contra h; push_neg at h
      have : ∑ x, Q x ≤ 0 := sum_nonpos fun x _ => h x
      linarith [hQ.sum_one]
    exact lt_of_lt_of_le (mul_pos hx (Real.exp_pos _))
      (single_le_sum (f := fun x => Q x * Real.exp (f x))
        (fun y _ => mul_nonneg (hQ.nonneg y) (Real.exp_pos _).le) (mem_univ x))
  set Qf : α → ℝ := fun x => Q x * Real.exp (f x) / Z
  have hQf : IsProb Qf := ⟨fun x => div_nonneg (mul_nonneg (hQ.nonneg x) (Real.exp_pos _).le)
      hZ.le, by simp only [Qf]; rw [← sum_div]; exact div_self hZ.ne'⟩
  have hPQf : AbsCont P Qf := by
    intro x hx
    simp only [Qf, div_eq_zero_iff, mul_eq_zero, (Real.exp_pos _).ne', or_false,
      hZ.ne'] at hx
    exact hPQ x hx
  have h0 := KL_nonneg hP hQf hPQf
  have hexp : KL P Qf = KL P Q - expect P f + Real.log Z := by
    unfold KL expect
    rw [← sum_sub_distrib, show Real.log Z = ∑ x, P x * Real.log Z by
      rw [← sum_mul, hP.sum_one, one_mul], ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rcases (hP.nonneg x).eq_or_lt with h | h
    · rw [← h]; simp
    · have hq : 0 < Q x := lt_of_le_of_ne (hQ.nonneg x) (fun h' => h.ne' (hPQ x h'.symm))
      simp only [Qf]
      rw [show P x / (Q x * Real.exp (f x) / Z) = (P x / Q x) * Z / Real.exp (f x) by
        field_simp]
      rw [Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity)
        hZ.ne', Real.log_exp]
      ring
  unfold dvObj
  linarith

/-- **Donsker–Varadhan formula** (Eq. (dv)): for laws of full support the supremum of the
objective is attained at the likelihood score `log(P/Q)` and equals `D(P‖Q)`. -/
theorem KL_isGreatest_dvObj {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q)
    (hPpos : ∀ x, 0 < P x) (hQpos : ∀ x, 0 < Q x) :
    IsGreatest (Set.range (dvObj P Q)) (KL P Q) := by
  refine ⟨⟨llr P Q, ?_⟩, ?_⟩
  · unfold dvObj llr expect KL
    have : ∀ x, Q x * Real.exp (Real.log (P x / Q x)) = P x := by
      intro x; rw [Real.exp_log (div_pos (hPpos x) (hQpos x))]; field_simp [(hQpos x).ne']
    simp_rw [this, hP.sum_one, Real.log_one, sub_zero]
  · rintro _ ⟨f, rfl⟩
    exact dvObj_le_KL hP hQ (fun x h => absurd h (hQpos x).ne') f

end Arrow

end LikelihoodPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Binary
    ════════════════════════════════════════════════════════════════════ -/

section BinaryPart

/-!
# Binary experiments, contamination, coupling and Hellinger bounds

* Eq. (binarydpi): `D(P‖Q) ≥ d_bin(P(A=1) ‖ Q(A=1))` for every (randomised) test.
* Eq. (binarylower): if a test has both orientation errors at most `α < 1/2` then
  `D(P‖Q) ≥ (1 - 2α) log((1-α)/α)`.
* Proposition `prop:contamination` (Eqs. (contamcap), (contamtv)) and the realisation of the
  contamination by a single common reversal channel (Eq. (contamchannel)).
* Eq. (transferadv): coupling transfer of distinguishing advantage.
* Eqs. (hellinger), (hellingertv): Hellinger affinity and the two-sided TV bounds.
-/


open Finset Real

namespace Arrow

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The Bernoulli law on `Bool` with `P(true) = u`. -/
def bern (u : ℝ) : Bool → ℝ := fun b => if b then u else 1 - u

lemma bern_isProb {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : IsProb (bern u) :=
  ⟨fun b => by cases b <;> simp [bern] <;> linarith, by simp [bern]⟩

/-- Binary relative entropy `d_bin(u‖v)`. -/
noncomputable def dbin (u v : ℝ) : ℝ :=
  u * Real.log (u / v) + (1 - u) * Real.log ((1 - u) / (1 - v))

lemma KL_bern (u v : ℝ) : KL (bern u) (bern v) = dbin u v := by
  simp [KL, bern, dbin]

/-- The channel turning a randomised test into its binary decision. -/
def testChan (A : α → ℝ) : α → Bool → ℝ := fun x b => if b then A x else 1 - A x

omit [Fintype α] in
lemma testChan_isChannel {A : α → ℝ} (hA : IsTest A) : IsChannel (testChan A) :=
  ⟨fun x b => by cases b <;> simp [testChan] <;> linarith [(hA x).1, (hA x).2],
    fun x => by simp [testChan]⟩

lemma chan_testChan {P : α → ℝ} (hP : IsProb P) (A : α → ℝ) :
    chan (testChan A) P = bern (expect P A) := by
  funext b
  cases b
  · simp only [chan, testChan, bern, expect, Bool.false_eq_true, if_false]
    simp [mul_sub, sum_sub_distrib, hP.sum_one]
  · simp [chan, testChan, bern, expect]

/-- **Eq. (binarydpi)**: binary data processing for an arbitrary (randomised) classifier. -/
theorem dbin_le_KL {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q)
    {A : α → ℝ} (hA : IsTest A) : dbin (expect P A) (expect Q A) ≤ KL P Q := by
  rw [← KL_bern, ← chan_testChan hP, ← chan_testChan hQ]
  exact KL_chan_le (testChan_isChannel hA) hP.nonneg hQ.nonneg hPQ

lemma absCont_bern_test {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q)
    {A : α → ℝ} (hA : IsTest A) : AbsCont (bern (expect P A)) (bern (expect Q A)) := by
  rw [← chan_testChan hP, ← chan_testChan hQ]
  exact AbsCont.chan (testChan_isChannel hA) hQ.nonneg hPQ

/-- Garbling of binary experiments: if `u ≥ 1 - a` and `v ≤ a` with `a < 1/2` then
`(1-a, a)` is a garbling of `(u, v)`, hence `d_bin(1-a‖a) ≤ d_bin(u‖v)`. -/
lemma dbin_boundary_le {a u v : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hu : 1 - a ≤ u)
    (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv : v ≤ a) (hac : AbsCont (bern u) (bern v)) :
    dbin (1 - a) a ≤ dbin u v := by
  set d := u - v with hd
  have hdpos : 1 - 2 * a ≤ d := by linarith
  have hd0 : 0 < d := by linarith
  set k := (1 - 2 * a) / d with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) hd0.le
  have hk1 : k ≤ 1 := (div_le_one hd0).mpr hdpos
  set t := a - v * k
  set s := t + k
  have ht0 : 0 ≤ t := by nlinarith
  have hs1 : s ≤ 1 := by
    have hkd : k * d = 1 - 2 * a := by rw [hk]; field_simp
    have : (1 - v) * k ≤ 1 - a := by
      have h1 : (1 - v) * (1 - 2 * a) ≤ (1 - a) * d := by nlinarith
      have h2 : (1 - v) * k * d ≤ (1 - a) * d := by rw [mul_assoc, hkd]; exact h1
      exact le_of_mul_le_mul_right h2 hd0
    simp only [s, t]; nlinarith
  let G : Bool → Bool → ℝ := fun b c =>
    if c then (if b then s else t) else 1 - (if b then s else t)
  have hG : IsChannel G := ⟨fun b c => by
      cases b <;> cases c <;> simp [G] <;> nlinarith, fun b => by simp [G]⟩
  have hout : ∀ w, chan G (bern w) = bern (t + w * k) := by
    intro w; funext c
    cases c <;> simp [chan, G, bern, s] <;> ring
  have hu' : t + u * k = 1 - a := by
    have hkd : k * d = 1 - 2 * a := by rw [hk]; field_simp
    simp only [t]; nlinarith
  have hv' : t + v * k = a := by simp only [t]; ring
  have := KL_chan_le hG (bern_isProb (by linarith) hu1).nonneg
    (bern_isProb hv0 (by linarith)).nonneg hac
  rwa [hout, hout, hu', hv', KL_bern, KL_bern] at this

lemma dbin_boundary (a : ℝ) (ha0 : 0 < a) :
    dbin (1 - a) a = (1 - 2 * a) * Real.log ((1 - a) / a) := by
  unfold dbin
  rw [show 1 - (1 - a) = a by ring, show a / (1 - a) = ((1 - a) / a)⁻¹ by
    field_simp, Real.log_inv]
  ring

/-- **Eq. (binarylower)**: a test whose two orientation errors are both at most `α < 1/2`
certifies `D(P‖Q) ≥ (1 - 2α) log((1-α)/α)`. -/
theorem KL_ge_of_test_errors {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q)
    {A : α → ℝ} (hA : IsTest A) {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hfwd : 1 - a ≤ expect P A) (hrev : expect Q A ≤ a) :
    (1 - 2 * a) * Real.log ((1 - a) / a) ≤ KL P Q := by
  have hE1 : expect P A ≤ 1 := by
    calc expect P A ≤ expect P (fun _ => 1) := expect_mono hP.nonneg fun x => (hA x).2
      _ = 1 := expect_const P hP 1
  have hE0 : 0 ≤ expect Q A := by
    calc (0 : ℝ) = expect Q (fun _ => 0) := (expect_const Q hQ 0).symm
      _ ≤ _ := expect_mono hQ.nonneg fun x => (hA x).1
  rw [← dbin_boundary a ha0]
  exact (dbin_boundary_le ha0 ha hfwd hE1 hE0 hrev (absCont_bern_test hP hQ hPQ hA)).trans
    (dbin_le_KL hP hQ hPQ hA)

/-! ### Symmetric orientation contamination (Proposition `prop:contamination`) -/

/-- The mixture `(1-ε) P + ε Q`. -/
def mix (ε : ℝ) (P Q : α → ℝ) : α → ℝ := fun x => (1 - ε) * P x + ε * Q x

lemma mix_isProb {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) : IsProb (mix ε P Q) :=
  ⟨fun x => by unfold mix; nlinarith [hP.nonneg x, hQ.nonneg x],
    by simp [mix, sum_add_distrib, ← mul_sum, hP.sum_one, hQ.sum_one]⟩

/-- **Eq. (contamcap)**: the contaminated likelihood ratio is bounded, hence so is the KL. -/
theorem contam_KL_le {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 2) :
    KL (mix ε P Q) (mix ε Q P) ≤ Real.log ((1 - ε) / ε) := by
  have hPe := mix_isProb hP hQ h0.le (by linarith)
  calc KL (mix ε P Q) (mix ε Q P)
      ≤ ∑ x, mix ε P Q x * Real.log ((1 - ε) / ε) := by
        refine sum_le_sum fun x _ => ?_
        have hp := hP.nonneg x; have hq := hQ.nonneg x
        rcases (hPe.nonneg x).eq_or_lt with h | h
        · rw [← h]; simp
        · refine mul_le_mul_of_nonneg_left ?_ h.le
          have hQe : 0 < mix ε Q P x := by
            unfold mix at h ⊢
            by_contra hc; push_neg at hc
            nlinarith
          refine Real.log_le_log (div_pos h hQe) ?_
          rw [div_le_div_iff₀ hQe h0]
          unfold mix; nlinarith
    _ = Real.log ((1 - ε) / ε) := by rw [← sum_mul, hPe.sum_one, one_mul]

/-- **Eq. (contamtv)**: total variation is multiplied by `1 - 2ε`. -/
theorem contam_TV (P Q : α → ℝ) {ε : ℝ} (h1 : ε ≤ 1 / 2) :
    TV (mix ε P Q) (mix ε Q P) = (1 - 2 * ε) * TV P Q := by
  unfold TV mix
  have : ∀ x, |(1 - ε) * P x + ε * Q x - ((1 - ε) * Q x + ε * P x)| =
      (1 - 2 * ε) * |P x - Q x| := by
    intro x
    rw [show (1 - ε) * P x + ε * Q x - ((1 - ε) * Q x + ε * P x) = (1 - 2 * ε) * (P x - Q x)
      by ring, abs_mul, abs_of_nonneg (by linarith)]
  simp_rw [this, ← mul_sum]; ring

/-- Each contaminated law is within `ε` of the original law in total variation. -/
theorem contam_TV_close (P Q : α → ℝ) (hP : IsProb P) (hQ : IsProb Q) {ε : ℝ} (h0 : 0 ≤ ε) :
    TV (mix ε P Q) P ≤ ε := by
  unfold TV mix
  have : ∀ x, |(1 - ε) * P x + ε * Q x - P x| ≤ ε * (P x + Q x) := by
    intro x
    rw [show (1 - ε) * P x + ε * Q x - P x = ε * (Q x - P x) by ring, abs_mul,
      abs_of_nonneg h0]
    have := abs_sub_le_iff.mpr (⟨by linarith [hP.nonneg x, hQ.nonneg x],
      by linarith [hP.nonneg x, hQ.nonneg x]⟩ : Q x - P x ≤ P x + Q x ∧ P x - Q x ≤ P x + Q x)
    exact mul_le_mul_of_nonneg_left this h0
  calc 1 / 2 * ∑ x, |(1 - ε) * P x + ε * Q x - P x| ≤ 1 / 2 * ∑ x, ε * (P x + Q x) := by
        gcongr with x; exact this x
    _ = ε := by rw [← mul_sum, sum_add_distrib, hP.sum_one, hQ.sum_one]; ring

/-- **Eq. (contamchannel)**: the contamination is produced by one hypothesis-independent
channel which applies the public reversal `τ` with probability `ε`. -/
def contamChan [DecidableEq α] (ε : ℝ) (τ : α → α) : α → α → ℝ :=
  fun r r' => (1 - ε) * (if r' = r then 1 else 0) + ε * (if r' = τ r then 1 else 0)

theorem contamChan_isChannel [DecidableEq α] {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (τ : α → α) :
    IsChannel (contamChan ε τ) :=
  ⟨fun r r' => by unfold contamChan; split_ifs <;> nlinarith, fun r => by
    simp [contamChan, sum_add_distrib]⟩

theorem chan_contamChan [DecidableEq α] (ε : ℝ) (P : α → ℝ) (τ : α → α)
    (hτ : Function.Involutive τ) :
    chan (contamChan ε τ) P = mix ε P (fun y => P (τ y)) ∧
      chan (contamChan ε τ) (fun y => P (τ y)) = mix ε (fun y => P (τ y)) P := by
  have key : ∀ (R : α → ℝ) y, chan (contamChan ε τ) R y = (1 - ε) * R y + ε * R (τ y) := by
    intro R y
    unfold chan contamChan
    simp only [mul_add, sum_add_distrib]
    congr 1
    · simp [mul_comm, mul_ite]
    · have : ∀ x, (y = τ x ↔ x = τ y) := fun x =>
        ⟨fun h => by rw [h, hτ x], fun h => by rw [h, hτ y]⟩
      simp only [this, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
      ring
  refine ⟨funext fun y => ?_, funext fun y => ?_⟩
  · rw [key]; rfl
  · rw [key, hτ y]; rfl

/-! ### Coupling and transfer of advantage (Eq. (transferadv)) -/

/-- If two laws are within `δ` in total variation, every test changes by at most `δ`. -/
lemma expect_close {P P' : α → ℝ} (hP : IsProb P) (hP' : IsProb P') {A : α → ℝ}
    (hA : IsTest A) {δ : ℝ} (h : TV P' P ≤ δ) : |expect P' A - expect P A| ≤ δ :=
  (adv_le_TV hP' hP hA).trans h

/-- **Coupling inequality**: if `J` couples `P'` and `P` and the two coordinates differ with
probability at most `δ`, then `TV(P', P) ≤ δ`. -/
theorem TV_le_of_coupling [DecidableEq α] {J : α × α → ℝ} (hJ : ∀ z, 0 ≤ J z)
    {P P' : α → ℝ} (h1 : ∀ x, P' x = ∑ y, J (x, y)) (h2 : ∀ x, P x = ∑ y, J (y, x)) {δ : ℝ}
    (hδ : ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), J z ≤ δ) : TV P' P ≤ δ := by
  unfold TV
  have hx : ∀ x, |P' x - P x| ≤ ∑ y ∈ univ.filter (fun y => y ≠ x), (J (x, y) + J (y, x)) := by
    intro x
    rw [h1, h2, ← sum_filter_add_sum_filter_not univ (fun y => y ≠ x) (fun y => J (x, y)),
      ← sum_filter_add_sum_filter_not univ (fun y => y ≠ x) (fun y => J (y, x))]
    have : ∑ y ∈ univ.filter (fun y => ¬ y ≠ x), J (x, y) =
        ∑ y ∈ univ.filter (fun y => ¬ y ≠ x), J (y, x) := by
      refine sum_congr rfl fun y hy => ?_
      simp only [mem_filter, mem_univ, true_and, not_not] at hy
      rw [hy]
    rw [this, add_sub_add_right_eq_sub, sum_add_distrib]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (sum_nonneg fun y _ => hJ _), abs_of_nonneg (sum_nonneg fun y _ => hJ _)]
  have hsum : ∑ x, ∑ y ∈ univ.filter (fun y => y ≠ x), (J (x, y) + J (y, x)) =
      2 * ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), J z := by
    simp_rw [sum_add_distrib]
    have hR : ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), J z =
        ∑ a, ∑ b, if a ≠ b then J (a, b) else 0 := by
      rw [sum_filter, Fintype.sum_prod_type]
    have e1 : ∑ x, ∑ y ∈ univ.filter (fun y => y ≠ x), J (x, y) =
        ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), J z := by
      rw [hR]
      refine sum_congr rfl fun x _ => ?_
      rw [sum_filter]
      simp only [ne_comm]
    have e2 : ∑ x, ∑ y ∈ univ.filter (fun y => y ≠ x), J (y, x) =
        ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), J z := by
      rw [hR]
      simp_rw [sum_filter]
      rw [sum_comm]
    rw [e1, e2]; ring
  calc 1 / 2 * ∑ x, |P' x - P x| ≤ 1 / 2 * ∑ x, ∑ y ∈ univ.filter (fun y => y ≠ x),
        (J (x, y) + J (y, x)) := by gcongr with x; exact hx x
    _ ≤ δ := by rw [hsum]; linarith

/-- **Eq. (transferadv)**: an imperfect recorder whose outputs are within `δ` of the ideal
outputs (e.g. by a coupling with failure probability `δ`) under each orientation changes any
distinguishing advantage by at most `2δ`. -/
theorem adv_transfer {P Q P' Q' : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hP' : IsProb P')
    (hQ' : IsProb Q') {A : α → ℝ} (hA : IsTest A) {δ : ℝ} (h1 : TV P' P ≤ δ)
    (h2 : TV Q' Q ≤ δ) : adv P' Q' A ≤ adv P Q A + 2 * δ := by
  unfold adv
  have a1 := expect_close hP hP' hA h1
  have a2 := expect_close hQ hQ' hA h2
  rw [abs_sub_comm] at a2
  have t1 := abs_sub_le (expect P' A) (expect P A) (expect Q' A)
  have t2 := abs_sub_le (expect P A) (expect Q A) (expect Q' A)
  linarith

/-! ### Hellinger affinity and Rényi divergences (Appendix `app:weakdrive`) -/

/-- Hellinger affinity `ρ = ∑ √(P Q)`. -/
noncomputable def hellinger (P Q : α → ℝ) : ℝ := ∑ x, Real.sqrt (P x * Q x)

/-- Rényi divergence of order `a ≠ 1`. -/
noncomputable def renyi (a : ℝ) (P Q : α → ℝ) : ℝ :=
  1 / (a - 1) * Real.log (∑ x, P x ^ a * Q x ^ (1 - a))

lemma TV_eq_one_sub_sum_min {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    TV P Q = 1 - ∑ x, min (P x) (Q x) := by
  unfold TV
  have : ∀ x, |P x - Q x| = P x + Q x - 2 * min (P x) (Q x) := by
    intro x
    rcases le_total (P x) (Q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  simp_rw [this, sum_sub_distrib, sum_add_distrib, hP.sum_one, hQ.sum_one, ← mul_sum]
  ring

/-- **Eq. (hellingertv)**: `1 - ρ ≤ TV(P,Q) ≤ √(1 - ρ²)`. -/
theorem hellinger_TV_bounds {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    1 - hellinger P Q ≤ TV P Q ∧ TV P Q ≤ Real.sqrt (1 - hellinger P Q ^ 2) := by
  constructor
  · rw [TV_eq_one_sub_sum_min hP hQ]
    have : ∀ x, min (P x) (Q x) ≤ Real.sqrt (P x * Q x) := by
      intro x
      apply Real.le_sqrt_of_sq_le
      rcases le_total (P x) (Q x) with h | h
      · rw [min_eq_left h]; nlinarith [hP.nonneg x]
      · rw [min_eq_right h]; nlinarith [hQ.nonneg x]
    unfold hellinger
    linarith [sum_le_sum fun x (_ : x ∈ univ) => this x]
  · have hTV : 0 ≤ TV P Q := by unfold TV; positivity
    apply Real.le_sqrt_of_sq_le
    set a := fun x => Real.sqrt (P x)
    set b := fun x => Real.sqrt (Q x)
    have ha : ∀ x, a x ^ 2 = P x := fun x => Real.sq_sqrt (hP.nonneg x)
    have hb : ∀ x, b x ^ 2 = Q x := fun x => Real.sq_sqrt (hQ.nonneg x)
    have hab : ∀ x, a x * b x = Real.sqrt (P x * Q x) := fun x =>
      (Real.sqrt_mul (hP.nonneg x) _).symm
    have habs : ∀ x, |P x - Q x| = |a x - b x| * (a x + b x) := by
      intro x
      rw [← ha, ← hb, show a x ^ 2 - b x ^ 2 = (a x - b x) * (a x + b x) by ring, abs_mul,
        abs_of_nonneg (a := a x + b x) (by positivity)]
    have CS := sum_mul_sq_le_sq_mul_sq univ (fun x => |a x - b x|) (fun x => a x + b x)
    have e1 : ∑ x, |a x - b x| ^ 2 = 2 - 2 * hellinger P Q := by
      unfold hellinger
      simp_rw [sq_abs, sub_sq, sum_add_distrib, sum_sub_distrib, ha, hb, hP.sum_one,
        hQ.sum_one, mul_assoc, ← mul_sum, hab]
      ring
    have e2 : ∑ x, (a x + b x) ^ 2 = 2 + 2 * hellinger P Q := by
      unfold hellinger
      simp_rw [add_sq, sum_add_distrib, ha, hb, hP.sum_one, hQ.sum_one, mul_assoc, ← mul_sum,
        hab]
      ring
    rw [e1, e2] at CS
    unfold TV
    simp_rw [habs]
    nlinarith

end Arrow

end BinaryPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Computation
    ════════════════════════════════════════════════════════════════════ -/

section ComputationPart

/-!
# Computational resources, negligible functions and hybrid arguments

The paper measures observers by randomised Boolean circuits of bounded size (Eq. (adv)).
Circuit complexity itself is *not* re-developed here: a resource-bounded observer class is
represented abstractly by a set `T` of randomised tests (`T s` = tests computable by circuits of
size at most `s`). The only facts about circuits that the paper's reductions use are
*closure properties* (composing a circuit of size `s` with an efficient sampler / channel costs
an additional polynomial `c`). These established facts of complexity theory are carried as
explicit hypotheses of each reduction theorem.

* `AdvLE T P Q b` : every test of the class has advantage at most `b`
  (i.e. `Adv_s(P,Q) ≤ b`).
* `Negligible`, `PolyBounded` and their closure properties.
* The product (independent-records) law and the hybrid argument of
  Proposition `prop:many`.
* Eq. (compdpi): efficient hypothesis-independent post-processing.
-/


open Finset Real Filter

namespace Arrow

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `Adv_T(P,Q) ≤ b`: every randomised test in the class `T` has advantage at most `b`. -/
def AdvLE (T : Set (α → ℝ)) (P Q : α → ℝ) (b : ℝ) : Prop :=
  ∀ A ∈ T, IsTest A → adv P Q A ≤ b

/-- A function `ε(n)` is negligible: for every `c` it is eventually at most `n^{-c}`. -/
def Negligible (ε : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, |ε n| ≤ 1 / (n : ℝ) ^ c

/-- A function is polynomially bounded. -/
def PolyBounded (q : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, ∀ᶠ n : ℕ in atTop, |q n| ≤ (n : ℝ) ^ k

/-- A size function `s : ℕ → ℕ` is polynomially bounded. -/
def PolySize (s : ℕ → ℕ) : Prop := PolyBounded (fun n => (s n : ℝ))

lemma Negligible.mono {ε δ : ℕ → ℝ} (hε : Negligible ε) (h : ∀ᶠ n in atTop, |δ n| ≤ |ε n|) :
    Negligible δ := fun c => (hε c).mp (h.mono fun _ h1 h2 => h1.trans h2)

lemma Negligible.zero : Negligible (fun _ => 0) := fun _ =>
  Filter.Eventually.of_forall fun _ => by simp

lemma Negligible.mul_poly {ε q : ℕ → ℝ} (hε : Negligible ε) (hq : PolyBounded q) :
    Negligible (fun n => q n * ε n) := by
  obtain ⟨k, hk⟩ := hq
  intro c
  filter_upwards [hε (c + k), hk, eventually_ge_atTop 1] with n h1 h2 h3
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h3
  have hpos : 0 < (n : ℝ) ^ (c + k) := by positivity
  rw [abs_mul]
  calc |q n| * |ε n| ≤ (n : ℝ) ^ k * (1 / (n : ℝ) ^ (c + k)) :=
        mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = 1 / (n : ℝ) ^ c := by
        rw [pow_add]; field_simp

lemma PolyBounded.const (C : ℝ) : PolyBounded (fun _ => C) := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (Nat.ceil |C|)] with n hn
  rw [pow_one]
  exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

lemma Negligible.const_mul {ε : ℕ → ℝ} (hε : Negligible ε) (C : ℝ) :
    Negligible (fun n => C * ε n) := hε.mul_poly (PolyBounded.const C)

lemma Negligible.add {ε δ : ℕ → ℝ} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (fun n => ε n + δ n) := by
  intro c
  filter_upwards [hε (c + 1), hδ (c + 1), eventually_ge_atTop 2] with n h1 h2 h3
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h3
  have hpos : 0 < (n : ℝ) ^ c := by positivity
  calc |ε n + δ n| ≤ |ε n| + |δ n| := abs_add_le _ _
    _ ≤ 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_le_add h1 h2
    _ = 2 / n * (1 / (n : ℝ) ^ c) := by rw [pow_succ]; field_simp; ring
    _ ≤ 1 * (1 / (n : ℝ) ^ c) := by
        gcongr; rw [div_le_one (by linarith)]; exact hn
    _ = _ := one_mul _

/-- Negligible functions tend to zero. -/
lemma Negligible.tendsto_zero {ε : ℕ → ℝ} (hε : Negligible ε) : Tendsto ε atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 1) atTop (nhds 0) := by
    simp only [pow_one]; exact tendsto_one_div_atTop_nhds_zero_nat
  exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) (hε 1) h1

lemma PolySize.add {s t : ℕ → ℕ} (hs : PolySize s) (ht : PolySize t) :
    PolySize (fun n => s n + t n) := by
  obtain ⟨k, hk⟩ := hs; obtain ⟨l, hl⟩ := ht
  refine ⟨k + l + 1, ?_⟩
  filter_upwards [hk, hl, eventually_ge_atTop 2] with n h1 h2 h3
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h3
  simp only [Nat.cast_add, Nat.cast_nonneg, abs_of_nonneg] at h1 h2 ⊢
  rw [abs_of_nonneg (by positivity)]
  have e1 : (n : ℝ) ^ k ≤ (n : ℝ) ^ (k + l) := pow_le_pow_right₀ (by linarith) (by omega)
  have e2 : (n : ℝ) ^ l ≤ (n : ℝ) ^ (k + l) := pow_le_pow_right₀ (by linarith) (by omega)
  have : (n : ℝ) ^ (k + l + 1) = (n : ℝ) ^ (k + l) * n := pow_succ _ _
  have : 0 < (n : ℝ) ^ (k + l) := by positivity
  nlinarith

/-! ### Uniform and product laws -/

/-- The uniform law on a finite type. -/
noncomputable def unif (α : Type*) [Fintype α] : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ)

lemma unif_isProb [Nonempty α] : IsProb (unif α) :=
  ⟨fun _ => by unfold unif; positivity, by
    simp [unif, Finset.card_univ]⟩

/-- Independent product of two laws. -/
def prodLaw (P : α → ℝ) (Q : β → ℝ) : α × β → ℝ := fun z => P z.1 * Q z.2

lemma prodLaw_isProb {P : α → ℝ} {Q : β → ℝ} (hP : IsProb P) (hQ : IsProb Q) :
    IsProb (prodLaw P Q) :=
  ⟨fun z => mul_nonneg (hP.nonneg _) (hQ.nonneg _), by
    rw [Fintype.sum_prod_type]; simp [prodLaw, ← mul_sum, hP.sum_one, hQ.sum_one]⟩

lemma expect_prodLaw (P : α → ℝ) (Q : β → ℝ) (f : α × β → ℝ) :
    expect (prodLaw P Q) f = ∑ a, P a * ∑ b, Q b * f (a, b) := by
  unfold expect prodLaw
  rw [Fintype.sum_prod_type]
  simp_rw [mul_sum, mul_assoc]

/-- Tensoring both laws with the same independent law leaves KL unchanged. -/
lemma KL_prodLaw_left {U : α → ℝ} (hU : IsProb U) (P Q : β → ℝ) :
    KL (prodLaw U P) (prodLaw U Q) = KL P Q := by
  unfold KL prodLaw
  rw [Fintype.sum_prod_type]
  have : ∀ a, ∑ b, U a * P b * Real.log (U a * P b / (U a * Q b)) =
      U a * ∑ b, P b * Real.log (P b / Q b) := by
    intro a
    rcases (hU.nonneg a).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [mul_sum]; refine sum_congr rfl fun b _ => ?_
      rw [mul_div_mul_left _ _ h.ne']; ring
  simp_rw [this, ← sum_mul, hU.sum_one, one_mul]

/-- Tensoring both laws with the same independent law leaves TV unchanged. -/
lemma TV_prodLaw_left {U : α → ℝ} (hU : IsProb U) (P Q : β → ℝ) :
    TV (prodLaw U P) (prodLaw U Q) = TV P Q := by
  unfold TV prodLaw
  rw [Fintype.sum_prod_type]
  congr 1
  have : ∀ a, ∑ b, |U a * P b - U a * Q b| = U a * ∑ b, |P b - Q b| := by
    intro a; rw [mul_sum]; refine sum_congr rfl fun b _ => ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg (hU.nonneg a)]
  simp_rw [this, ← sum_mul, hU.sum_one, one_mul]

/-! ### Independent records and the hybrid argument (Proposition `prop:many`) -/

/-- Law of `q` independent records, the `k`-th record having law `w k`. -/
def piLaw {q : ℕ} (w : Fin q → α → ℝ) : (Fin q → α) → ℝ := fun x => ∏ k, w k (x k)

/-- `q` independent copies of one law. -/
def iidLaw (q : ℕ) (P : α → ℝ) : (Fin q → α) → ℝ := piLaw (fun _ => P)

lemma sum_piLaw {q : ℕ} (w : Fin q → α → ℝ) : ∑ x, piLaw w x = ∏ k, ∑ a, w k a := by
  unfold piLaw; rw [Fintype.prod_sum]

lemma piLaw_isProb {q : ℕ} {w : Fin q → α → ℝ} (hw : ∀ k, IsProb (w k)) : IsProb (piLaw w) :=
  ⟨fun x => prod_nonneg fun k _ => (hw k).nonneg _, by
    rw [sum_piLaw]; simp [(hw _).sum_one]⟩

/-- The single-record test used for the `i`-th hybrid transition: the record under test is
placed in position `i`, and the other records are sampled independently from `w`. -/
noncomputable def embedTest [DecidableEq α] {q : ℕ} (i : Fin q) (w : Fin q → α → ℝ)
    (A : (Fin q → α) → ℝ) : α → ℝ :=
  fun r => ∑ y : {k // k ≠ i} → α, (∏ k : {k // k ≠ i}, w k (y k)) *
    A ((Equiv.piSplitAt i _).symm (r, y))

omit [Fintype α] in
lemma piSplitAt_symm_self [DecidableEq α] {q : ℕ} (i : Fin q) (r : α) (y : {k // k ≠ i} → α) :
    (Equiv.piSplitAt i (fun _ => α)).symm (r, y) i = r := by
  simp [Equiv.piSplitAt_symm_apply]

omit [Fintype α] in
lemma piSplitAt_symm_ne [DecidableEq α] {q : ℕ} (i : Fin q) (r : α) (y : {k // k ≠ i} → α)
    (k : {k // k ≠ i}) : (Equiv.piSplitAt i (fun _ => α)).symm (r, y) k = y k := by
  simp [Equiv.piSplitAt_symm_apply, k.2]

lemma expect_piLaw_split [DecidableEq α] {q : ℕ} (i : Fin q) (w : Fin q → α → ℝ)
    (A : (Fin q → α) → ℝ) :
    expect (piLaw w) A = ∑ r, w i r * embedTest i w A r := by
  unfold expect piLaw embedTest
  rw [← (Equiv.piSplitAt i (fun _ => α)).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun r _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [piSplitAt_symm_self, piSplitAt_symm_ne]
  ring

lemma embedTest_isTest [DecidableEq α] {q : ℕ} (i : Fin q) {w : Fin q → α → ℝ}
    (hw : ∀ k, IsProb (w k)) {A : (Fin q → α) → ℝ} (hA : IsTest A) :
    IsTest (embedTest i w A) := by
  have hsum : ∑ y : {k // k ≠ i} → α, ∏ k : {k // k ≠ i}, w k (y k) = 1 := by
    rw [← Fintype.prod_sum (f := fun (k : {k // k ≠ i}) a => w k a)]
    simp [(hw _).sum_one]
  have hnn : ∀ y : {k // k ≠ i} → α, 0 ≤ ∏ k : {k // k ≠ i}, w k (y k) :=
    fun y => prod_nonneg fun k _ => (hw k).nonneg _
  intro r
  unfold embedTest
  constructor
  · exact sum_nonneg fun y _ => mul_nonneg (hnn y) (hA _).1
  · calc _ ≤ ∑ y : {k // k ≠ i} → α, (∏ k : {k // k ≠ i}, w k (y k)) * 1 :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hA _).2 (hnn y)
      _ = 1 := by simp [hsum]

/-- Hybrid weights: the first `j` records follow `Q`, the remaining ones follow `P`. -/
def hybridW {q : ℕ} (j : ℕ) (P Q : α → ℝ) : Fin q → α → ℝ :=
  fun k => if (k : ℕ) < j then Q else P

/-- **Hybrid inequality** for independent records: the advantage of a test on `q` records is
at most the sum of the advantages of the `q` single-record embedded tests. -/
theorem adv_iid_le_sum [DecidableEq α] {q : ℕ} (P Q : α → ℝ) (A : (Fin q → α) → ℝ) :
    adv (iidLaw q P) (iidLaw q Q) A ≤
      ∑ i : Fin q, adv P Q (embedTest i (hybridW i P Q) A) := by
  set H : ℕ → ℝ := fun j => expect (piLaw (hybridW (q := q) j P Q)) A
  have h0 : H 0 = expect (iidLaw q P) A := by
    simp only [H, iidLaw]
    rw [show hybridW (q := q) 0 P Q = fun _ => P from funext fun k => by simp [hybridW]]
  have hq : H q = expect (iidLaw q Q) A := by
    simp only [H, iidLaw]
    rw [show hybridW (q := q) q P Q = fun _ => Q from funext fun k => by simp [hybridW, k.isLt]]
  have hstep : ∀ i : Fin q, H i - H (i + 1) =
      expect P (embedTest i (hybridW i P Q) A) - expect Q (embedTest i (hybridW i P Q) A) := by
    intro i
    have e : embedTest i (hybridW (q := q) (i + 1) P Q) A = embedTest i (hybridW i P Q) A := by
      funext r; unfold embedTest; refine sum_congr rfl fun y _ => ?_
      congr 1; refine prod_congr rfl fun k _ => ?_
      have : (k : ℕ) ≠ i := fun h => k.2 (Fin.ext h)
      have hk : ((k : ℕ) < i + 1 ↔ (k : ℕ) < i) := by omega
      simp only [hybridW, hk]
    simp only [H]
    rw [expect_piLaw_split i, expect_piLaw_split i, e]
    simp [hybridW, expect]
  unfold adv
  rw [← h0, ← hq]
  have tel : H 0 - H q = ∑ i : Fin q, (H i - H (i + 1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => H i - H (i + 1)), ← neg_sub, ← sum_range_sub H q]
    simp
  rw [tel]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  rw [hstep]

/-- **Proposition `prop:many`** (abstract form): if every embedded single-record test of a
size-`s` test on `q` records lies in the single-record class `T₁` and that class has advantage
at most `b`, then the `q`-record advantage is at most `q b`. -/
theorem advLE_iid [DecidableEq α] {q : ℕ} {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q)
    (Tq : Set ((Fin q → α) → ℝ)) (T₁ : Set (α → ℝ)) {b : ℝ} (hb : AdvLE T₁ P Q b)
    (hclos : ∀ A ∈ Tq, ∀ i : Fin q, embedTest i (hybridW i P Q) A ∈ T₁) :
    AdvLE Tq (iidLaw q P) (iidLaw q Q) (q * b) := by
  intro A hA hAt
  have hw : ∀ (i : Fin q) k, IsProb (hybridW (q := q) i P Q k) := fun i k => by
    unfold hybridW; split_ifs <;> assumption
  refine (adv_iid_le_sum P Q A).trans ?_
  calc ∑ i : Fin q, adv P Q (embedTest i (hybridW i P Q) A) ≤ ∑ _i : Fin q, b :=
        sum_le_sum fun i _ => hb _ (hclos A hA i) (embedTest_isTest i (hw i) hAt)
    _ = q * b := by simp

/-- The statistical evidence of independent records adds up: `D(P^{⊗q}‖Q^{⊗q}) = q D(P‖Q)`. -/
theorem KL_iidLaw {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (hPQ : AbsCont P Q) (q : ℕ) :
    KL (iidLaw q P) (iidLaw q Q) = q * KL P Q := by
  induction q with
  | zero => simp [KL, iidLaw, piLaw]
  | succ q ih =>
    -- split off the first record
    have e : ∀ (R : α → ℝ), iidLaw (q + 1) R =
        fun x => R (x 0) * iidLaw q R (Fin.tail x) := by
      intro R; funext x; simp [iidLaw, piLaw, Fin.prod_univ_succ, Fin.tail]
    have hPq : IsProb (iidLaw q P) := piLaw_isProb fun _ => hP
    have key : KL (iidLaw (q + 1) P) (iidLaw (q + 1) Q) =
        KL (prodLaw P (iidLaw q P)) (prodLaw Q (iidLaw q Q)) := by
      rw [e, e]
      unfold KL
      rw [← (Fin.consEquiv (fun _ : Fin (q + 1) => α)).sum_comp, Fintype.sum_prod_type]
      simp [Fin.consEquiv, prodLaw, Fintype.sum_prod_type]
    rw [key]
    unfold KL prodLaw
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b, P a * iidLaw q P b * Real.log (P a * iidLaw q P b / (Q a * iidLaw q Q b))
        = iidLaw q P b * (P a * Real.log (P a / Q a)) +
          P a * (iidLaw q P b * Real.log (iidLaw q P b / iidLaw q Q b)) := by
      intro a b
      rcases (hP.nonneg a).eq_or_lt with h | h
      · rw [← h]; simp
      rcases (hPq.nonneg b).eq_or_lt with h' | h'
      · rw [← h']; simp
      have hq : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (fun h0 => h.ne' (hPQ a h0.symm))
      have hqb : 0 < iidLaw q Q b := by
        refine lt_of_le_of_ne ((piLaw_isProb (w := fun _ => Q) (fun _ => hQ)).nonneg b)
          (fun h1 => ?_)
        have h1' : ∏ k, Q (b k) = 0 := h1.symm
        obtain ⟨k, -, hk⟩ := prod_eq_zero_iff.mp h1'
        have : iidLaw q P b = 0 := show ∏ k, P (b k) = 0 from prod_eq_zero (mem_univ k) (hPQ _ hk)
        exact h'.ne' this
      rw [show P a * iidLaw q P b / (Q a * iidLaw q Q b) =
        (P a / Q a) * (iidLaw q P b / iidLaw q Q b) by field_simp,
        Real.log_mul (by positivity) (by positivity)]
      ring
    simp_rw [hterm, sum_add_distrib, ← mul_sum, ← sum_mul]
    rw [hP.sum_one, hPq.sum_one]
    unfold KL at ih
    rw [ih]; simp only [one_mul]; push_cast; ring

end Arrow

end ComputationPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Universal
    ════════════════════════════════════════════════════════════════════ -/

section UniversalPart

/-!
# Section 4: a universal construction using one hard-core bit

* The encoder `E(s,x) = (F(s), θ^{h(s)} x)` and the public reversal `τ(y,z) = (y, θ z)`.
* Lemma `lem:equivariant`: `E` is a bijection, `E ∘ θ̃ = τ ∘ E`, and `Q = τ_* P`.
* Theorem `thm:universal`: KL and TV are preserved (Eqs. (preservekl), (preservetv)) and every
  test in the observer class has advantage at most `2 ε_hc` (Eq. (mainsecurity)), via an
  explicit reduction to the decisional hard-core assumption (Eq. (hardcore)).
* The asymptotic form (negligible advantage for every polynomial size).
* The information-theoretic remark: the mutual information between the orientation label and
  the record is at most `log 2`.
* Eq. (compdpi): efficient post-processing.
* Proposition `prop:clean`: a clean reversible encoder would invert the permutation.
-/


open Finset Real Filter

namespace Arrow

variable {D X : Type*} [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X]

/-- `θ^b` for a bit `b` (`θ^0 = id`, `θ^1 = θ`). -/
def thetaPow (θ : X → X) (b : Bool) : X → X := if b then θ else id

omit [Fintype X] [DecidableEq X] in
lemma thetaPow_comm (θ : X → X) (b : Bool) (x : X) : thetaPow θ b (θ x) = θ (thetaPow θ b x) := by
  cases b <;> rfl

omit [Fintype X] [DecidableEq X] in
lemma thetaPow_involutive {θ : X → X} (hθ : Function.Involutive θ) (b : Bool) :
    Function.Involutive (thetaPow θ b) := by
  cases b
  · exact fun x => rfl
  · exact hθ

/-- The one-bit encoder `E(s,x) = (F(s), θ^{h(s)} x)` (Eq. (encoder)). -/
def encoder (F : D ≃ D) (h : D → Bool) (θ : X → X) : D × X → D × X :=
  fun sx => (F sx.1, thetaPow θ (h sx.1) sx.2)

/-- The public reversal on records `τ(y,z) = (y, θ z)` (Eq. (encoder)). -/
def recRev (θ : X → X) : D × X → D × X := fun yz => (yz.1, θ yz.2)

/-- The physical (raw) reversal `θ̃(s,x) = (s, θ x)`; the seed is time-even. -/
def rawRev (θ : X → X) : D × X → D × X := fun sx => (sx.1, θ sx.2)

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X] in
/-- **Lemma `lem:equivariant` (commutation)**: `E ∘ θ̃ = τ ∘ E`. -/
theorem encoder_comm (F : D ≃ D) (h : D → Bool) (θ : X → X) (sx : D × X) :
    encoder F h θ (rawRev θ sx) = recRev θ (encoder F h θ sx) := by
  simp [encoder, rawRev, recRev, thetaPow_comm]

/-- The encoder is a bijection (Lemma `lem:equivariant`); its inverse is a mathematical
operation, not a promised efficient algorithm. -/
def encoderEquiv (F : D ≃ D) (h : D → Bool) (θ : X → X) (hθ : Function.Involutive θ) :
    D × X ≃ D × X where
  toFun := encoder F h θ
  invFun yz := (F.symm yz.1, thetaPow θ (h (F.symm yz.1)) yz.2)
  left_inv sx := by
    simp [encoder, thetaPow_involutive hθ _ sx.2]
  right_inv yz := by
    simp [encoder, thetaPow_involutive hθ _ yz.2]

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X] in
lemma encoder_bijective (F : D ≃ D) (h : D → Bool) (θ : X → X) (hθ : Function.Involutive θ) :
    Function.Bijective (encoder F h θ) := (encoderEquiv F h θ hθ).bijective

/-- The encoded record law `E_*(U_d ⊗ P⁰)`. -/
noncomputable def encLaw (F : D ≃ D) (h : D → Bool) (θ : X → X) (P0 : X → ℝ) : D × X → ℝ :=
  push (encoder F h θ) (prodLaw (unif D) P0)

/-- **Lemma `lem:equivariant` (consequence)**: `Q = τ_* P`, i.e. the encoded reversed law is the
forward encoded law composed with the public reversal. -/
theorem encLaw_reverse (F : D ≃ D) (h : D → Bool) {θ : X → X} (hθ : Function.Involutive θ)
    (P0 : X → ℝ) :
    encLaw F h θ (fun x => P0 (θ x)) = fun r => encLaw F h θ P0 (recRev θ r) := by
  funext r
  have e1 : encoder F h θ = encoderEquiv F h θ hθ := rfl
  unfold encLaw
  rw [e1, push_equiv, push_equiv]
  have key : (encoderEquiv F h θ hθ).symm (recRev θ r) =
      rawRev θ ((encoderEquiv F h θ hθ).symm r) := by
    apply (encoderEquiv F h θ hθ).injective
    rw [Equiv.apply_symm_apply]
    change recRev θ r = encoder F h θ (rawRev θ ((encoderEquiv F h θ hθ).symm r))
    rw [encoder_comm]
    change recRev θ r = recRev θ ((encoderEquiv F h θ hθ) ((encoderEquiv F h θ hθ).symm r))
    rw [Equiv.apply_symm_apply]
  beta_reduce
  rw [key]
  rfl

lemma encLaw_isProb [Nonempty D] (F : D ≃ D) (h : D → Bool) (θ : X → X) {P0 : X → ℝ}
    (hP0 : IsProb P0) : IsProb (encLaw F h θ P0) :=
  (prodLaw_isProb unif_isProb hP0).push _

/-! ### The hard-core experiment and the reduction -/

/-- The real hard-core experiment `(F(S), h(S))`, `S` uniform. -/
noncomputable def hcReal (F : D ≃ D) (h : D → Bool) : D × Bool → ℝ :=
  push (fun s => (F s, h s)) (unif D)

/-- The ideal hard-core experiment `(F(S), B)`, `B` an independent fair bit. -/
noncomputable def hcIdeal (F : D ≃ D) : D × Bool → ℝ :=
  push (fun sb : D × Bool => (F sb.1, sb.2)) (prodLaw (unif D) (unif Bool))

/-- The reduction used in Theorem `thm:universal`: given a challenge `(y, b)`, sample
`X ∼ P⁰` and feed `(y, θ^b X)` to the record distinguisher. -/
def redTest (θ : X → X) (P0 : X → ℝ) (A : D × X → ℝ) : D × Bool → ℝ :=
  fun yb => ∑ x, P0 x * A (yb.1, thetaPow θ yb.2 x)

omit [DecidableEq D] [Fintype D] [DecidableEq X] in
lemma redTest_isTest (θ : X → X) {P0 : X → ℝ} (hP0 : IsProb P0) {A : D × X → ℝ}
    (hA : IsTest A) : IsTest (redTest θ P0 A) := by
  intro yb
  unfold redTest
  constructor
  · exact sum_nonneg fun x _ => mul_nonneg (hP0.nonneg x) (hA _).1
  · calc _ ≤ ∑ x, P0 x * 1 := sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hA _).2
          (hP0.nonneg x)
      _ = 1 := by simp [hP0.sum_one]

lemma expect_hcReal_redTest (F : D ≃ D) (h : D → Bool) (θ : X → X) (P0 : X → ℝ)
    (A : D × X → ℝ) :
    expect (hcReal F h) (redTest θ P0 A) = expect (encLaw F h θ P0) A := by
  unfold hcReal encLaw
  rw [expect_push, expect_push, expect_prodLaw]
  unfold expect redTest encoder
  rfl

omit [DecidableEq X] in
lemma expect_hcIdeal_redTest (F : D ≃ D) {θ : X → X} (hθ : Function.Involutive θ)
    (P0 : X → ℝ) (A : D × X → ℝ) :
    expect (hcIdeal F) (redTest θ P0 A) = expect (hcIdeal F) (redTest θ (fun x => P0 (θ x)) A) := by
  unfold hcIdeal
  rw [expect_push, expect_push, expect_prodLaw, expect_prodLaw]
  refine sum_congr rfl fun s _ => ?_
  congr 1
  simp only [Fintype.sum_bool, redTest, thetaPow, if_true, Bool.false_eq_true, if_false, id]
  have e1 : ∑ x, P0 (θ x) * A (F s, θ x) = ∑ x, P0 x * A (F s, x) :=
    Fintype.sum_equiv (Function.Involutive.toPerm θ hθ) _ _ (fun x => by simp)
  have e2 : ∑ x, P0 (θ x) * A (F s, x) = ∑ x, P0 x * A (F s, θ x) :=
    Fintype.sum_equiv (Function.Involutive.toPerm θ hθ) _ _ (fun x => by simp [hθ x])
  rw [e1, e2]
  simp only [unif]
  ring

/-- **Theorem `thm:universal` (information-preserving computational concealment).**

For any finite raw law `P⁰` and involution `θ`, with `Q⁰ = θ_* P⁰`, the encoded laws
`P = E_*(U ⊗ P⁰)`, `Q = E_*(U ⊗ Q⁰)` satisfy
* `D(P‖Q) = D(P⁰‖Q⁰)` (Eq. (preservekl)),
* `TV(P,Q) = TV(P⁰,Q⁰)` (Eq. (preservetv)),
* if every hard-core test of the class `TH` has advantage at most `e` and the reductions of
  the tests of the record class `TR` (sampling `X ∼ P⁰` or `X ∼ Q⁰`, applying `θ^b`) lie in
  `TH`, then every test of `TR` has advantage at most `2e` (Eq. (mainsecurity)). -/
theorem universal_concealment [Nonempty D] (F : D ≃ D) (h : D → Bool) {θ : X → X}
    (hθ : Function.Involutive θ) {P0 : X → ℝ} (hP0 : IsProb P0) :
    KL (encLaw F h θ P0) (encLaw F h θ (fun x => P0 (θ x))) = KL P0 (fun x => P0 (θ x)) ∧
    TV (encLaw F h θ P0) (encLaw F h θ (fun x => P0 (θ x))) = TV P0 (fun x => P0 (θ x)) ∧
    ∀ (TR : Set (D × X → ℝ)) (TH : Set (D × Bool → ℝ)) (e : ℝ),
      AdvLE TH (hcReal F h) (hcIdeal F) e →
      (∀ A ∈ TR, redTest θ P0 A ∈ TH ∧ redTest θ (fun x => P0 (θ x)) A ∈ TH) →
      AdvLE TR (encLaw F h θ P0) (encLaw F h θ (fun x => P0 (θ x))) (2 * e) := by
  have hE : encoder F h θ = encoderEquiv F h θ hθ := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold encLaw; rw [hE, KL_push_equiv, KL_prodLaw_left unif_isProb]
  · unfold encLaw; rw [hE, TV_push_equiv, TV_prodLaw_left unif_isProb]
  · intro TR TH e hhc hred A hA hAt
    have hQ0 : IsProb (fun x => P0 (θ x)) :=
      ⟨fun x => hP0.nonneg _, by
        rw [Fintype.sum_equiv (Function.Involutive.toPerm θ hθ) (fun x => P0 (θ x)) P0
          (fun x => rfl), hP0.sum_one]⟩
    have h1 := hhc _ (hred A hA).1 (redTest_isTest θ hP0 hAt)
    have h2 := hhc _ (hred A hA).2 (redTest_isTest θ hQ0 hAt)
    unfold adv at *
    rw [expect_hcReal_redTest] at h1 h2
    rw [expect_hcIdeal_redTest F hθ P0 A] at h1
    have := abs_sub_le (expect (encLaw F h θ P0) A)
      (expect (hcIdeal F) (redTest θ (fun x => P0 (θ x)) A))
      (expect (encLaw F h θ (fun x => P0 (θ x))) A)
    rw [abs_sub_comm (expect (hcIdeal F) _) _] at this
    linarith

/-! ### Asymptotic form -/

/-- **Decisional hard-core assumption** (Eq. (hardcore)) for a family of permutations
`F n` of finite seed spaces `D n` with predicates `h n`, against the observer classes
`TH n s` (randomised circuits of size `≤ s`): for every polynomial size bound `s(n)`, the
advantage `ε_hc(n, s(n))` is negligible. This is an unproved cryptographic assumption
(implied by nonuniformly secure one-way permutations via Goldreich–Levin). -/
def HardCoreAssumption (D : ℕ → Type*) [∀ n, Fintype (D n)] [∀ n, DecidableEq (D n)]
    (F : ∀ n, D n ≃ D n) (h : ∀ n, D n → Bool) (TH : ∀ n, ℕ → Set (D n × Bool → ℝ)) : Prop :=
  ∀ s : ℕ → ℕ, PolySize s → ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, AdvLE (TH n (s n)) (hcReal (F n) (h n)) (hcIdeal (F n)) (ε n)

/-- **Theorem `thm:universal`, asymptotic form**: under the hard-core assumption, and the
complexity-theoretic closure property that the reduction (efficient sampling of `P⁰`,
reversal, composition) costs at most a polynomial `c(n)` extra gates, every polynomial-size
observer has negligible advantage on the encoded records. -/
theorem universal_concealment_asymptotic (D : ℕ → Type*) [∀ n, Fintype (D n)]
    [∀ n, DecidableEq (D n)] [∀ n, Nonempty (D n)] (F : ∀ n, D n ≃ D n) (h : ∀ n, D n → Bool)
    (TH : ∀ n, ℕ → Set (D n × Bool → ℝ)) (hhc : HardCoreAssumption D F h TH)
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    (θ : ∀ n, X n → X n) (hθ : ∀ n, Function.Involutive (θ n))
    (P0 : ∀ n, X n → ℝ) (hP0 : ∀ n, IsProb (P0 n))
    (TR : ∀ n, ℕ → Set (D n × X n → ℝ)) (c : ℕ → ℕ) (hc : PolySize c)
    (hred : ∀ n s, ∀ A ∈ TR n s, redTest (θ n) (P0 n) A ∈ TH n (s + c n) ∧
      redTest (θ n) (fun x => P0 n (θ n x)) A ∈ TH n (s + c n))
    (s : ℕ → ℕ) (hs : PolySize s) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, AdvLE (TR n (s n))
      (encLaw (F n) (h n) (θ n) (P0 n)) (encLaw (F n) (h n) (θ n) (fun x => P0 n (θ n x)))
      (ε n) := by
  obtain ⟨ε, hε, hbound⟩ := hhc (fun n => s n + c n) (hs.add hc)
  refine ⟨fun n => 2 * ε n, hε.const_mul 2, fun n => ?_⟩
  exact ((universal_concealment (F n) (h n) (hθ n) (hP0 n)).2.2 (TR n (s n))
    (TH n (s n + c n)) (ε n) (hbound n) (fun A hA => hred n (s n) A hA))

/-! ### Information-theoretic remark: one hidden bit suffices -/

/-- Mutual information between a uniformly distributed orientation label and the record:
`I = ½ D(P‖M) + ½ D(Q‖M)` with `M = (P+Q)/2`. -/
noncomputable def labelInfo {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * KL P (fun x => (P x + Q x) / 2) + (1 / 2) * KL Q (fun x => (P x + Q x) / 2)

/-- The orientation hypothesis is a single binary variable: its mutual information with the
record is at most `log 2`, however large the relative entropy `D(P‖Q)` is. -/
theorem labelInfo_le_log_two {α : Type*} [Fintype α] {P Q : α → ℝ} (hP : IsProb P)
    (hQ : IsProb Q) : labelInfo P Q ≤ Real.log 2 := by
  have key : ∀ (R S : α → ℝ), IsProb R → IsProb S →
      KL R (fun x => (R x + S x) / 2) ≤ Real.log 2 := by
    intro R S hR hS
    calc KL R (fun x => (R x + S x) / 2) ≤ ∑ x, R x * Real.log 2 := by
          refine sum_le_sum fun x _ => ?_
          rcases (hR.nonneg x).eq_or_lt with h | h
          · rw [← h]; simp
          · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by
              have := hS.nonneg x; positivity) ?_) h.le
            rw [div_le_iff₀ (by have := hS.nonneg x; positivity)]
            nlinarith [hS.nonneg x]
      _ = Real.log 2 := by rw [← sum_mul, hR.sum_one, one_mul]
  have h1 := key P Q hP hQ
  have h2 := key Q P hQ hP
  have e : (fun x => (Q x + P x) / 2) = (fun x => (P x + Q x) / 2) := by
    funext x; ring
  rw [e] at h2
  unfold labelInfo
  linarith

/-! ### Efficient post-processing, Eq. (compdpi) -/

/-- **Eq. (compdpi)**: if a hypothesis-independent randomised post-processing channel `K`,
composed with any test of the class `T'`, yields a test of the class `T`
(circuit composition costs `c` gates), then `Adv_{T'}(K_*P, K_*Q) ≤ Adv_T(P,Q)`. -/
theorem advLE_chan {α β : Type*} [Fintype α] [Fintype β] {K : α → β → ℝ} (hK : IsChannel K)
    (P Q : α → ℝ) (T : Set (α → ℝ)) (T' : Set (β → ℝ)) {b : ℝ} (hb : AdvLE T P Q b)
    (hclos : ∀ A ∈ T', (fun x => ∑ y, K x y * A y) ∈ T) :
    AdvLE T' (chan K P) (chan K Q) b := by
  intro A hA hAt
  have ht : IsTest (fun x => ∑ y, K x y * A y) := by
    intro x
    constructor
    · exact sum_nonneg fun y _ => mul_nonneg (hK.nonneg x y) (hAt y).1
    · calc _ ≤ ∑ y, K x y * 1 := sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hAt y).2 (hK.nonneg x y)
        _ = 1 := by simp [hK.sum_one]
  unfold adv
  rw [expect_chan, expect_chan]
  exact hb _ (hclos A hA) ht

/-! ### Proposition `prop:clean`: no clean polynomial reversible encoder -/

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X] in
/-- **Proposition `prop:clean` (logical core).** Suppose a reversible map `R` on
seed × payload × work bits realises `(s, j, 0) ↦ (E(s,j), 0)` for every input, where the first
component of `E(s,j)` is `G(s)` for a permutation `G`. Then running `R` backwards on
`(y, z, 0)` for an *arbitrary* payload `z` returns the seed `G⁻¹(y)`. Since reversing a
reversible circuit preserves its size, a polynomial-size clean encoder would give a
polynomial-size inverse of `G`. -/
theorem clean_encoder_inverts {W : Type*} (G : D ≃ D) (E : D × X ≃ D × X)
    (hE : ∀ sx, (E sx).1 = G sx.1) (R : D × X × W ≃ D × X × W) (w0 : W)
    (hR : ∀ s j, R (s, j, w0) = ((E (s, j)).1, (E (s, j)).2, w0)) (y : D) (z : X) :
    (R.symm (y, z, w0)).1 = G.symm y := by
  set sx := E.symm (y, z)
  have h1 : R (sx.1, sx.2, w0) = (y, z, w0) := by
    rw [hR]; simp [sx]
  have h2 : R.symm (y, z, w0) = (sx.1, sx.2, w0) := by
    rw [← h1, Equiv.symm_apply_apply]
  rw [h2]
  have : G sx.1 = y := by rw [← hE]; simp [sx]
  rw [← this, Equiv.symm_apply_apply]

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X] in
/-- **Proposition `prop:clean`** for the one-bit encoder: the backwards circuit inverts `F`. -/
theorem clean_onebit_inverts {W : Type*} (F : D ≃ D) (h : D → Bool) {θ : X → X}
    (hθ : Function.Involutive θ) (R : D × X × W ≃ D × X × W) (w0 : W)
    (hR : ∀ s j, R (s, j, w0) = ((encoder F h θ (s, j)).1, (encoder F h θ (s, j)).2, w0))
    (y : D) (z : X) : (R.symm (y, z, w0)).1 = F.symm y :=
  clean_encoder_inverts F (encoderEquiv F h θ hθ) (fun _ => rfl) R w0 hR y z

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq X] in
/-- **Proposition `prop:clean`** for an encoder whose endpoint is `F^ℓ(s)` (the causal
encoder): the backwards circuit followed by `ℓ - 1` forward applications of `F` inverts `F`. -/
theorem clean_iterate_inverts {W : Type*} (F : D ≃ D) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (E : D × X ≃ D × X)
    (hE : ∀ sx, (E sx).1 = (F ^ ℓ) sx.1) (R : D × X × W ≃ D × X × W) (w0 : W)
    (hR : ∀ s j, R (s, j, w0) = ((E (s, j)).1, (E (s, j)).2, w0)) (y : D) (z : X) :
    (F ^ (ℓ - 1)) ((R.symm (y, z, w0)).1) = F.symm y := by
  rw [clean_encoder_inverts (F ^ ℓ) E hE R w0 hR y z]
  apply F.injective
  rw [Equiv.apply_symm_apply]
  change (F * F ^ (ℓ - 1)) ((F ^ ℓ).symm y) = y
  rw [← pow_succ', Nat.sub_add_cancel hℓ]
  exact Equiv.apply_symm_apply _ _

end Arrow

end UniversalPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Bernoulli
    ════════════════════════════════════════════════════════════════════ -/

section BernoulliPart

/-!
# Bernoulli direction strings (Section 5 and Appendix `app:binomial`)

Jump-direction strings of length `m` are functions `Fin m → Bool` (`true` = clockwise).
Under the forward fixed-count ring experiment the directions are i.i.d. `Ber(p)`
(`bernProd p m`); physical reversal is `θ_m(j₁,…,j_m) = (1-j_m,…,1-j₁)` (Eq. (jumpreversal)).

Main facts:
* `θ_m` is an involution and `(θ_m)_* Ber(p)^{⊗m} = Ber(1-p)^{⊗m}` (Eq. (bernoulli)).
* The count `K = |j|` is `Bin(m,p)` (Eq. (binpmf)); its moments and generating function
  (Eqs. (sigmamoments), (sigmamgf), (iftsecond)).
* `D(Ber(p)^{⊗m} ‖ Ber(1-p)^{⊗m}) = m d(p)` with `d(p) = (2p-1) log(p/(1-p))`.
* `TV = 1 - 2 e_m(p)` (Eqs. (ringtv), (bayes)).
* Chernoff/Hoeffding: `e_m(p) ≤ [2√(p(1-p))]^m ≤ e^{-2m(p-1/2)²}`
  (Eqs. (hoeffding), (chernoffsharp)).
-/


open Finset Real Filter

namespace Arrow

/-- Number of clockwise jumps `|j| = K`. -/
def ones {m : ℕ} (x : Fin m → Bool) : ℕ := ∑ i, (x i).toNat

/-- Raw path reversal of a jump-direction string, Eq. (jumpreversal):
`θ_m(j₁,…,j_m) = (1-j_m,…,1-j₁)`. -/
def jumpRev {m : ℕ} (x : Fin m → Bool) : Fin m → Bool := fun i => !(x (Fin.rev i))

lemma jumpRev_involutive (m : ℕ) : Function.Involutive (jumpRev (m := m)) := by
  intro x; funext i; simp [jumpRev]

/-- I.i.d. `Ber(p)` directions. -/
noncomputable def bernProd (p : ℝ) (m : ℕ) : (Fin m → Bool) → ℝ := iidLaw m (bern p)

lemma bernProd_isProb {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (m : ℕ) : IsProb (bernProd p m) :=
  piLaw_isProb fun _ => bern_isProb h0 h1

lemma bern_not (p : ℝ) (b : Bool) : bern p (!b) = bern (1 - p) b := by
  cases b <;> simp [bern]

/-- Reversal maps the forward direction law to the reverse direction law:
`P⁰ ∘ θ_m = Ber(1-p)^{⊗m}`, i.e. `Q⁰_m = Ber(1-p)^{⊗m}` (Eq. (bernoulli)). -/
theorem bernProd_jumpRev (p : ℝ) (m : ℕ) (x : Fin m → Bool) :
    bernProd p m (jumpRev x) = bernProd (1 - p) m x := by
  unfold bernProd iidLaw piLaw jumpRev
  simp_rw [bern_not]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)

lemma ones_jumpRev {m : ℕ} (x : Fin m → Bool) : ones (jumpRev x) + ones x = m := by
  unfold ones jumpRev
  rw [show ∑ i, (x i).toNat = ∑ i, (x (Fin.rev i)).toNat from
    (Fintype.sum_equiv Fin.revPerm _ _ (fun i => by simp)), ← sum_add_distrib]
  have : ∀ b : Bool, (!b).toNat + b.toNat = 1 := by decide
  simp [this]

lemma bernProd_eq (p : ℝ) {m : ℕ} (x : Fin m → Bool) :
    bernProd p m x = p ^ ones x * (1 - p) ^ (m - ones x) := by
  induction m with
  | zero => simp [bernProd, iidLaw, piLaw, ones]
  | succ m ih =>
    have h1 : bernProd p (m + 1) x = bern p (x 0) * bernProd p m (Fin.tail x) := by
      simp [bernProd, iidLaw, piLaw, Fin.prod_univ_succ, Fin.tail]
    have h2 : ones x = (x 0).toNat + ones (Fin.tail x) := by
      simp [ones, Fin.sum_univ_succ, Fin.tail]
    have hle : ones (Fin.tail x) ≤ m := by
      unfold ones
      calc ∑ i, (Fin.tail x i).toNat ≤ ∑ _i : Fin m, 1 :=
            sum_le_sum fun i _ => Bool.toNat_le _
        _ = m := by simp
    rw [h1, h2, ih]
    cases x 0
    · simp only [bern, Bool.false_eq_true, if_false, Bool.toNat_false, zero_add]
      rw [show m + 1 - ones (Fin.tail x) = (m - ones (Fin.tail x)) + 1 by omega, pow_succ]
      ring
    · simp only [bern, if_true, Bool.toNat_true]
      rw [show m + 1 - (1 + ones (Fin.tail x)) = m - ones (Fin.tail x) by omega, pow_add]
      ring

/-! ### Expectations of functions of the count -/

/-- `E_{K ∼ Bin(m,p)} f(K)`, computed on direction strings. -/
noncomputable def binExp (p : ℝ) (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ x : Fin m → Bool, bernProd p m x * f (ones x)

lemma binExp_zero (p : ℝ) (f : ℕ → ℝ) : binExp p 0 f = f 0 := by
  simp [binExp, bernProd, iidLaw, piLaw, ones]

lemma binExp_succ (p : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binExp p (m + 1) f = p * binExp p m (fun k => f (k + 1)) + (1 - p) * binExp p m f := by
  unfold binExp
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk]
  have hP : ∀ (b : Bool) (y : Fin m → Bool),
      bernProd p (m + 1) (Fin.cons b y) = bern p b * bernProd p m y := by
    intro b y; simp [bernProd, iidLaw, piLaw, Fin.prod_univ_succ]
  have hK : ∀ (b : Bool) (y : Fin m → Bool), ones (Fin.cons b y : Fin (m + 1) → Bool) =
      b.toNat + ones y := by
    intro b y; simp [ones, Fin.sum_univ_succ]
  simp only [hP, hK, bern, if_true, Bool.false_eq_true, if_false, Bool.toNat_true,
    Bool.toNat_false, zero_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun y _ => ?_; rw [add_comm 1]; ring
  · refine sum_congr rfl fun y _ => ?_; ring

lemma binExp_add (p : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    binExp p m (fun k => f k + g k) = binExp p m f + binExp p m g := by
  simp [binExp, mul_add, sum_add_distrib]

lemma binExp_const_mul (p : ℝ) (m : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binExp p m (fun k => c * f k) = c * binExp p m f := by
  unfold binExp; rw [mul_sum]; exact sum_congr rfl fun x _ => by ring

lemma binExp_one (p : ℝ) (m : ℕ) : binExp p m (fun _ => 1) = 1 := by
  induction m with
  | zero => simp [binExp_zero]
  | succ m ih => rw [binExp_succ, ih]; ring

lemma binExp_mono {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (m : ℕ) {f g : ℕ → ℝ}
    (h : ∀ k, f k ≤ g k) : binExp p m f ≤ binExp p m g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h _) ((bernProd_isProb h0 h1 m).nonneg x)

/-- The binomial probability mass function. -/
noncomputable def binPmf (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)

/-- The count is binomially distributed: `P(K = k) = C(m,k) p^k (1-p)^{m-k}` (Eq. (binpmf)). -/
theorem binExp_indicator (p : ℝ) (m k : ℕ) :
    binExp p m (fun j => if j = k then 1 else 0) = binPmf m p k := by
  induction m generalizing k with
  | zero =>
    rw [binExp_zero]; unfold binPmf
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · simp [Nat.choose_eq_zero_of_lt h, h.ne]
  | succ m ih =>
    rw [binExp_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have : binExp p m (fun j => if j + 1 = 0 then (1 : ℝ) else 0) = 0 := by
        simp [binExp]
      rw [this, ih]; simp [binPmf, pow_succ]; ring
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have e : (fun j => if j + 1 = k' + 1 then (1 : ℝ) else 0) = fun j => if j = k' then 1 else 0 :=
        by funext j; simp
      rw [e, ih, ih]
      unfold binPmf
      rw [Nat.choose_succ_succ', Nat.cast_add]
      rcases Nat.lt_or_ge m k' with hlt | hge
      · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega)]; simp
      · rcases hge.eq_or_lt with heq | hlt
        · subst heq; simp; ring
        · rw [show m + 1 - (k' + 1) = m - k' by omega, show m - k' = (m - (k' + 1)) + 1 by omega,
            pow_succ]
          ring

/-- Reversal symmetry of the binomial law, `b_{1-p}(k) = b_p(m-k)` (Eq. (binpmf)). -/
theorem binPmf_symm (m : ℕ) (p : ℝ) {k : ℕ} (hk : k ≤ m) :
    binPmf m (1 - p) k = binPmf m p (m - k) := by
  unfold binPmf
  rw [Nat.choose_symm hk, show m - (m - k) = k by omega, sub_sub_cancel]
  ring

/-- Generating function of the count: `E z^K = (1 - p + p z)^m`. -/
theorem binExp_pow (p z : ℝ) (m : ℕ) : binExp p m (fun k => z ^ k) = (1 - p + p * z) ^ m := by
  induction m with
  | zero => simp [binExp_zero]
  | succ m ih =>
    rw [binExp_succ, show (fun k : ℕ => z ^ (k + 1)) = fun k : ℕ => z * z ^ k by funext k; ring,
      binExp_const_mul, ih, pow_succ]; ring

lemma binExp_id (p : ℝ) (m : ℕ) : binExp p m (fun k => (k : ℝ)) = m * p := by
  induction m with
  | zero => simp [binExp_zero]
  | succ m ih =>
    rw [binExp_succ, show (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) = fun k : ℕ => (k : ℝ) + 1 by
      funext k; push_cast; ring, binExp_add, binExp_one, ih]; push_cast; ring

lemma binExp_sq (p : ℝ) (m : ℕ) :
    binExp p m (fun k => (k : ℝ) ^ 2) = m * p * (1 - p) + (m * p) ^ 2 := by
  induction m with
  | zero => simp [binExp_zero]
  | succ m ih =>
    rw [binExp_succ, show (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 2) =
      fun k : ℕ => (k : ℝ) ^ 2 + (2 * (k : ℝ) + 1) by funext k; push_cast; ring, binExp_add,
      show (fun k : ℕ => 2 * (k : ℝ) + 1) = fun k : ℕ => 2 * (k : ℝ) + 1 * 1 by funext k; ring,
      binExp_add, binExp_const_mul, binExp_const_mul, binExp_one, binExp_id, ih]
    push_cast; ring

/-! ### Entropy production of the direction string -/

/-- Dimensionless affinity per jump `a = log(p/(1-p))`. -/
noncomputable def affinity (p : ℝ) : ℝ := Real.log (p / (1 - p))

/-- Divergence rate per jump `d(p) = (2p-1) log(p/(1-p))` (Eq. (drate)). -/
noncomputable def drate (p : ℝ) : ℝ := (2 * p - 1) * Real.log (p / (1 - p))

/-- The raw log-likelihood ratio (entropy production) of a direction string is
`σ = a (2K - m)` (Eq. (ringsigma) with `N = m`). -/
theorem llr_bernProd {p : ℝ} (h0 : 0 < p) (h1 : p < 1) {m : ℕ} (x : Fin m → Bool) :
    llr (bernProd p m) (bernProd (1 - p) m) x = affinity p * (2 * (ones x : ℝ) - m) := by
  have hle : ones x ≤ m := by
    have := ones_jumpRev x; omega
  unfold llr affinity
  rw [bernProd_eq, bernProd_eq, sub_sub_cancel]
  have hq : 0 < 1 - p := by linarith
  rw [show p ^ ones x * (1 - p) ^ (m - ones x) / ((1 - p) ^ ones x * p ^ (m - ones x)) =
      (p / (1 - p)) ^ ones x / (p / (1 - p)) ^ (m - ones x) by
    rw [div_pow, div_pow]; field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Nat.cast_sub hle]
  ring

/-- Mean entropy production `E σ = m a (2p-1) = m d(p)` (Eq. (sigmamoments)). -/
theorem mean_sigma (p : ℝ) (m : ℕ) :
    binExp p m (fun k => affinity p * (2 * (k : ℝ) - m)) = m * drate p := by
  rw [show (fun k : ℕ => affinity p * (2 * (k : ℝ) - m)) =
    fun k : ℕ => (2 * affinity p) * (k : ℝ) + (-(affinity p * m)) * 1 by funext k; ring,
    binExp_add, binExp_const_mul, binExp_const_mul, binExp_id, binExp_one]
  unfold drate affinity; ring

/-- Variance of the entropy production `Var σ = 4 m a² p (1-p)` (Eq. (sigmamoments)). -/
theorem var_sigma (p : ℝ) (m : ℕ) :
    binExp p m (fun k => (affinity p * (2 * (k : ℝ) - m) - m * drate p) ^ 2) =
      4 * m * affinity p ^ 2 * p * (1 - p) := by
  have e : (fun k : ℕ => (affinity p * (2 * (k : ℝ) - m) - m * drate p) ^ 2) =
      fun k : ℕ => (4 * affinity p ^ 2) * (k : ℝ) ^ 2 +
        ((-(8 * affinity p ^ 2 * m * p)) * (k : ℝ) + (affinity p ^ 2 * m ^ 2 * (2 * p) ^ 2) * 1)
      := by
    funext k; unfold drate affinity; ring
  rw [e, binExp_add, binExp_add, binExp_const_mul, binExp_const_mul, binExp_const_mul,
    binExp_sq, binExp_id, binExp_one]
  ring

/-- Moment-generating function `E e^{tσ} = [(1-p)e^{-ta} + p e^{ta}]^m` (Eq. (sigmamgf)). -/
theorem mgf_sigma (p t : ℝ) (m : ℕ) :
    binExp p m (fun k => Real.exp (t * (affinity p * (2 * (k : ℝ) - m)))) =
      ((1 - p) * Real.exp (-t * affinity p) + p * Real.exp (t * affinity p)) ^ m := by
  have e : (fun k : ℕ => Real.exp (t * (affinity p * (2 * (k : ℝ) - m)))) =
      fun k : ℕ => Real.exp (-t * affinity p) ^ m * (Real.exp (2 * t * affinity p)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [e, binExp_const_mul, binExp_pow, ← mul_pow]
  congr 1
  rw [show Real.exp (t * affinity p) = Real.exp (-t * affinity p) * Real.exp (2 * t * affinity p)
    by rw [← Real.exp_add]; ring_nf]
  ring

/-- At `t = -1` the bracket equals one: the integral fluctuation identity `E e^{-σ} = 1`
derived from the generating function (Appendix `app:binomial`). -/
theorem ift_from_mgf {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (m : ℕ) :
    binExp p m (fun k => Real.exp (-1 * (affinity p * (2 * (k : ℝ) - m)))) = 1 := by
  rw [mgf_sigma]
  have hq : 0 < 1 - p := by linarith
  have e1 : Real.exp (-(-1) * affinity p) = p / (1 - p) := by
    simp [affinity, Real.exp_log (div_pos h0 hq)]
  have e2 : Real.exp (-1 * affinity p) = (1 - p) / p := by
    rw [show -1 * affinity p = -affinity p by ring, Real.exp_neg]
    simp [affinity, Real.exp_log (div_pos h0 hq)]
  rw [e1, e2]
  field_simp
  simp

/-- Second moment of the naive fluctuation estimator `E e^{-2σ} = [(1-p)e^{2a} + p e^{-2a}]^m`
(Eq. (iftsecond)). -/
theorem ift_second_moment (p : ℝ) (m : ℕ) :
    binExp p m (fun k => Real.exp (-2 * (affinity p * (2 * (k : ℝ) - m)))) =
      ((1 - p) * Real.exp (2 * affinity p) + p * Real.exp (-2 * affinity p)) ^ m := by
  rw [mgf_sigma]; congr 2; ring_nf

/-- For nonzero affinity the bracket in Eq. (iftsecond) exceeds one, so the second moment
grows exponentially in `m`. -/
theorem ift_second_bracket_gt_one {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hp : p ≠ 1 / 2) :
    1 < (1 - p) * Real.exp (2 * affinity p) + p * Real.exp (-2 * affinity p) := by
  have hq : 0 < 1 - p := by linarith
  have e1 : Real.exp (2 * affinity p) = (p / (1 - p)) ^ 2 := by
    rw [show 2 * affinity p = Real.log ((p / (1 - p)) ^ 2) by
      rw [Real.log_pow]; unfold affinity; push_cast; ring, Real.exp_log (by positivity)]
  have e2 : Real.exp (-2 * affinity p) = ((1 - p) / p) ^ 2 := by
    rw [show -2 * affinity p = Real.log (((1 - p) / p) ^ 2) by
      rw [Real.log_pow, show (1 - p) / p = (p / (1 - p))⁻¹ by rw [inv_div], Real.log_inv]
      unfold affinity; push_cast; ring, Real.exp_log (by positivity)]
  rw [e1, e2]
  have key : (1 - p) * (p / (1 - p)) ^ 2 + p * ((1 - p) / p) ^ 2 =
      (p ^ 3 + (1 - p) ^ 3) / (p * (1 - p)) := by field_simp
  rw [key, lt_div_iff₀ (by positivity)]
  have : (2 * p - 1) ^ 2 > 0 := by
    have : 2 * p - 1 ≠ 0 := fun h => hp (by linarith)
    positivity
  nlinarith

/-! ### Relative entropy and total variation of the direction laws -/

lemma dbin_flip (p : ℝ) : dbin p (1 - p) = drate p := by
  unfold dbin drate
  rw [sub_sub_cancel, show (1 - p) / p = (p / (1 - p))⁻¹ by rw [inv_div], Real.log_inv]
  ring

/-- `D(Ber(p)^{⊗m} ‖ Ber(1-p)^{⊗m}) = m d(p)`. -/
theorem KL_bernProd {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (m : ℕ) :
    KL (bernProd p m) (bernProd (1 - p) m) = m * drate p := by
  unfold bernProd
  rw [KL_iidLaw (bern_isProb h0.le h1.le) (bern_isProb (by linarith) (by linarith)), KL_bern,
    dbin_flip]
  intro b hb
  cases b <;> simp [bern] at hb ⊢ <;> linarith

/-- Optimal equal-prior orientation error `e_m(p) = P(K < m/2) + ½ P(K = m/2)`
(Eq. (bayes)). -/
noncomputable def bayesErrBin (m : ℕ) (p : ℝ) : ℝ :=
  binExp p m (fun k => if 2 * k < m then 1 else if 2 * k = m then 1 / 2 else 0)

/-- `e_m(p)` written with the binomial mass function, exactly as in Eq. (bayes). -/
theorem bayesErrBin_eq_sum (m : ℕ) (p : ℝ) :
    bayesErrBin m p = ∑ k ∈ range (m + 1),
      (if 2 * k < m then 1 else if 2 * k = m then 1 / 2 else 0) * binPmf m p k := by
  have hf : ∀ (f : ℕ → ℝ), binExp p m f =
      ∑ k ∈ range (m + 1), f k * binExp p m (fun j => if j = k then 1 else 0) := by
    intro f
    unfold binExp
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    have hx : ones x ∈ range (m + 1) := by
      have := ones_jumpRev x; rw [mem_range]; omega
    rw [sum_eq_single (ones x)]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hx h
  unfold bayesErrBin
  rw [hf]
  simp_rw [binExp_indicator]

/-- Sign structure of the likelihood ratio: for `p ≥ 1/2` the forward weight dominates
exactly when `2K > m`. -/
lemma bern_sign {p : ℝ} (hp : 1 / 2 ≤ p) (h1 : p ≤ 1) {m k : ℕ} (hk : k ≤ m) :
    (m < 2 * k → (1 - p) ^ k * p ^ (m - k) ≤ p ^ k * (1 - p) ^ (m - k)) ∧
    (2 * k < m → p ^ k * (1 - p) ^ (m - k) ≤ (1 - p) ^ k * p ^ (m - k)) ∧
    (2 * k = m → p ^ k * (1 - p) ^ (m - k) = (1 - p) ^ k * p ^ (m - k)) := by
  have hq : 1 - p ≤ p := by linarith
  have hq0 : 0 ≤ 1 - p := by linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, hr⟩ : ∃ r, k = (m - k) + r := ⟨k - (m - k), by omega⟩
    set j := m - k
    rw [hr, pow_add, pow_add]
    have := pow_le_pow_left₀ hq0 hq r
    have h2 : 0 ≤ (1 - p) ^ (m - k) * p ^ (m - k) := by positivity
    nlinarith
  · obtain ⟨r, hr⟩ : ∃ r, m - k = k + r := ⟨m - k - k, by omega⟩
    set j := m - k
    rw [hr, pow_add, pow_add]
    have := pow_le_pow_left₀ hq0 hq r
    have h2 : 0 ≤ p ^ k * (1 - p) ^ k := by positivity
    nlinarith
  · rw [show m - k = k by omega]; ring

/-- **Eqs. (ringtv), (bayes)**: `TV(Ber(p)^{⊗m}, Ber(1-p)^{⊗m}) = 1 - 2 e_m(p)` for `p ≥ 1/2`. -/
theorem TV_bernProd {p : ℝ} (hp : 1 / 2 ≤ p) (h1 : p ≤ 1) (m : ℕ) :
    TV (bernProd p m) (bernProd (1 - p) m) = 1 - 2 * bayesErrBin m p := by
  set sg : ℕ → ℝ := fun k => if m < 2 * k then 1 else if 2 * k < m then -1 else 0
  have habs : ∀ x : Fin m → Bool, |bernProd p m x - bernProd (1 - p) m x| =
      (bernProd p m x - bernProd (1 - p) m x) * sg (ones x) := by
    intro x
    have hle : ones x ≤ m := by have := ones_jumpRev x; omega
    obtain ⟨s1, s2, s3⟩ := bern_sign hp h1 hle
    rw [bernProd_eq, bernProd_eq, sub_sub_cancel]
    simp only [sg]
    split_ifs with ha hb
    · rw [abs_of_nonneg (by linarith [s1 ha]), mul_one]
    · rw [abs_of_nonpos (by linarith [s2 hb]), mul_neg_one, neg_sub]
    · rw [s3 (by omega), sub_self, abs_zero, zero_mul]
  have hsg : ∀ x : Fin m → Bool, sg (ones (jumpRev x)) = - sg (ones x) := by
    intro x
    have := ones_jumpRev x
    simp only [sg]
    split_ifs <;> first | (exfalso; omega) | rfl | norm_num
  have hrev : ∑ x, bernProd (1 - p) m x * sg (ones x) = -∑ x, bernProd p m x * sg (ones x) := by
    calc ∑ x, bernProd (1 - p) m x * sg (ones x)
        = ∑ x, bernProd p m (jumpRev x) * sg (ones x) := by simp_rw [bernProd_jumpRev]
      _ = ∑ y, bernProd p m y * sg (ones (jumpRev y)) :=
          Fintype.sum_equiv (Function.Involutive.toPerm _ (jumpRev_involutive m)) _ _
            (fun x => by simp [jumpRev_involutive m x])
      _ = -∑ x, bernProd p m x * sg (ones x) := by
          rw [← sum_neg_distrib]; refine sum_congr rfl fun x _ => ?_; rw [hsg]; ring
  have hTV : TV (bernProd p m) (bernProd (1 - p) m) = binExp p m sg := by
    unfold TV binExp
    simp_rw [habs, sub_mul, sum_sub_distrib, hrev]
    ring
  rw [hTV]
  have e : sg = fun k => 1 + (-2) * (if 2 * k < m then 1 else if 2 * k = m then 1 / 2 else 0) := by
    funext k
    simp only [sg]
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [e, binExp_add, binExp_one, binExp_const_mul]
  unfold bayesErrBin
  ring

/-! ### Concentration: Chernoff, Hoeffding and Chebyshev bounds -/

/-- Probability that the count is at most `m/2`. -/
noncomputable def lowerTail (m : ℕ) (p : ℝ) : ℝ :=
  binExp p m (fun k => if 2 * k ≤ m then 1 else 0)

lemma bayesErrBin_le_lowerTail {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (m : ℕ) :
    bayesErrBin m p ≤ lowerTail m p := by
  refine binExp_mono h0 h1 m fun k => ?_
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma bayesErrBin_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (m : ℕ) : 0 ≤ bayesErrBin m p := by
  unfold bayesErrBin binExp
  exact sum_nonneg fun x _ => mul_nonneg ((bernProd_isProb h0 h1 m).nonneg x)
    (by dsimp only; split_ifs <;> norm_num)

/-- **Chernoff bound** (Eqs. (chernoffraw), (chernoffsharp)):
`P(K ≤ m/2) ≤ [2√(p(1-p))]^m` for `1/2 ≤ p < 1`. -/
theorem lowerTail_le_chernoff {p : ℝ} (hp : 1 / 2 ≤ p) (h1 : p < 1) (m : ℕ) :
    lowerTail m p ≤ (2 * Real.sqrt (p * (1 - p))) ^ m := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < 1 - p := by linarith
  set v := Real.sqrt (1 - p)
  set w := Real.sqrt p
  have hv : 0 < v := Real.sqrt_pos.mpr hq0
  have hw : 0 < w := Real.sqrt_pos.mpr hp0
  have hv2 : v ^ 2 = 1 - p := Real.sq_sqrt hq0.le
  have hw2 : w ^ 2 = p := Real.sq_sqrt hp0.le
  set u := v / w
  have hu : 0 < u := div_pos hv hw
  have hu1 : u ≤ 1 := by
    rw [div_le_one hw]
    exact Real.sqrt_le_sqrt (by linarith)
  have hu2 : u ^ 2 = (1 - p) / p := by rw [div_pow, hv2, hw2]
  have hpt : ∀ k : ℕ, (if 2 * k ≤ m then (1 : ℝ) else 0) ≤ (1 / u ^ m) * (u ^ 2) ^ k := by
    intro k
    split_ifs with hk
    · rw [← pow_mul, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_of_le_one hu.le hu1 hk
    · positivity
  calc lowerTail m p ≤ binExp p m (fun k => (1 / u ^ m) * (u ^ 2) ^ k) :=
        binExp_mono hp0.le h1.le m hpt
    _ = (1 / u ^ m) * (1 - p + p * u ^ 2) ^ m := by rw [binExp_const_mul, binExp_pow]
    _ = (2 * (w * v)) ^ m := by
        rw [hu2, show 1 - p + p * ((1 - p) / p) = 2 * (1 - p) by field_simp; ring,
          ← hv2, show u = v / w from rfl, div_pow, one_div_div, ← div_pow, ← mul_pow]
        congr 1
        field_simp
    _ = (2 * Real.sqrt (p * (1 - p))) ^ m := by
        rw [Real.sqrt_mul hp0.le]

lemma two_sqrt_le_exp {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 * Real.sqrt (p * (1 - p)) ≤ Real.exp (-2 * (p - 1 / 2) ^ 2) := by
  have hA : 0 ≤ 2 * Real.sqrt (p * (1 - p)) := by positivity
  have hB : 0 ≤ Real.exp (-2 * (p - 1 / 2) ^ 2) := (Real.exp_pos _).le
  refine (pow_le_pow_iff_left₀ hA hB (two_ne_zero)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by nlinarith), ← Real.exp_nat_mul]
  have := Real.add_one_le_exp (-4 * (p - 1 / 2) ^ 2)
  push_cast
  rw [show (2 : ℝ) * (-2 * (p - 1 / 2) ^ 2) = -4 * (p - 1 / 2) ^ 2 by ring]
  nlinarith

/-- **Eq. (hoeffding)**: `e_m(p) ≤ e^{-2m(p-1/2)²}` for `1/2 ≤ p < 1`. -/
theorem bayesErrBin_le_hoeffding {p : ℝ} (hp : 1 / 2 ≤ p) (h1 : p < 1) (m : ℕ) :
    bayesErrBin m p ≤ Real.exp (-2 * m * (p - 1 / 2) ^ 2) := by
  calc bayesErrBin m p ≤ lowerTail m p := bayesErrBin_le_lowerTail (by linarith) h1.le m
    _ ≤ (2 * Real.sqrt (p * (1 - p))) ^ m := lowerTail_le_chernoff hp h1 m
    _ ≤ Real.exp (-2 * (p - 1 / 2) ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) (two_sqrt_le_exp (by linarith) h1.le) m
    _ = Real.exp (-2 * m * (p - 1 / 2) ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The sharp Chernoff exponent `I(p) = -½ log(4p(1-p))` (Eq. (chernoffsharp)). -/
noncomputable def chernoffExp (p : ℝ) : ℝ := -(1 / 2) * Real.log (4 * p * (1 - p))

/-- `[2√(p(1-p))]^m = e^{-m I(p)}` (Eq. (chernoffsharp)). -/
theorem chernoff_eq_exp {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (m : ℕ) :
    (2 * Real.sqrt (p * (1 - p))) ^ m = Real.exp (-(m * chernoffExp p)) := by
  have hq : 0 < 1 - p := by linarith
  have : 2 * Real.sqrt (p * (1 - p)) = Real.exp (-chernoffExp p) := by
    unfold chernoffExp
    have hpos : 0 < 4 * p * (1 - p) := by positivity
    have h4 : Real.sqrt (4 * p * (1 - p)) = Real.exp (Real.log (4 * p * (1 - p)) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    have h2 : 2 * Real.sqrt (p * (1 - p)) = Real.sqrt (4 * p * (1 - p)) := by
      rw [show 4 * p * (1 - p) = 2 ^ 2 * (p * (1 - p)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2) (p * (1 - p)),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h2, h4]; ring_nf
  rw [this, ← Real.exp_nat_mul]; ring_nf

/-- The sharp exponent dominates the Hoeffding exponent: `I(p) ≥ 2(p-1/2)²`, positive for
`p ≠ 1/2` (Eq. (chernoffsharp)). -/
theorem chernoffExp_ge {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    2 * (p - 1 / 2) ^ 2 ≤ chernoffExp p := by
  unfold chernoffExp
  have hq : 0 < 1 - p := by linarith
  have hpos : 0 < 4 * p * (1 - p) := by positivity
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith

/-- **Chebyshev bound** for the lower tail of the count: for `t > 0`,
`P(K ≤ m(p - t)) ≤ p(1-p)/(m t²)`. -/
theorem lowerTail_chebyshev {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht : 0 < t) :
    binExp p m (fun k => if (k : ℝ) ≤ m * (p - t) then 1 else 0) ≤ p * (1 - p) / (m * t ^ 2) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpt : ∀ k : ℕ, (if (k : ℝ) ≤ m * (p - t) then (1 : ℝ) else 0) ≤
      (1 / (m * t) ^ 2) * ((k : ℝ) ^ 2 + ((-(2 * m * p)) * (k : ℝ) + (m * p) ^ 2 * 1)) := by
    intro k
    have hsq : (k : ℝ) ^ 2 + ((-(2 * m * p)) * (k : ℝ) + (m * p) ^ 2 * 1) = ((k : ℝ) - m * p) ^ 2 :=
      by ring
    rw [hsq]
    split_ifs with hk
    · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
      have : m * t ≤ m * p - k := by nlinarith
      have h2 : 0 ≤ m * t := by positivity
      nlinarith
    · positivity
  calc _ ≤ binExp p m (fun k => (1 / (m * t) ^ 2) *
        ((k : ℝ) ^ 2 + ((-(2 * m * p)) * (k : ℝ) + (m * p) ^ 2 * 1))) := binExp_mono h0 h1 m hpt
    _ = (1 / (m * t) ^ 2) * (m * p * (1 - p)) := by
        rw [binExp_const_mul, binExp_add, binExp_add, binExp_const_mul, binExp_const_mul,
          binExp_sq, binExp_id, binExp_one]
        ring
    _ = p * (1 - p) / (m * t ^ 2) := by field_simp

end Arrow

end BernoulliPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Ring
    ════════════════════════════════════════════════════════════════════ -/

section RingPart

/-!
# Section 5: a bounded-rate thermodynamic core (the driven three-state ring)

**Physical input (treated as established physics, not re-derived).** The stationary
continuous-time Markov jump process on `ℤ₃` with clockwise/counter-clockwise rates
`k₊ = κ e^{a/2}`, `k₋ = κ e^{-a/2}` has the path density (Eq. (ringdensity))
`P(ω) = ⅓ e^{-λT} k₊^K k₋^{N-K}` with respect to ordered jump times; conditionally on `N(T) = m`
the jump directions are i.i.d. `Ber(p)` with `p = k₊/(k₊+k₋)`, independent of the initial site
and of the jump times, whose conditional laws are the same under the two hypotheses; the jump
count is Poisson. Thermodynamic consistency identifies the log path-probability ratio with the
entropy production (Eq. (thermoid)). We take these as the modelling assumptions and formalise
everything that follows from them.

Formalised here:
* rates, uniform stationarity, local detailed balance and cycle affinity;
* the entropy production `σ = a(2K - N)` from the path densities (Eq. (ringsigma));
* `p = e^a/(1+e^a)` and `d(p) = (2p-1)log(p/(1-p)) = a tanh(a/2) > 0` (Eqs. (bernoulli), (drate));
* sufficiency of the direction string (no KL loss when discarding a variable with a common
  conditional law);
* **Theorem `thm:ring`** (Eqs. (ringkl)–(ringcomp)) in finite and asymptotic form;
* encoded likelihoods and fluctuation relations (Eqs. (encodedprob)–(encodeddft));
* the absolute current has the same law under both hypotheses;
* the fixed-count acceptance probability `e^{-m} m^m/m! ∼ 1/√(2πm)` (Eq. (acceptance)).
-/


open Finset Real Filter Asymptotics

namespace Arrow

/-! ### Rates, stationarity and local detailed balance -/

/-- Clockwise rate `k₊ = κ e^{a/2}`. -/
noncomputable def kPlus (κ a : ℝ) : ℝ := κ * Real.exp (a / 2)

/-- Counter-clockwise rate `k₋ = κ e^{-a/2}`. -/
noncomputable def kMinus (κ a : ℝ) : ℝ := κ * Real.exp (-(a / 2))

/-- Escape rate `λ = k₊ + k₋`. -/
noncomputable def escapeRate (κ a : ℝ) : ℝ := kPlus κ a + kMinus κ a

/-- Transition rates of the ring on `ℤ₃` (`Fin 3`). -/
noncomputable def ringRate (κ a : ℝ) (r s : Fin 3) : ℝ :=
  if s = r + 1 then kPlus κ a else if s = r - 1 then kMinus κ a else 0

/-- The uniform distribution is stationary: the probability flux into every site equals the
flux out of it. -/
theorem ring_uniform_stationary (κ a : ℝ) (s : Fin 3) :
    ∑ r, (1 / 3 : ℝ) * ringRate κ a r s = (1 / 3) * escapeRate κ a := by
  fin_cases s <;> simp (config := { decide := true }) [ringRate, Fin.sum_univ_three, escapeRate] <;>
    ring

/-- Local detailed balance: a clockwise jump carries the dimensionless entropy flow `a`. -/
theorem ring_ldb (κ a : ℝ) (hκ : 0 < κ) : Real.log (kPlus κ a / kMinus κ a) = a := by
  unfold kPlus kMinus
  rw [mul_div_mul_left _ _ hκ.ne', ← Real.exp_sub, Real.log_exp]; ring

/-- The cycle affinity of the driven ring is `3a`. -/
theorem ring_cycle_affinity (κ a : ℝ) (hκ : 0 < κ) :
    Real.log ((kPlus κ a / kMinus κ a) ^ 3) = 3 * a := by
  rw [Real.log_pow, ring_ldb κ a hκ]; norm_num

/-- The jump bias `p = k₊/(k₊+k₋) = e^a/(1+e^a)` (Eq. (bernoulli)). -/
theorem jump_bias (κ a : ℝ) (hκ : 0 < κ) :
    kPlus κ a / (kPlus κ a + kMinus κ a) = Real.exp a / (1 + Real.exp a) := by
  unfold kPlus kMinus
  have h1 : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(a / 2)) * Real.exp (a / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have := Real.exp_pos (a / 2)
  have := Real.exp_pos (-(a / 2))
  field_simp
  nlinarith [h1, h2]

/-- The bias exceeds `1/2` iff the affinity is positive. -/
theorem bias_gt_half {a : ℝ} (ha : 0 < a) : 1 / 2 < Real.exp a / (1 + Real.exp a) := by
  have := Real.one_lt_exp_iff.mpr ha
  rw [lt_div_iff₀ (by positivity)]; linarith

/-- The affinity per jump recovered from the bias is `a`. -/
theorem affinity_of_bias (a : ℝ) : affinity (Real.exp a / (1 + Real.exp a)) = a := by
  unfold affinity
  have h := Real.exp_pos a
  rw [show Real.exp a / (1 + Real.exp a) / (1 - Real.exp a / (1 + Real.exp a)) = Real.exp a by
    field_simp; ring, Real.log_exp]

/-- **Eq. (drate)**: `d(p) = (2p-1) log(p/(1-p)) = a tanh(a/2)` for `p = e^a/(1+e^a)`. -/
theorem drate_eq_tanh (a : ℝ) : drate (Real.exp a / (1 + Real.exp a)) = a * Real.tanh (a / 2) := by
  unfold drate
  have h := affinity_of_bias a
  unfold affinity at h
  rw [h, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have e1 : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, Real.exp_neg]
  have := Real.exp_pos (a / 2)
  field_simp
  ring

/-- `d(p) > 0` for `p ≠ 1/2` in `(0,1)`. -/
theorem drate_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (hp : p ≠ 1 / 2) : 0 < drate p := by
  unfold drate
  have hq : 0 < 1 - p := by linarith
  rcases lt_or_gt_of_ne hp with h | h
  · have : Real.log (p / (1 - p)) < 0 :=
      Real.log_neg (div_pos h0 hq) (by rw [div_lt_one hq]; linarith)
    nlinarith
  · have : 0 < Real.log (p / (1 - p)) :=
      Real.log_pos (by rw [one_lt_div hq]; linarith)
    nlinarith

/-! ### Path densities and the entropy production -/

/-- Forward path density of a path with `N` jumps, `K` of them clockwise (Eq. (ringdensity)).
This formula is the physical input. -/
noncomputable def ringDensity (κ a T : ℝ) (N K : ℕ) : ℝ :=
  (1 / 3) * Real.exp (-(escapeRate κ a * T)) * kPlus κ a ^ K * kMinus κ a ^ (N - K)

/-- **Eq. (ringsigma)**: the reversed path exchanges `K` and `N - K`, the stationary boundary
terms cancel, and the entropy production is `σ = a(2K - N)`. -/
theorem ring_sigma (κ a T : ℝ) (hκ : 0 < κ) {N K : ℕ} (hK : K ≤ N) :
    Real.log (ringDensity κ a T N K / ringDensity κ a T N (N - K)) = a * (2 * K - N) := by
  unfold ringDensity
  rw [Nat.sub_sub_self hK]
  have hp : 0 < kPlus κ a := by unfold kPlus; positivity
  have hm : 0 < kMinus κ a := by unfold kMinus; positivity
  rw [show 1 / 3 * Real.exp (-(escapeRate κ a * T)) * kPlus κ a ^ K * kMinus κ a ^ (N - K) /
      (1 / 3 * Real.exp (-(escapeRate κ a * T)) * kPlus κ a ^ (N - K) * kMinus κ a ^ K) =
      (kPlus κ a / kMinus κ a) ^ K / (kPlus κ a / kMinus κ a) ^ (N - K) by
    rw [div_pow, div_pow]; field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, ring_ldb κ a hκ,
    Nat.cast_sub hK]
  ring

/-- The representative computational choice `p = 3/4` corresponds to `a = log 3`. -/
theorem bias_log_three : Real.exp (Real.log 3) / (1 + Real.exp (Real.log 3)) = 3 / 4 := by
  rw [Real.exp_log (by norm_num)]; norm_num

/-! ### Sufficiency of the direction string -/

/-- **Sufficiency**: if the remaining path variables (initial site, jump times; here any
finite variable `W`) are produced from the direction string by a channel `C` that is common to
both hypotheses, discarding them loses no relative entropy. -/
theorem sufficient_statistic_no_loss {X W : Type*} [Fintype X] [Fintype W] {C : X → W → ℝ}
    (hC : IsChannel C) (P Q : X → ℝ) : KL (joint C P) (joint C Q) = KL P Q :=
  KL_joint hC

/-! ### Theorem `thm:ring` -/

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Encoded forward fixed-count ring law `P_m`. -/
noncomputable def ringP (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) : D × (Fin m → Bool) → ℝ :=
  encLaw F h jumpRev (bernProd p m)

/-- Encoded reversed-path ring law `Q_m`. -/
noncomputable def ringQ (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) : D × (Fin m → Bool) → ℝ :=
  encLaw F h jumpRev (bernProd (1 - p) m)

lemma ringQ_eq (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) :
    ringQ F h p m = encLaw F h jumpRev (fun x => bernProd p m (jumpRev x)) := by
  unfold ringQ; congr 1; funext x; rw [bernProd_jumpRev]

/-- **Theorem `thm:ring` (statistical part)**, Eqs. (ringkl)–(hoeffding): for `1/2 < p < 1`,
* `D(P_m‖Q_m) = m d(p)` and `d(p) > 0`,
* `TV(P_m,Q_m) = 1 - 2 e_m(p)`,
* `e_m(p) ≤ e^{-2m(p-1/2)²}`,
* the mean raw entropy production under the forward law is `m d(p)` (Eq. (ringkl), first
  equality, with the physical identification Eq. (thermoid)). -/
theorem ring_statistics [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) (m : ℕ) :
    KL (ringP F h p m) (ringQ F h p m) = m * drate p ∧ 0 < drate p ∧
    TV (ringP F h p m) (ringQ F h p m) = 1 - 2 * bayesErrBin m p ∧
    bayesErrBin m p ≤ Real.exp (-2 * m * (p - 1 / 2) ^ 2) ∧
    expect (bernProd p m) (llr (bernProd p m) (bernProd (1 - p) m)) = m * drate p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hKL, hTV, -⟩ := universal_concealment F h (jumpRev_involutive m)
    (bernProd_isProb hp0.le hp1.le m)
  have e : (fun x => bernProd p m (jumpRev x)) = bernProd (1 - p) m := by
    funext x; rw [bernProd_jumpRev]
  rw [e] at hKL hTV
  refine ⟨?_, drate_pos hp0 hp1 (by linarith), ?_, bayesErrBin_le_hoeffding hp.le hp1 m, ?_⟩
  · unfold ringP ringQ; rw [hKL, KL_bernProd hp0 hp1]
  · unfold ringP ringQ; rw [hTV, TV_bernProd hp.le hp1.le]
  · rw [← mean_sigma]
    unfold expect binExp
    exact sum_congr rfl fun x _ => by rw [llr_bernProd hp0 hp1]

/-- **Theorem `thm:ring` (computational part, finite form)**, Eq. (ringcomp): if the hard-core
experiment resists the class `TH` up to advantage `e`, and the reductions (sampling
`Ber(p)^{⊗m}` or `Ber(1-p)^{⊗m}`, reversal, composition) of the record tests lie in `TH`,
then every record test has advantage at most `2e`. -/
theorem ring_concealment [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (m : ℕ) (TR : Set (D × (Fin m → Bool) → ℝ)) (TH : Set (D × Bool → ℝ))
    (e : ℝ) (hhc : AdvLE TH (hcReal F h) (hcIdeal F) e)
    (hred : ∀ A ∈ TR, redTest jumpRev (bernProd p m) A ∈ TH ∧
      redTest jumpRev (bernProd (1 - p) m) A ∈ TH) :
    AdvLE TR (ringP F h p m) (ringQ F h p m) (2 * e) := by
  have := (universal_concealment F h (jumpRev_involutive m) (bernProd_isProb hp0 hp1 m)).2.2
    TR TH e hhc
  have e' : (fun x => bernProd p m (jumpRev x)) = bernProd (1 - p) m := by
    funext x; rw [bernProd_jumpRev]
  rw [e'] at this
  exact this hred

/-- **Theorem `thm:ring`, asymptotic form** (`m = 2n`): relative entropy `2n d(p) = Θ(n)`,
unrestricted advantage `TV ≥ 1 - 2 e^{-4n(p-1/2)²} = 1 - e^{-Ω(n)}`, and — under the hard-core
assumption and the polynomial-overhead closure of the reduction — negligible advantage for every
polynomial-size observer. -/
theorem ring_separation (Dn : ℕ → Type*) [∀ n, Fintype (Dn n)] [∀ n, DecidableEq (Dn n)]
    [∀ n, Nonempty (Dn n)] (F : ∀ n, Dn n ≃ Dn n) (h : ∀ n, Dn n → Bool)
    (TH : ∀ n, ℕ → Set (Dn n × Bool → ℝ)) (hhc : HardCoreAssumption Dn F h TH)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (TR : ∀ n, ℕ → Set (Dn n × (Fin (2 * n) → Bool) → ℝ)) (c : ℕ → ℕ) (hc : PolySize c)
    (hred : ∀ n s, ∀ A ∈ TR n s, redTest jumpRev (bernProd p (2 * n)) A ∈ TH n (s + c n) ∧
      redTest jumpRev (bernProd (1 - p) (2 * n)) A ∈ TH n (s + c n)) :
    (∀ n : ℕ, KL (ringP (F n) (h n) p (2 * n)) (ringQ (F n) (h n) p (2 * n)) =
      2 * n * drate p) ∧ 0 < drate p ∧
    (∀ n : ℕ, 1 - 2 * Real.exp (-4 * n * (p - 1 / 2) ^ 2) ≤
      TV (ringP (F n) (h n) p (2 * n)) (ringQ (F n) (h n) p (2 * n))) ∧
    (∀ s : ℕ → ℕ, PolySize s → ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, AdvLE (TR n (s n)) (ringP (F n) (h n) p (2 * n)) (ringQ (F n) (h n) p (2 * n))
        (ε n)) := by
  have hp0 : 0 < p := by linarith
  refine ⟨fun n => ?_, drate_pos hp0 hp1 (by linarith), fun n => ?_, fun s hs => ?_⟩
  · rw [(ring_statistics (F n) (h n) hp hp1 (2 * n)).1]; push_cast; ring
  · obtain ⟨-, -, hTV, hH, -⟩ := ring_statistics (F n) (h n) hp hp1 (2 * n)
    rw [hTV]
    have : Real.exp (-2 * ((2 * n : ℕ) : ℝ) * (p - 1 / 2) ^ 2) =
        Real.exp (-4 * n * (p - 1 / 2) ^ 2) := by push_cast; ring_nf
    linarith
  · obtain ⟨ε, hε, hb⟩ := hhc (fun n => s n + c n) (hs.add hc)
    exact ⟨fun n => 2 * ε n, hε.const_mul 2, fun n =>
      ring_concealment (F n) (h n) hp0.le hp1.le (2 * n) _ _ (ε n) (hb n) (hred n (s n))⟩

/-! ### Likelihoods and fluctuation relations in encoded coordinates -/

lemma ringQ_eq_comp (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) :
    ringQ F h p m = fun r => ringP F h p m (recRev jumpRev r) := by
  rw [ringQ_eq]; exact encLaw_reverse F h (jumpRev_involutive m) _

/-- **Eq. (encodedprob)**: `P_m(y,z) = 2^{-d} p^{|j|}(1-p)^{m-|j|}` with
`j = θ_m^{h(F⁻¹ y)} z` (here `2^{-d} = 1/|D|`). -/
theorem ringP_apply (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) (y : D) (z : Fin m → Bool) :
    ringP F h p m (y, z) = (1 / Fintype.card D) *
      (p ^ ones (thetaPow jumpRev (h (F.symm y)) z) *
        (1 - p) ^ (m - ones (thetaPow jumpRev (h (F.symm y)) z))) := by
  unfold ringP encLaw
  rw [show encoder F h jumpRev = encoderEquiv F h jumpRev (jumpRev_involutive m) from rfl,
    push_equiv]
  simp [encoderEquiv, prodLaw, unif, bernProd_eq]

/-- **Eq. (encodedprob)** for the reversed law. -/
theorem ringQ_apply (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) (y : D) (z : Fin m → Bool) :
    ringQ F h p m (y, z) = (1 / Fintype.card D) *
      ((1 - p) ^ ones (thetaPow jumpRev (h (F.symm y)) z) *
        p ^ (m - ones (thetaPow jumpRev (h (F.symm y)) z))) := by
  unfold ringQ
  have := ringP_apply F h (1 - p) m y z
  unfold ringP at this
  rw [this, sub_sub_cancel]

lemma ringP_pos [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (r : D × (Fin m → Bool)) : 0 < ringP F h p m r := by
  obtain ⟨y, z⟩ := r
  rw [ringP_apply]
  have : 0 < 1 - p := by linarith
  have : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  positivity

/-- **Eq. (encodedllr)**: the accessible record determines a unique entropy-production value
`ℓ_m(y,z) = a(2|j| - m)`. -/
theorem ring_encoded_llr [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) (y : D) (z : Fin m → Bool) :
    llr (ringP F h p m) (ringQ F h p m) (y, z) =
      affinity p * (2 * (ones (thetaPow jumpRev (h (F.symm y)) z) : ℝ) - m) := by
  rw [← llr_bernProd hp0 hp1]
  unfold llr
  rw [ringP_apply, ringQ_apply, bernProd_eq, bernProd_eq, sub_sub_cancel]
  have : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  rw [mul_div_mul_left _ _ (by positivity)]

/-- **Eqs. (encodedift), (encodeddft)**: in encoded coordinates the likelihood is odd under the
public reversal, `E_{P_m} e^{-ℓ_m} = 1`, and `P_m(ℓ_m = u) = e^u P_m(ℓ_m = -u)`. -/
theorem ring_encoded_fluctuations [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) :
    (∀ r, llr (ringP F h p m) (ringQ F h p m) (recRev jumpRev r) =
      - llr (ringP F h p m) (ringQ F h p m) r) ∧
    expect (ringP F h p m) (fun r => Real.exp (- llr (ringP F h p m) (ringQ F h p m) r)) = 1 ∧
    ∀ u : ℝ, ∑ r ∈ univ.filter (fun r => llr (ringP F h p m) (ringQ F h p m) r = u),
        ringP F h p m r =
      Real.exp u * ∑ r ∈ univ.filter (fun r => llr (ringP F h p m) (ringQ F h p m) r = -u),
        ringP F h p m r := by
  have hτ : Function.Involutive (recRev (D := D) (jumpRev (m := m))) := by
    intro r; simp [recRev, jumpRev_involutive m r.2]
  rw [ringQ_eq_comp]
  exact ⟨llr_reversal _ _ hτ, integral_fluctuation (encLaw_isProb F h _
    (bernProd_isProb hp0.le hp1.le m)) (ringP_pos F h hp0 hp1 m) _ hτ,
    detailed_fluctuation (ringP_pos F h hp0 hp1 m) _ hτ⟩

/-- The absolute current `|2|Z| - m|` of the one-bit encoding is time-reversal-even, hence has
exactly the same law under both orientation hypotheses. -/
theorem ring_abs_current_same_law (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) :
    push (fun r : D × (Fin m → Bool) => |2 * (ones r.2 : ℤ) - m|) (ringQ F h p m) =
      push (fun r : D × (Fin m → Bool) => |2 * (ones r.2 : ℤ) - m|) (ringP F h p m) := by
  have hτ : Function.Involutive (recRev (D := D) (jumpRev (m := m))) := by
    intro r; simp [recRev, jumpRev_involutive m r.2]
  rw [ringQ_eq_comp]
  refine push_even_statistic _ _ hτ _ fun r => ?_
  have := ones_jumpRev r.2
  simp only [recRev]
  rw [show (ones (jumpRev r.2) : ℤ) = m - ones r.2 by omega]
  rw [show 2 * ((m : ℤ) - ones r.2) - m = -(2 * ones r.2 - m) by ring, abs_neg]

/-! ### The cost of conditioning, Eq. (acceptance) -/

/-- Poisson probability `P[N(T) = m]` at mean `λT = m` (the count law is the physical input). -/
noncomputable def acceptProb (m : ℕ) : ℝ := Real.exp (-(m : ℝ)) * (m : ℝ) ^ m / m.factorial

/-- **Eq. (acceptance)**: `P[N(T)=m] = e^{-m} m^m/m! ∼ 1/√(2πm)` (by Stirling's formula). -/
theorem acceptProb_equiv :
    acceptProb ~[atTop] fun m : ℕ => 1 / Real.sqrt (2 * Real.pi * m) := by
  have hS := Stirling.factorial_isEquivalent_stirling
  have hnum : (fun m : ℕ => Real.exp (-(m : ℝ)) * (m : ℝ) ^ m) ~[atTop]
      (fun m : ℕ => Real.exp (-(m : ℝ)) * (m : ℝ) ^ m) := IsEquivalent.refl
  have := hnum.div hS
  refine this.congr_right ?_ |>.congr_left ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [Pi.div_apply]
    rw [div_pow, Real.exp_neg]
    have h1 : Real.exp 1 ^ m = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    rw [h1]
    have : 0 < Real.sqrt (2 * m * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.exp (m : ℝ) := Real.exp_pos _
    have : (0 : ℝ) < (m : ℝ) ^ m := by positivity
    rw [show 2 * Real.pi * (m : ℝ) = 2 * m * Real.pi by ring]
    field_simp
  · filter_upwards with m
    simp [acceptProb]

/-- Expected number of independent repetitions until acceptance, `1/P[N(T)=m] ∼ √(2πm)`. -/
theorem expected_trials_equiv :
    (fun m : ℕ => 1 / acceptProb m) ~[atTop] fun m : ℕ => Real.sqrt (2 * Real.pi * m) := by
  have := acceptProb_equiv.inv
  refine this.congr_right ?_ |>.congr_left ?_
  · filter_upwards with m; simp
  · filter_upwards with m; simp

end Arrow

end RingPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Poisson
    ════════════════════════════════════════════════════════════════════ -/

section PoissonPart

/-!
# Poisson counts (Section 6 and Appendix `app:algorithms`)

`poisW μ j = e^{-μ} μ^j / j!`. We prove normalisation, the mean, the first-moment tail
identity `E[N 1_{N>L}] = μ P[N ≥ L]` (Eq. (poissontail)), the generating function
`E x^N = e^{μ(x-1)}`, and the Chernoff tail bound
`P[N ≥ L] ≤ exp(-μ((1+δ)log(1+δ) - δ))` for `L ≥ (1+δ)μ`.
-/


open Finset Real Filter

namespace Arrow

/-- Poisson weights `w_j = e^{-μ} μ^j / j!` (Eq. (countweights)). -/
noncomputable def poisW (μ : ℝ) (j : ℕ) : ℝ := Real.exp (-μ) * μ ^ j / j.factorial

lemma poisW_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ poisW μ j := by
  unfold poisW; positivity

lemma hasSum_exp_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

/-- Poisson generating function `∑ w_j x^j = e^{μ(x-1)}`. -/
theorem poisW_hasSum_pow (μ x : ℝ) :
    HasSum (fun j => poisW μ j * x ^ j) (Real.exp (μ * (x - 1))) := by
  have := (hasSum_exp_series (μ * x)).mul_left (Real.exp (-μ))
  rw [← Real.exp_add, show -μ + μ * x = μ * (x - 1) by ring] at this
  convert this using 1
  funext j; unfold poisW; rw [mul_pow]; ring

/-- Normalisation `∑ w_j = 1`. -/
theorem poisW_hasSum_one (μ : ℝ) : HasSum (poisW μ) 1 := by
  have := poisW_hasSum_pow μ 1
  simpa using this

/-- Mean `∑ j w_j = μ`. -/
theorem poisW_hasSum_mean (μ : ℝ) : HasSum (fun j : ℕ => (j : ℝ) * poisW μ j) μ := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have := (poisW_hasSum_one μ).mul_left μ
  rw [mul_one] at this
  convert this using 1
  funext j
  unfold poisW
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Finite version of the shift identity: `∑_{j ≤ L} j w_j = μ ∑_{j < L} w_j`. -/
lemma poisW_partial_mean (μ : ℝ) (L : ℕ) :
    ∑ j ∈ range (L + 1), (j : ℝ) * poisW μ j = μ * ∑ j ∈ range L, poisW μ j := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih, sum_range_succ, mul_add]
    congr 1
    unfold poisW
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

/-- Tail of a convergent series. -/
lemma hasSum_tail {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) (L : ℕ) :
    HasSum (fun j => if L < j then f j else 0) (a - ∑ j ∈ range (L + 1), f j) := by
  have h0 : ∑ j ∈ range (L + 1), f j = ∑ j ∈ range (L + 1), (if L < j then 0 else f j) := by
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj; simp [show ¬ L < j by omega]
  have h1 : HasSum (fun j => if L < j then 0 else f j) (∑ j ∈ range (L + 1), f j) := by
    rw [h0]
    exact hasSum_sum_of_ne_finset_zero (fun j hj => by
        simp only [mem_range, not_lt] at hj; simp [show L < j by omega])
  convert hf.sub h1 using 1
  funext j; split_ifs <;> ring

/-- `P[N > L] = 1 - ∑_{j ≤ L} w_j`. -/
noncomputable def poisTailGT (μ : ℝ) (L : ℕ) : ℝ := ∑' j, if L < j then poisW μ j else 0

/-- `P[N ≥ L]`. -/
noncomputable def poisTailGE (μ : ℝ) (L : ℕ) : ℝ := ∑' j, if L ≤ j then poisW μ j else 0

lemma poisTailGT_eq (μ : ℝ) (L : ℕ) :
    poisTailGT μ L = 1 - ∑ j ∈ range (L + 1), poisW μ j :=
  (hasSum_tail (poisW_hasSum_one μ) L).tsum_eq

lemma poisTailGE_eq (μ : ℝ) (L : ℕ) :
    poisTailGE μ L = 1 - ∑ j ∈ range L, poisW μ j := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; simp [poisTailGE, (poisW_hasSum_one μ).tsum_eq]
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have := (hasSum_tail (poisW_hasSum_one μ) L').tsum_eq
    unfold poisTailGE
    rw [← this]
    congr 1

/-- **Eq. (poissontail)**: `E[N 1_{N>L}] = μ P[Poi(μ) ≥ L]`. -/
theorem poisson_tail_first_moment (μ : ℝ) (L : ℕ) :
    (∑' j : ℕ, if L < j then (j : ℝ) * poisW μ j else 0) = μ * poisTailGE μ L := by
  rw [(hasSum_tail (poisW_hasSum_mean μ) L).tsum_eq, poisTailGE_eq, poisW_partial_mean]
  ring

/-- **Chernoff tail bound** for the Poisson count: if `L ≥ (1+δ)μ` with `δ > 0`, `μ ≥ 0`, then
`P[N ≥ L] ≤ exp(-μ h(δ))`, `h(δ) = (1+δ) log(1+δ) - δ`. -/
theorem poisTailGE_le {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ) {L : ℕ} (hL : (1 + δ) * μ ≤ L) :
    poisTailGE μ L ≤ Real.exp (-(μ * ((1 + δ) * Real.log (1 + δ) - δ))) := by
  set t := Real.log (1 + δ)
  have ht : 0 ≤ t := Real.log_nonneg (by linarith)
  have het : Real.exp t = 1 + δ := Real.exp_log (by linarith)
  have hpt : ∀ j : ℕ, (if L ≤ j then poisW μ j else 0) ≤
      Real.exp (-(t * L)) * (poisW μ j * Real.exp t ^ j) := by
    intro j
    split_ifs with hj
    · have : Real.exp (-(t * L)) * Real.exp t ^ j = Real.exp (t * ((j : ℝ) - L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      have h1 : 1 ≤ Real.exp (t * ((j : ℝ) - L)) :=
        Real.one_le_exp (mul_nonneg ht (by
          have : (L : ℝ) ≤ j := by exact_mod_cast hj
          linarith))
      have h2 := poisW_nonneg hμ j
      calc poisW μ j = poisW μ j * 1 := (mul_one _).symm
        _ ≤ poisW μ j * Real.exp (t * ((j : ℝ) - L)) := mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by rw [← this]; ring
    · have := poisW_nonneg hμ j; positivity
  have hS := (poisW_hasSum_pow μ (Real.exp t)).mul_left (Real.exp (-(t * L)))
  have hsum : Summable (fun j => if L ≤ j then poisW μ j else 0) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs; exacts [poisW_nonneg hμ j, le_rfl])
      (fun j => by split_ifs; exacts [le_rfl, poisW_nonneg hμ j]) (poisW_hasSum_one μ).summable
  calc poisTailGE μ L ≤ Real.exp (-(t * L)) * Real.exp (μ * (Real.exp t - 1)) :=
        hasSum_le hpt hsum.hasSum hS
    _ ≤ Real.exp (-(μ * ((1 + δ) * t - δ))) := by
        rw [← Real.exp_add, het]
        apply Real.exp_le_exp.mpr
        have : t * ((1 + δ) * μ) ≤ t * L := mul_le_mul_of_nonneg_left hL ht
        nlinarith

/-- The Chernoff exponent `h(δ) = (1+δ)log(1+δ) - δ` is positive for `δ > 0`. -/
theorem poisson_rate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < (1 + δ) * Real.log (1 + δ) - δ := by
  have h := Real.log_lt_sub_one_of_pos (show 0 < (1 + δ)⁻¹ by positivity)
    (by rw [Ne, inv_eq_one]; linarith)
  rw [Real.log_inv] at h
  have : (1 + δ)⁻¹ = 1 / (1 + δ) := by rw [one_div]
  rw [this] at h
  have h2 : (1 + δ) * (1 / (1 + δ)) = 1 := by field_simp
  nlinarith

end Arrow

end PoissonPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Clocked
    ════════════════════════════════════════════════════════════════════ -/

section ClockedPart

/-!
# Section 6: a fixed-time experiment with an explicit cutoff (Theorem `thm:clocked`)

The stationary ring runs for time `T = μ/λ`; the jump count is `N ∼ Poi(μ)` (physical input),
and conditionally on `N = j` the directions are i.i.d. `Ber(p)`. With an integer cutoff `L`,
the record is `(N, F(S), θ_N^{h(S)} J)` if `N ≤ L` and a common overflow symbol `⊥` otherwise.

Record space: `Option (Σ j : Fin (L+1), D × (Fin j → Bool))` (`none = ⊥`).

Formalised:
* Eq. (capkl): `D(P^{≤L}‖Q^{≤L}) = d(p) E[N 1_{N≤L}]`;
* Eq. (poissonkl): the full core divergence (sum over count slices) is `μ d(p)`;
* Eq. (caploss): the deficit is `d(p) μ P[Poi(μ) ≥ L]`;
* Eq. (captv): `TV ≥ 1 - P(N>L) - 2 e^{-μ(1-e^{-c_p})}`, `c_p = 2(p-1/2)²`;
* explicit exponential bounds for `L ≥ (1+δ)μ`;
* the computational reduction (one hard-core bit replaced once for the whole experiment).
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Cutoff record space: `⊥` or `(N, y, z)` with `N ≤ L`. -/
abbrev CutRec (D : Type*) (L : ℕ) := Option (Σ j : Fin (L + 1), D × (Fin j → Bool))

/-- A law on cutoff records built from count weights `w`, overflow weight `wb` and slice laws. -/
def cutLaw {L : ℕ} (w : ℕ → ℝ) (wb : ℝ) (Pj : ∀ j : ℕ, D × (Fin j → Bool) → ℝ) :
    CutRec D L → ℝ
  | none => wb
  | some ⟨j, r⟩ => w j * Pj j r

omit [DecidableEq D] in
lemma cutLaw_isProb {L : ℕ} {w : ℕ → ℝ} {wb : ℝ} {Pj : ∀ j : ℕ, D × (Fin j → Bool) → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hwb : 0 ≤ wb) (hsum : wb + ∑ j ∈ range (L + 1), w j = 1)
    (hP : ∀ j, IsProb (Pj j)) : IsProb (cutLaw (L := L) w wb Pj) := by
  refine ⟨fun o => ?_, ?_⟩
  · rcases o with _ | ⟨j, r⟩
    · exact hwb
    · exact mul_nonneg (hw j) ((hP j).nonneg r)
  · rw [Fintype.sum_option, Fintype.sum_sigma]
    simp only [cutLaw, ← mul_sum, (hP _).sum_one, mul_one]
    rw [Fin.sum_univ_eq_sum_range (fun j => w j), hsum]

omit [DecidableEq D] in
/-- Relative entropy decomposes over count slices (the count law is common to both
hypotheses and overflow contributes zero divergence). -/
theorem KL_cutLaw {L : ℕ} {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (wb : ℝ)
    (P Q : ∀ j : ℕ, D × (Fin j → Bool) → ℝ) :
    KL (cutLaw (L := L) w wb P) (cutLaw (L := L) w wb Q) =
      ∑ j ∈ range (L + 1), w j * KL (P j) (Q j) := by
  unfold KL
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [cutLaw]
  have h0 : wb * Real.log (wb / wb) = 0 := by
    rcases eq_or_ne wb 0 with h | h
    · simp [h]
    · simp [div_self h]
  rw [h0, zero_add, ← Fin.sum_univ_eq_sum_range (fun j => w j * ∑ x, P j x *
    Real.log (P j x / Q j x))]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rcases (hw j).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [mul_div_mul_left _ _ h.ne']; ring

omit [DecidableEq D] in
/-- Total variation decomposes over count slices. -/
theorem TV_cutLaw {L : ℕ} {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (wb : ℝ)
    (P Q : ∀ j : ℕ, D × (Fin j → Bool) → ℝ) :
    TV (cutLaw (L := L) w wb P) (cutLaw (L := L) w wb Q) =
      ∑ j ∈ range (L + 1), w j * TV (P j) (Q j) := by
  unfold TV
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [cutLaw, sub_self, abs_zero, zero_add]
  rw [← Fin.sum_univ_eq_sum_range (fun j => w j * (1 / 2 * ∑ x, |P j x - Q j x|)), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have : ∀ r, |w j * P j r - w j * Q j r| = w j * |P j r - Q j r| := fun r => by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw j)]
  simp_rw [this, ← mul_sum]; ring

/-- Forward cutoff record law `P^{≤L}`. -/
noncomputable def cutP (F : D ≃ D) (h : D → Bool) (p μ : ℝ) (L : ℕ) : CutRec D L → ℝ :=
  cutLaw (poisW μ) (poisTailGT μ L) (fun j => ringP F h p j)

/-- Reversed cutoff record law `Q^{≤L}`. -/
noncomputable def cutQ (F : D ≃ D) (h : D → Bool) (p μ : ℝ) (L : ℕ) : CutRec D L → ℝ :=
  cutLaw (poisW μ) (poisTailGT μ L) (fun j => ringQ F h p j)

/-- The full core divergence of the fixed-time experiment, obtained by summing the conditional
divergences `j d(p)` over all count slices with Poisson weights. -/
noncomputable def fullCoreKL (p μ : ℝ) : ℝ := ∑' j : ℕ, poisW μ j * (j * drate p)

/-- **Eq. (poissonkl)**: `D(𝖯‖𝖰) = μ d(p)`. -/
theorem fullCoreKL_eq (p μ : ℝ) : fullCoreKL p μ = μ * drate p := by
  unfold fullCoreKL
  have := (poisW_hasSum_mean μ).mul_right (drate p)
  rw [← this.tsum_eq]
  congr 1; funext j; ring

/-- **Theorem `thm:clocked`, Eq. (capkl)**: `D(P^{≤L}‖Q^{≤L}) = d(p) E[N 1_{N ≤ L}]`. -/
theorem clocked_KL [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    {μ : ℝ} (hμ : 0 ≤ μ) (L : ℕ) :
    KL (cutP F h p μ L) (cutQ F h p μ L) =
      drate p * ∑ j ∈ range (L + 1), (j : ℝ) * poisW μ j := by
  unfold cutP cutQ
  rw [KL_cutLaw (poisW_nonneg hμ), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [(ring_statistics F h hp hp1 j).1]; ring

/-- **Theorem `thm:clocked`, Eq. (caploss)**: the overflow loses exactly
`d(p) μ P[Poi(μ) ≥ L]`. -/
theorem clocked_KL_loss [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {μ : ℝ} (hμ : 0 ≤ μ) (L : ℕ) :
    fullCoreKL p μ - KL (cutP F h p μ L) (cutQ F h p μ L) = drate p * μ * poisTailGE μ L := by
  rw [fullCoreKL_eq, clocked_KL F h hp hp1 hμ L, poisW_partial_mean, poisTailGE_eq]
  ring

/-- **Theorem `thm:clocked`, Eq. (captv)**:
`TV(P^{≤L},Q^{≤L}) ≥ 1 - P(N>L) - 2 e^{-μ(1-e^{-c_p})}` with `c_p = 2(p-1/2)²`. -/
theorem clocked_TV [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {μ : ℝ} (hμ : 0 ≤ μ) (L : ℕ) :
    1 - poisTailGT μ L - 2 * Real.exp (-(μ * (1 - Real.exp (-(2 * (p - 1 / 2) ^ 2))))) ≤
      TV (cutP F h p μ L) (cutQ F h p μ L) := by
  set x := Real.exp (-(2 * (p - 1 / 2) ^ 2))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  unfold cutP cutQ
  rw [TV_cutLaw (poisW_nonneg hμ)]
  have hslice : ∀ j : ℕ, poisW μ j * (1 - 2 * x ^ j) ≤ poisW μ j * TV (ringP F h p j) (ringQ F h p j) := by
    intro j
    obtain ⟨-, -, hTV, hH, -⟩ := ring_statistics F h hp hp1 j
    refine mul_le_mul_of_nonneg_left ?_ (poisW_nonneg hμ j)
    rw [hTV]
    have : x ^ j = Real.exp (-2 * j * (p - 1 / 2) ^ 2) := by
      rw [← Real.exp_nat_mul]; ring_nf
    linarith
  have hgen : ∑ j ∈ range (L + 1), poisW μ j * x ^ j ≤ Real.exp (μ * (x - 1)) :=
    sum_le_hasSum _ (fun j _ => mul_nonneg (poisW_nonneg hμ j) (pow_nonneg hx0 j))
      (poisW_hasSum_pow μ x)
  calc 1 - poisTailGT μ L - 2 * Real.exp (-(μ * (1 - x)))
      = ∑ j ∈ range (L + 1), poisW μ j - 2 * Real.exp (μ * (x - 1)) := by
        rw [poisTailGT_eq]; ring_nf
    _ ≤ ∑ j ∈ range (L + 1), poisW μ j - 2 * ∑ j ∈ range (L + 1), poisW μ j * x ^ j := by
        linarith
    _ = ∑ j ∈ range (L + 1), poisW μ j * (1 - 2 * x ^ j) := by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    _ ≤ _ := sum_le_sum fun j _ => hslice j

/-- **Theorem `thm:clocked`, quantitative form.** With `L ≥ (1+δ)μ`, `δ > 0`, and
`h(δ) = (1+δ)log(1+δ) - δ > 0`:
* the observed divergence is at least `μ d(p) (1 - e^{-μ h(δ)})` and at most `μ d(p)`;
* the deficit from the full core divergence is at most `μ d(p) e^{-μ h(δ)}`;
* `TV ≥ 1 - e^{-μ h(δ)} - 2 e^{-μ(1-e^{-c_p})}`.
With `μ = γ n` this is `Θ(n)`, `O(n) e^{-Ω(n)}` and `1 - e^{-Ω(n)}` respectively. -/
theorem clocked_bounds [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ) {L : ℕ} (hL : (1 + δ) * μ ≤ L) :
    μ * drate p * (1 - Real.exp (-(μ * ((1 + δ) * Real.log (1 + δ) - δ)))) ≤
        KL (cutP F h p μ L) (cutQ F h p μ L) ∧
    KL (cutP F h p μ L) (cutQ F h p μ L) ≤ μ * drate p ∧
    fullCoreKL p μ - KL (cutP F h p μ L) (cutQ F h p μ L) ≤
        μ * drate p * Real.exp (-(μ * ((1 + δ) * Real.log (1 + δ) - δ))) ∧
    1 - Real.exp (-(μ * ((1 + δ) * Real.log (1 + δ) - δ))) -
        2 * Real.exp (-(μ * (1 - Real.exp (-(2 * (p - 1 / 2) ^ 2))))) ≤
      TV (cutP F h p μ L) (cutQ F h p μ L) := by
  have hloss := clocked_KL_loss F h hp hp1 hμ L
  have htail := poisTailGE_le hμ hδ hL
  have hd : 0 < drate p := drate_pos (by linarith) hp1 (by linarith)
  have hGE0 : 0 ≤ poisTailGE μ L :=
    tsum_nonneg fun j => by split_ifs; exacts [poisW_nonneg hμ j, le_rfl]
  have hGT : poisTailGT μ L ≤ poisTailGE μ L := by
    rw [poisTailGT_eq, poisTailGE_eq, sum_range_succ]
    linarith [poisW_nonneg hμ L]
  have hKL : KL (cutP F h p μ L) (cutQ F h p μ L) = μ * drate p - drate p * μ * poisTailGE μ L := by
    rw [← hloss, fullCoreKL_eq]; ring
  have hdμ : 0 ≤ drate p * μ := mul_nonneg hd.le hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hKL]; nlinarith
  · rw [hKL]; nlinarith
  · rw [hloss]; nlinarith
  · linarith [clocked_TV F h hp hp1 hμ L]

/-! ### Computational hiding for the cutoff record -/

/-- The reduction for the cutoff record: given a hard-core challenge `(y, b)`, sample the count
`N` (overflow with weight `wb`), the directions `J ∼ P⁰_N`, and feed `(N, y, θ_N^b J)` (or `⊥`)
to the record distinguisher. The hard-core bit is replaced once for the whole experiment. -/
noncomputable def redCut {L : ℕ} (w : ℕ → ℝ) (wb : ℝ) (P0 : ∀ j : ℕ, (Fin j → Bool) → ℝ)
    (A : CutRec D L → ℝ) : D × Bool → ℝ :=
  fun yb => wb * A none + ∑ j : Fin (L + 1),
    w j * redTest jumpRev (P0 j) (fun r => A (some ⟨j, r⟩)) yb

omit [DecidableEq D] in
lemma expect_redCut {L : ℕ} (R : D × Bool → ℝ) (hR : IsProb R) (w : ℕ → ℝ) (wb : ℝ)
    (P0 : ∀ j : ℕ, (Fin j → Bool) → ℝ) (A : CutRec D L → ℝ) :
    expect R (redCut w wb P0 A) = wb * A none + ∑ j : Fin (L + 1),
      w j * expect R (redTest jumpRev (P0 j) (fun r => A (some ⟨j, r⟩))) := by
  unfold redCut expect
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1
  · first | rw [hR.sum_one, one_mul] | rw [← sum_mul, hR.sum_one, one_mul]
  · rw [sum_comm]; exact sum_congr rfl fun j _ => sum_congr rfl fun x _ => by ring

omit [DecidableEq D] in
lemma expect_cutLaw {L : ℕ} (w : ℕ → ℝ) (wb : ℝ) (Pj : ∀ j : ℕ, D × (Fin j → Bool) → ℝ)
    (A : CutRec D L → ℝ) :
    expect (cutLaw w wb Pj) A = wb * A none + ∑ j : Fin (L + 1),
      w j * expect (Pj j) (fun r => A (some ⟨j, r⟩)) := by
  unfold expect
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [cutLaw, mul_sum]
  congr 1
  exact sum_congr rfl fun j _ => sum_congr rfl fun r _ => by ring

omit [Fintype D] [DecidableEq D] in
lemma redCut_isTest {L : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A : CutRec D L → ℝ} (hA : IsTest A) :
    IsTest (redCut (L := L) (poisW μ) (poisTailGT μ L) (fun j => bernProd p j) A) := by
  have hwb : 0 ≤ poisTailGT μ L :=
    tsum_nonneg fun j => by split_ifs; exacts [poisW_nonneg hμ j, le_rfl]
  intro yb
  have ht : ∀ j : Fin (L + 1), IsTest (redTest (D := D) jumpRev (bernProd p j)
      (fun r => A (some ⟨j, r⟩))) := fun j =>
    redTest_isTest jumpRev (bernProd_isProb hp0 hp1 j) (fun r => hA _)
  unfold redCut
  constructor
  · exact add_nonneg (mul_nonneg hwb (hA _).1)
      (sum_nonneg fun j _ => mul_nonneg (poisW_nonneg hμ j) ((ht j) yb).1)
  · calc _ ≤ poisTailGT μ L * 1 + ∑ j : Fin (L + 1), poisW μ j * 1 := by
          gcongr with j
          · exact (hA _).2
          · exact poisW_nonneg hμ j
          · exact ((ht j) yb).2
      _ = 1 := by
          rw [mul_one, Fin.sum_univ_eq_sum_range (fun j => poisW μ j * 1)]
          simp only [mul_one]
          rw [poisTailGT_eq]; ring

/-- **Theorem `thm:clocked` (computational part)**: if the hard-core experiment resists the
class `TH` up to advantage `e` and the two reductions of every record test lie in `TH`
(polynomial-precision count sampling, see Appendix `app:algorithms`, is part of this
complexity-theoretic closure hypothesis), then every record test has advantage at most `2e`. -/
theorem clocked_concealment [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) {μ : ℝ} (hμ : 0 ≤ μ) (L : ℕ) (TR : Set (CutRec D L → ℝ))
    (TH : Set (D × Bool → ℝ)) (e : ℝ) (hhc : AdvLE TH (hcReal F h) (hcIdeal F) e)
    (hred : ∀ A ∈ TR,
      redCut (poisW μ) (poisTailGT μ L) (fun j => bernProd p j) A ∈ TH ∧
      redCut (poisW μ) (poisTailGT μ L) (fun j => bernProd (1 - p) j) A ∈ TH) :
    AdvLE TR (cutP F h p μ L) (cutQ F h p μ L) (2 * e) := by
  intro A hA hAt
  have hR : IsProb (hcReal F h) := unif_isProb.push _
  have hI : IsProb (hcIdeal F) := (prodLaw_isProb unif_isProb unif_isProb).push _
  have h1 := hhc _ (hred A hA).1 (redCut_isTest hμ hp0 hp1 hAt)
  have h2 := hhc _ (hred A hA).2 (redCut_isTest hμ (by linarith) (by linarith) hAt)
  unfold adv at h1 h2 ⊢
  rw [expect_redCut _ hR, expect_redCut _ hI] at h1 h2
  simp only [expect_hcReal_redTest] at h1 h2
  have hsym : ∀ j : Fin (L + 1), expect (hcIdeal F) (redTest jumpRev (bernProd p j)
      (fun r => A (some ⟨j, r⟩))) = expect (hcIdeal F) (redTest jumpRev (bernProd (1 - p) j)
      (fun r => A (some ⟨j, r⟩))) := by
    intro j
    rw [expect_hcIdeal_redTest F (jumpRev_involutive j)]
    congr 2; funext x; rw [bernProd_jumpRev]
  simp only [hsym] at h1
  have eP : expect (cutP F h p μ L) A = poisTailGT μ L * A none + ∑ j : Fin (L + 1),
      poisW μ j * expect (encLaw F h jumpRev (bernProd p j)) (fun r => A (some ⟨j, r⟩)) := by
    unfold cutP; rw [expect_cutLaw]; rfl
  have eQ : expect (cutQ F h p μ L) A = poisTailGT μ L * A none + ∑ j : Fin (L + 1),
      poisW μ j * expect (encLaw F h jumpRev (bernProd (1 - p) j)) (fun r => A (some ⟨j, r⟩)) := by
    unfold cutQ; rw [expect_cutLaw]; rfl
  rw [eP, eQ]
  set a := poisTailGT μ L * A none + ∑ j : Fin (L + 1),
      poisW μ j * expect (encLaw F h jumpRev (bernProd p j)) (fun r => A (some ⟨j, r⟩))
  set b := poisTailGT μ L * A none + ∑ j : Fin (L + 1),
      poisW μ j * expect (encLaw F h jumpRev (bernProd (1 - p) j)) (fun r => A (some ⟨j, r⟩))
  set c := poisTailGT μ L * A none + ∑ j : Fin (L + 1), poisW μ j * expect (hcIdeal F)
      (redTest jumpRev (bernProd (1 - p) j) (fun r => A (some ⟨j, r⟩)))
  have := abs_sub_le a c b
  rw [abs_sub_comm c b] at this
  linarith

end Arrow

end ClockedPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Generator
    ════════════════════════════════════════════════════════════════════ -/

section GeneratorPart

/-!
# Section 7: the endpoint-augmented hard-core generator (Lemma `lem:generator`)

`Y = F^ℓ(S)`, `K_i = h(F^{i}(S))` for `i = 0, …, ℓ-1` (Eq. (generator), 0-indexed).
The hybrid argument shows that every test distinguishing `(Y, K)` from `(U_d, U_ℓ)` has
advantage at most the sum of `ℓ` hard-core advantages (Eq. (generatorbound)).
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The real generator output `(F^ℓ(S), (h(F^i(S)))_{i<ℓ})`. -/
noncomputable def genReal (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) : D × (Fin ℓ → Bool) → ℝ :=
  push (fun s => ((F ^ ℓ) s, fun i : Fin ℓ => h ((F ^ (i : ℕ)) s))) (unif D)

/-- The ideal output: an independent uniform endpoint and `ℓ` fair bits. -/
noncomputable def genIdeal (ℓ : ℕ) : D × (Fin ℓ → Bool) → ℝ :=
  prodLaw (unif D) (unif (Fin ℓ → Bool))

/-- Hybrid `j`: the first `j` bits are fair, the remaining ones are generated by iteration from
a uniform point `u` (which is distributed as `F^j(S)`). -/
noncomputable def hybridGen (F : D ≃ D) (h : D → Bool) (ℓ j : ℕ) (A : D × (Fin ℓ → Bool) → ℝ) :
    ℝ :=
  expect (prodLaw (unif D) (unif (Fin ℓ → Bool))) fun ub =>
    A ((F ^ (ℓ - j)) ub.1, fun i => if (i : ℕ) < j then ub.2 i else h ((F ^ ((i : ℕ) - j)) ub.1))

/-- The reduction for the hybrid transition `j → j+1`: on challenge `(y', c)`, sample `j` fair
bits, use `c` as bit `j`, and generate the later bits and the endpoint by forward iteration
from `y'`. -/
noncomputable def genRed (F : D ≃ D) (h : D → Bool) (ℓ j : ℕ) (A : D × (Fin ℓ → Bool) → ℝ) :
    D × Bool → ℝ :=
  fun yc => expect (unif (Fin ℓ → Bool)) fun b =>
    A ((F ^ (ℓ - j - 1)) yc.1, fun i => if (i : ℕ) < j then b i else if (i : ℕ) = j then yc.2
      else h ((F ^ ((i : ℕ) - j - 1)) yc.1))

omit [Fintype D] [DecidableEq D] in
lemma perm_pow_succ_apply (F : D ≃ D) (n : ℕ) (u : D) : (F ^ (n + 1)) u = (F ^ n) (F u) := by
  rw [pow_succ, Equiv.Perm.mul_apply]

omit [Fintype D] [DecidableEq D] in
lemma genRed_isTest [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ j : ℕ) {A : D × (Fin ℓ → Bool) → ℝ}
    (hA : IsTest A) : IsTest (genRed F h ℓ j A) := by
  intro yc
  have hU : IsProb (unif (Fin ℓ → Bool)) := unif_isProb
  constructor
  · exact sum_nonneg fun b _ => mul_nonneg (hU.nonneg b) (hA _).1
  · calc genRed F h ℓ j A yc ≤ expect (unif (Fin ℓ → Bool)) (fun _ => 1) :=
          expect_mono hU.nonneg fun b => (hA _).2
      _ = 1 := expect_const _ hU 1

lemma hybridGen_zero [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (A : D × (Fin ℓ → Bool) → ℝ) :
    hybridGen F h ℓ 0 A = expect (genReal F h ℓ) A := by
  unfold hybridGen genReal
  rw [expect_push, expect_prodLaw]
  simp only [Nat.not_lt_zero, if_false, Nat.sub_zero]
  unfold expect
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_mul, show ∑ b : Fin ℓ → Bool, unif (Fin ℓ → Bool) b = 1 from unif_isProb.sum_one,
    one_mul]

omit [DecidableEq D] in
lemma hybridGen_last (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (A : D × (Fin ℓ → Bool) → ℝ) :
    hybridGen F h ℓ ℓ A = expect (genIdeal ℓ) A := by
  unfold hybridGen genIdeal
  simp only [Nat.sub_self, pow_zero, Equiv.Perm.coe_one, id, Fin.is_lt, if_true]

/-- Averaging over a fresh bit placed at coordinate `j` is the same as averaging over the
`j`-th coordinate of the uniform bit string. -/
lemma sum_update_bool {ℓ : ℕ} (j : Fin ℓ) (f : (Fin ℓ → Bool) → ℝ) :
    ∑ c : Bool, ∑ b : Fin ℓ → Bool, f (Function.update b j c) = 2 * ∑ b, f b := by
  rw [sum_comm]
  simp only [Fintype.sum_bool, sum_add_distrib]
  have e : ∀ b : Fin ℓ → Bool, f (Function.update b j true) + f (Function.update b j false) =
      f b + f (Function.update b j (!b j)) := by
    intro b
    cases hb : b j
    · rw [show Function.update b j false = b by rw [← hb]; exact Function.update_eq_self j b]
      simp [add_comm]
    · rw [show Function.update b j true = b by rw [← hb]; exact Function.update_eq_self j b]
      simp
  rw [← sum_add_distrib, sum_congr rfl fun b _ => e b, sum_add_distrib]
  have : ∑ b : Fin ℓ → Bool, f (Function.update b j (!b j)) = ∑ b, f b := by
    refine Fintype.sum_equiv (Function.Involutive.toPerm (fun b => Function.update b j (!b j))
      (fun b => by funext i; by_cases hi : i = j <;> simp [Function.update_apply, hi])) _ _
      (fun b => rfl)
  rw [this]; ring

lemma expect_hcReal_genRed [Nonempty D] (F : D ≃ D) (h : D → Bool) {ℓ j : ℕ} (hj : j < ℓ)
    (A : D × (Fin ℓ → Bool) → ℝ) :
    expect (hcReal F h) (genRed F h ℓ j A) = hybridGen F h ℓ j A := by
  unfold hcReal hybridGen genRed
  rw [expect_push, expect_prodLaw]
  unfold expect
  refine sum_congr rfl fun u _ => ?_
  congr 1
  refine sum_congr rfl fun b _ => ?_
  congr 1
  have e1 : (F ^ (ℓ - j - 1)) (F u) = (F ^ (ℓ - j)) u := by
    rw [← perm_pow_succ_apply, show ℓ - j - 1 + 1 = ℓ - j by omega]
  beta_reduce
  congr 1
  refine Prod.ext e1 (funext fun i => ?_)
  · simp only
    split_ifs with h1 h2
    · rfl
    · rw [h2]; simp
    · rw [← perm_pow_succ_apply, show (i : ℕ) - j - 1 + 1 = (i : ℕ) - j by omega]

lemma expect_hcIdeal_genRed (F : D ≃ D) (h : D → Bool) {ℓ j : ℕ} (hj : j < ℓ)
    (A : D × (Fin ℓ → Bool) → ℝ) :
    expect (hcIdeal F) (genRed F h ℓ j A) = hybridGen F h ℓ (j + 1) A := by
  unfold hcIdeal hybridGen genRed
  rw [expect_push, expect_prodLaw, expect_prodLaw]
  -- reindex the seed by the permutation `F`
  rw [show (∑ a, unif D a * ∑ b, unif Bool b *
      expect (unif (Fin ℓ → Bool)) (fun b' => A ((F ^ (ℓ - j - 1)) (F a), fun i =>
        if (i : ℕ) < j then b' i else if (i : ℕ) = j then b else
          h ((F ^ ((i : ℕ) - j - 1)) (F a))))) =
      ∑ a, unif D a * ∑ b, unif Bool b *
      expect (unif (Fin ℓ → Bool)) (fun b' => A ((F ^ (ℓ - j - 1)) a, fun i =>
        if (i : ℕ) < j then b' i else if (i : ℕ) = j then b else
          h ((F ^ ((i : ℕ) - j - 1)) a))) from
    Fintype.sum_equiv F _ _ (fun a => by simp [unif])]
  refine sum_congr rfl fun u _ => ?_
  congr 1
  set jj : Fin ℓ := ⟨j, hj⟩
  set f : (Fin ℓ → Bool) → ℝ := fun b => A ((F ^ (ℓ - (j + 1))) u, fun i =>
    if (i : ℕ) < j + 1 then b i else h ((F ^ ((i : ℕ) - (j + 1))) u))
  have key : ∀ (c : Bool) (b : Fin ℓ → Bool),
      A ((F ^ (ℓ - j - 1)) u, fun i => if (i : ℕ) < j then b i else if (i : ℕ) = j then c else
        h ((F ^ ((i : ℕ) - j - 1)) u)) = f (Function.update b jj c) := by
    intro c b
    simp only [f]
    congr 1
    refine Prod.ext (by simp only; rw [Nat.sub_sub]) (funext fun i => ?_)
    · simp only
      by_cases h1 : (i : ℕ) < j
      · have : i ≠ jj := fun e => by rw [e] at h1; simp [jj] at h1
        simp [h1, this, show (i : ℕ) < j + 1 by omega]
      · by_cases h2 : (i : ℕ) = j
        · have : i = jj := Fin.ext h2
          rw [if_neg h1, if_pos h2, if_pos (by omega), this, Function.update_self]
        · have : i ≠ jj := fun e => h2 (by rw [e])
          simp [h1, h2, show ¬ (i : ℕ) < j + 1 by omega, Nat.sub_sub]
  unfold expect
  simp_rw [key]
  simp only [unif, Fintype.card_bool]
  simp_rw [← mul_sum]
  show _ = 1 / (Fintype.card (Fin ℓ → Bool) : ℝ) * ∑ b, f b
  rw [sum_update_bool jj f]
  push_cast
  ring

/-- **Lemma `lem:generator` (hybrid inequality).** The advantage of a test between the real
generator output and the ideal output is at most the sum of the advantages of the `ℓ` hybrid
reductions in the hard-core experiment. -/
theorem adv_gen_le_sum [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    (A : D × (Fin ℓ → Bool) → ℝ) :
    adv (genReal F h ℓ) (genIdeal ℓ) A ≤
      ∑ j ∈ range ℓ, adv (hcReal F h) (hcIdeal F) (genRed F h ℓ j A) := by
  unfold adv
  rw [← hybridGen_zero, ← hybridGen_last]
  have tel : hybridGen F h ℓ 0 A - hybridGen F h ℓ ℓ A =
      ∑ j ∈ range ℓ, (hybridGen F h ℓ j A - hybridGen F h ℓ (j + 1) A) := by
    rw [← neg_sub, ← sum_range_sub (fun j => hybridGen F h ℓ j A) ℓ, ← sum_neg_distrib]
    simp
  rw [tel]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => le_of_eq ?_)
  rw [mem_range] at hj
  rw [expect_hcReal_genRed F h hj, expect_hcIdeal_genRed F h hj]

/-- **Lemma `lem:generator`** (Eq. (generatorbound)): if every hybrid reduction of a test of the
class `T` lies in the hard-core observer class `TH`, whose advantage is at most `e`, then the
generator output is `ℓ e`-indistinguishable from `(U_d, U_ℓ)` for the class `T`. -/
theorem generator_bound [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    (T : Set (D × (Fin ℓ → Bool) → ℝ)) (TH : Set (D × Bool → ℝ)) (e : ℝ)
    (hhc : AdvLE TH (hcReal F h) (hcIdeal F) e)
    (hred : ∀ A ∈ T, ∀ j < ℓ, genRed F h ℓ j A ∈ TH) :
    AdvLE T (genReal F h ℓ) (genIdeal ℓ) (ℓ * e) := by
  intro A hA hAt
  refine (adv_gen_le_sum F h ℓ A).trans ?_
  calc ∑ j ∈ range ℓ, adv (hcReal F h) (hcIdeal F) (genRed F h ℓ j A) ≤ ∑ _j ∈ range ℓ, e :=
        sum_le_sum fun j hj => hhc _ (hred A hA j (mem_range.mp hj)) (genRed_isTest F h ℓ j hAt)
    _ = ℓ * e := by simp

end Arrow

end GeneratorPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Causal
    ════════════════════════════════════════════════════════════════════ -/

section CausalPart

/-!
# Section 7: causal recording with a palindromic mask (Theorem `thm:causal`)

Direction strings of even length `m = 2ℓ` are `Fin (2ℓ) → Bool`. The palindromic mask
`M(K) = (K₁,…,K_ℓ,K_ℓ,…,K₁)` (Eq. (palindrome)) is `M(K)_i = K_{fold i}` and the causal encoder
is `E_c(s,j) = (F^ℓ(s), j ⊕ M(K(s)))` with `K(s)_i = h(F^i(s))` (Eq. (causalencoder)).

Formalised:
* `E_c` is a bijection and commutes with the public reversal `τ(y,z) = (y, 1 ⊕ rev z)`
  (Eq. (maskcommute)); KL and TV are preserved;
* with an ideal uniform mask the forward and reversed laws coincide exactly, for *every*
  (possibly correlated) direction law;
* Eq. (causaladv): advantage at most `2ℓ ε_hc`, via Lemma `lem:generator`;
* Eq. (pairideal): ideal masked mirror-pair probabilities for i.i.d. directions.
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Folding a position of a length-`2ℓ` string onto its mirror-pair index. -/
def fold {ℓ : ℕ} (i : Fin (2 * ℓ)) : Fin ℓ :=
  if h : (i : ℕ) < ℓ then ⟨i, h⟩ else ⟨2 * ℓ - 1 - i, by have := i.isLt; omega⟩

/-- The first `ℓ` positions. -/
def emb {ℓ : ℕ} (k : Fin ℓ) : Fin (2 * ℓ) := ⟨k, by have := k.isLt; omega⟩

lemma fold_rev {ℓ : ℕ} (i : Fin (2 * ℓ)) : fold (Fin.rev i) = fold i := by
  have := i.isLt
  unfold fold
  simp only [Fin.val_rev]
  split_ifs with h1 h2 h2 <;> (apply Fin.ext; simp) <;> omega

lemma emb_fold {ℓ : ℕ} (i : Fin (2 * ℓ)) : emb (fold i) = i ∨ emb (fold i) = Fin.rev i := by
  have := i.isLt
  unfold fold emb
  split_ifs with h
  · left; rfl
  · right; apply Fin.ext; simp only [Fin.val_rev]; omega

/-- The palindromic mask `M(K)`. -/
def mask {ℓ : ℕ} (K : Fin ℓ → Bool) : Fin (2 * ℓ) → Bool := fun i => K (fold i)

lemma mask_rev {ℓ : ℕ} (K : Fin ℓ → Bool) (i : Fin (2 * ℓ)) : mask K (Fin.rev i) = mask K i := by
  simp [mask, fold_rev]

/-- Coordinatewise XOR. -/
def xorS {n : ℕ} (a b : Fin n → Bool) : Fin n → Bool := fun i => xor (a i) (b i)

/-- The generator bits `K(s)_i = h(F^i(s))`. -/
def genBits (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (s : D) : Fin ℓ → Bool :=
  fun i => h ((F ^ (i : ℕ)) s)

/-- The causal encoder `E_c(s,j) = (F^ℓ(s), j ⊕ M(K(s)))`. -/
def causalEnc (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) :
    D × (Fin (2 * ℓ) → Bool) → D × (Fin (2 * ℓ) → Bool) :=
  fun sj => ((F ^ ℓ) sj.1, xorS sj.2 (mask (genBits F h ℓ sj.1)))

/-- `E_c` is a bijection: the endpoint determines `s` (inverting `F` `ℓ` times) and then the
payload determines `j`. -/
def causalEncEquiv (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) :
    D × (Fin (2 * ℓ) → Bool) ≃ D × (Fin (2 * ℓ) → Bool) where
  toFun := causalEnc F h ℓ
  invFun yz := ((F ^ ℓ).symm yz.1, xorS yz.2 (mask (genBits F h ℓ ((F ^ ℓ).symm yz.1))))
  left_inv sj := by
    obtain ⟨s, j⟩ := sj
    simp only [causalEnc, Equiv.symm_apply_apply, Prod.mk.injEq, true_and]
    funext i; simp [xorS]
  right_inv yz := by
    obtain ⟨y, z⟩ := yz
    simp only [causalEnc, Equiv.apply_symm_apply, Prod.mk.injEq, true_and]
    funext i; simp [xorS]

omit [Fintype D] [DecidableEq D] in
/-- **Eq. (maskcommute)**: since `M = rev M`, the causal encoder commutes with the public
reversal `τ(y,z) = (y, 1 ⊕ rev z)`. -/
theorem causalEnc_comm (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (sj : D × (Fin (2 * ℓ) → Bool)) :
    causalEnc F h ℓ (rawRev jumpRev sj) = recRev jumpRev (causalEnc F h ℓ sj) := by
  simp only [causalEnc, rawRev, recRev, Prod.mk.injEq, true_and]
  funext i
  simp only [xorS, jumpRev, mask_rev]
  cases sj.2 (Fin.rev i) <;> cases mask (genBits F h ℓ sj.1) i <;> rfl

/-- The causal record law. -/
noncomputable def causalLaw (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (P0 : (Fin (2 * ℓ) → Bool) → ℝ) :
    D × (Fin (2 * ℓ) → Bool) → ℝ :=
  push (causalEnc F h ℓ) (prodLaw (unif D) P0)

/-- `Q_c = τ_* P_c`. -/
theorem causalLaw_reverse (F : D ≃ D) (h : D → Bool) (ℓ : ℕ) (P0 : (Fin (2 * ℓ) → Bool) → ℝ) :
    causalLaw F h ℓ (fun x => P0 (jumpRev x)) = fun r => causalLaw F h ℓ P0 (recRev jumpRev r) := by
  funext r
  unfold causalLaw
  rw [show causalEnc F h ℓ = causalEncEquiv F h ℓ from rfl, push_equiv, push_equiv]
  have key : (causalEncEquiv F h ℓ).symm (recRev jumpRev r) =
      rawRev jumpRev ((causalEncEquiv F h ℓ).symm r) := by
    apply (causalEncEquiv F h ℓ).injective
    rw [Equiv.apply_symm_apply]
    change recRev jumpRev r = causalEnc F h ℓ (rawRev jumpRev ((causalEncEquiv F h ℓ).symm r))
    rw [causalEnc_comm]
    change recRev jumpRev r =
      recRev jumpRev ((causalEncEquiv F h ℓ) ((causalEncEquiv F h ℓ).symm r))
    rw [Equiv.apply_symm_apply]
  beta_reduce
  rw [key]
  rfl

/-- The reduction from the causal record to the generator experiment: on `(y, K)`, sample
`J ∼ P⁰` and output `(y, J ⊕ M(K))`. -/
def causalRed {ℓ : ℕ} (P0 : (Fin (2 * ℓ) → Bool) → ℝ) (A : D × (Fin (2 * ℓ) → Bool) → ℝ) :
    D × (Fin ℓ → Bool) → ℝ :=
  fun yK => ∑ j, P0 j * A (yK.1, xorS j (mask yK.2))

omit [Fintype D] [DecidableEq D] in
lemma causalRed_isTest {ℓ : ℕ} {P0 : (Fin (2 * ℓ) → Bool) → ℝ} (hP0 : IsProb P0)
    {A : D × (Fin (2 * ℓ) → Bool) → ℝ} (hA : IsTest A) : IsTest (causalRed P0 A) := by
  intro yK
  unfold causalRed
  constructor
  · exact sum_nonneg fun x _ => mul_nonneg (hP0.nonneg x) (hA _).1
  · calc _ ≤ ∑ x, P0 x * 1 := sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hA _).2
          (hP0.nonneg x)
      _ = 1 := by simp [hP0.sum_one]

lemma expect_genReal_causalRed (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    (P0 : (Fin (2 * ℓ) → Bool) → ℝ) (A : D × (Fin (2 * ℓ) → Bool) → ℝ) :
    expect (genReal F h ℓ) (causalRed P0 A) = expect (causalLaw F h ℓ P0) A := by
  unfold genReal causalLaw
  rw [expect_push, expect_push, expect_prodLaw]
  rfl

/-- The mask re-indexing used for the ideal symmetry. -/
def maskFlip {ℓ : ℕ} (j : Fin (2 * ℓ) → Bool) (K : Fin ℓ → Bool) : Fin ℓ → Bool :=
  fun k => !(xor (xor (j (emb k)) (j (Fin.rev (emb k)))) (K k))

lemma maskFlip_involutive {ℓ : ℕ} (j : Fin (2 * ℓ) → Bool) :
    Function.Involutive (maskFlip j) := by
  intro K; funext k; simp only [maskFlip]
  cases j (emb k) <;> cases j (Fin.rev (emb k)) <;> cases K k <;> rfl

/-- Key identity: reversal followed by an ideal mask equals the original string with a
re-indexed mask, `θ(j) ⊕ M(K) = j ⊕ M(φ_j K)`. -/
lemma jumpRev_xor_mask {ℓ : ℕ} (j : Fin (2 * ℓ) → Bool) (K : Fin ℓ → Bool) :
    xorS (jumpRev j) (mask K) = xorS j (mask (maskFlip j K)) := by
  funext i
  simp only [xorS, jumpRev, mask, maskFlip]
  have hpair : xor (j (emb (fold i))) (j (Fin.rev (emb (fold i)))) = xor (j i) (j (Fin.rev i)) := by
    rcases emb_fold i with h | h
    · rw [h]
    · rw [h, Fin.rev_rev, Bool.xor_comm]
  rw [hpair]
  cases j i <;> cases j (Fin.rev i) <;> cases K (fold i) <;> rfl

omit [DecidableEq D] in
/-- **Ideal symmetry (proof of Theorem `thm:causal`)**: with an independent uniform endpoint and
uniform mask, the forward and reversed ideal laws coincide exactly, for any direction law. -/
lemma expect_genIdeal_causalRed {ℓ : ℕ} (P0 : (Fin (2 * ℓ) → Bool) → ℝ)
    (A : D × (Fin (2 * ℓ) → Bool) → ℝ) :
    expect (genIdeal (D := D) ℓ) (causalRed P0 A) =
      expect (genIdeal (D := D) ℓ) (causalRed (fun x => P0 (jumpRev x)) A) := by
  unfold genIdeal
  rw [expect_prodLaw, expect_prodLaw]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  unfold causalRed
  simp only [mul_sum]
  rw [sum_comm, sum_comm (f := fun K x => unif (Fin ℓ → Bool) K * (P0 (jumpRev x) * _))]
  symm
  calc ∑ x, ∑ K, unif (Fin ℓ → Bool) K * (P0 (jumpRev x) * A (y, xorS x (mask K)))
      = ∑ x, ∑ K, unif (Fin ℓ → Bool) K * (P0 x * A (y, xorS (jumpRev x) (mask K))) :=
        Fintype.sum_equiv (Function.Involutive.toPerm _ (jumpRev_involutive (2 * ℓ))) _ _
          (fun x => by simp [jumpRev_involutive (2 * ℓ) x])
    _ = ∑ x, ∑ K, unif (Fin ℓ → Bool) K * (P0 x * A (y, xorS x (mask K))) :=
        sum_congr rfl fun x _ => by
          simp_rw [jumpRev_xor_mask]
          exact Fintype.sum_equiv (Function.Involutive.toPerm _ (maskFlip_involutive x)) _ _
            (fun K => by simp [unif])

/-- **Theorem `thm:causal` (causal, information-preserving concealment).** For every direction
law `P⁰` on `{0,1}^{2ℓ}` and `Q⁰ = θ_* P⁰`:
* the causal encoder preserves KL divergence and total variation;
* the reversed record law is the forward one composed with `τ`;
* if the hard-core class `TH` has advantage at most `e` and the generator hybrids of the
  reductions of every record test lie in `TH`, every record test has advantage at most
  `2ℓ e` (Eq. (causaladv)). -/
theorem causal_concealment [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    {P0 : (Fin (2 * ℓ) → Bool) → ℝ} (hP0 : IsProb P0) :
    KL (causalLaw F h ℓ P0) (causalLaw F h ℓ (fun x => P0 (jumpRev x))) =
      KL P0 (fun x => P0 (jumpRev x)) ∧
    TV (causalLaw F h ℓ P0) (causalLaw F h ℓ (fun x => P0 (jumpRev x))) =
      TV P0 (fun x => P0 (jumpRev x)) ∧
    causalLaw F h ℓ (fun x => P0 (jumpRev x)) =
      (fun r => causalLaw F h ℓ P0 (recRev jumpRev r)) ∧
    ∀ (TR : Set (D × (Fin (2 * ℓ) → Bool) → ℝ)) (TH : Set (D × Bool → ℝ)) (e : ℝ),
      AdvLE TH (hcReal F h) (hcIdeal F) e →
      (∀ A ∈ TR, ∀ i < ℓ, genRed F h ℓ i (causalRed P0 A) ∈ TH ∧
        genRed F h ℓ i (causalRed (fun x => P0 (jumpRev x)) A) ∈ TH) →
      AdvLE TR (causalLaw F h ℓ P0) (causalLaw F h ℓ (fun x => P0 (jumpRev x))) (2 * ℓ * e) := by
  have hE : causalEnc F h ℓ = causalEncEquiv F h ℓ := rfl
  have hQ0 : IsProb (fun x => P0 (jumpRev x)) :=
    ⟨fun x => hP0.nonneg _, by
      rw [Fintype.sum_equiv (Function.Involutive.toPerm _ (jumpRev_involutive (2 * ℓ)))
        (fun x => P0 (jumpRev x)) P0 (fun x => rfl), hP0.sum_one]⟩
  refine ⟨?_, ?_, causalLaw_reverse F h ℓ P0, ?_⟩
  · unfold causalLaw; rw [hE, KL_push_equiv, KL_prodLaw_left unif_isProb]
  · unfold causalLaw; rw [hE, TV_push_equiv, TV_prodLaw_left unif_isProb]
  · intro TR TH e hhc hred A hA hAt
    have g1 := generator_bound F h ℓ {B | ∀ i < ℓ, genRed F h ℓ i B ∈ TH} TH e hhc
      (fun B hB i hi => hB i hi) (causalRed P0 A) (fun i hi => (hred A hA i hi).1)
      (causalRed_isTest hP0 hAt)
    have g2 := generator_bound F h ℓ {B | ∀ i < ℓ, genRed F h ℓ i B ∈ TH} TH e hhc
      (fun B hB i hi => hB i hi) (causalRed (fun x => P0 (jumpRev x)) A)
      (fun i hi => (hred A hA i hi).2) (causalRed_isTest hQ0 hAt)
    unfold adv at g1 g2 ⊢
    rw [expect_genReal_causalRed] at g1 g2
    rw [expect_genIdeal_causalRed] at g1
    have := abs_sub_le (expect (causalLaw F h ℓ P0) A)
      (expect (genIdeal ℓ) (causalRed (fun x => P0 (jumpRev x)) A))
      (expect (causalLaw F h ℓ (fun x => P0 (jumpRev x))) A)
    rw [abs_sub_comm (expect (genIdeal ℓ) _) _] at this
    linarith

/-- **Eq. (pairideal)**: for i.i.d. `Ber(p)` directions, a mirror pair masked by the same fair
bit has `P(00) = P(11) = (p² + (1-p)²)/2` and `P(01) = P(10) = p(1-p)`. -/
theorem masked_pair_ideal (p : ℝ) (x y : Bool) :
    (1 / 2) * ∑ c : Bool, bern p (xor x c) * bern p (xor y c) =
      if x = y then (p ^ 2 + (1 - p) ^ 2) / 2 else p * (1 - p) := by
  cases x <;> cases y <;> simp [bern] <;> ring

end Arrow

end CausalPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Samples
    ════════════════════════════════════════════════════════════════════ -/

section SamplesPart

/-!
# Section 8: repeated observations, training and leakage

* Proposition `prop:many` (Eq. (many)) for the one-bit and the causal constructions, and
  preservation of negligibility for polynomially many records.
* The statistical evidence of independent records adds up (`D(P^{⊗q}‖Q^{⊗q}) = q D(P‖Q)`).
* Seed reuse in the one-bit construction: an efficient two-record attack with both orientation
  errors at most `2 P(K ≤ m/2) ≤ 2 e^{-2m(p-1/2)²}`.
* Mask reuse in the causal construction: coordinatewise majority vote recovers the mask with
  failure probability at most `ℓ e^{-2q(p-1/2)²}` (Eq. (reuse)), and the exact success
  probability `[1 - P(Bin(q,p) ≤ (q-1)/2)]^ℓ` (Eq. (reuseexact)).
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ### Proposition `prop:many` -/

/-- **Proposition `prop:many`, one-bit construction** (Eq. (many)): with fresh seeds,
`q` independent encoded records are `2qe`-indistinguishable, provided the embedded single-record
tests of the `q`-record class lie in the single-record class `T₁` and their reductions lie in
the hard-core class `TH`. -/
theorem many_records_onebit [Nonempty D] {X : Type*} [Fintype X] [DecidableEq X] (F : D ≃ D)
    (h : D → Bool) {θ : X → X} (hθ : Function.Involutive θ) {P0 : X → ℝ} (hP0 : IsProb P0)
    (q : ℕ) (Tq : Set ((Fin q → D × X) → ℝ)) (T₁ : Set (D × X → ℝ)) (TH : Set (D × Bool → ℝ))
    (e : ℝ) (hhc : AdvLE TH (hcReal F h) (hcIdeal F) e)
    (hred : ∀ A ∈ T₁, redTest θ P0 A ∈ TH ∧ redTest θ (fun x => P0 (θ x)) A ∈ TH)
    (hclos : ∀ A ∈ Tq, ∀ i : Fin q, embedTest i (hybridW i (encLaw F h θ P0)
      (encLaw F h θ (fun x => P0 (θ x)))) A ∈ T₁) :
    AdvLE Tq (iidLaw q (encLaw F h θ P0)) (iidLaw q (encLaw F h θ (fun x => P0 (θ x))))
      (q * (2 * e)) := by
  have hQ0 : IsProb (fun x => P0 (θ x)) :=
    ⟨fun x => hP0.nonneg _, by
      rw [Fintype.sum_equiv (Function.Involutive.toPerm θ hθ) (fun x => P0 (θ x)) P0
        (fun x => rfl), hP0.sum_one]⟩
  exact advLE_iid (encLaw_isProb F h θ hP0) (encLaw_isProb F h θ hQ0) Tq T₁
    ((universal_concealment F h hθ hP0).2.2 T₁ TH e hhc hred) hclos

/-- **Proposition `prop:many`, causal construction**: the bound is `2qℓe`. -/
theorem many_records_causal [Nonempty D] (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    {P0 : (Fin (2 * ℓ) → Bool) → ℝ} (hP0 : IsProb P0) (q : ℕ)
    (Tq : Set ((Fin q → D × (Fin (2 * ℓ) → Bool)) → ℝ)) (T₁ : Set (D × (Fin (2 * ℓ) → Bool) → ℝ))
    (TH : Set (D × Bool → ℝ)) (e : ℝ) (hhc : AdvLE TH (hcReal F h) (hcIdeal F) e)
    (hred : ∀ A ∈ T₁, ∀ i < ℓ, genRed F h ℓ i (causalRed P0 A) ∈ TH ∧
        genRed F h ℓ i (causalRed (fun x => P0 (jumpRev x)) A) ∈ TH)
    (hclos : ∀ A ∈ Tq, ∀ i : Fin q, embedTest i (hybridW i (causalLaw F h ℓ P0)
      (causalLaw F h ℓ (fun x => P0 (jumpRev x)))) A ∈ T₁) :
    AdvLE Tq (iidLaw q (causalLaw F h ℓ P0)) (iidLaw q (causalLaw F h ℓ (fun x => P0 (jumpRev x))))
      (q * (2 * ℓ * e)) := by
  have hQ0 : IsProb (fun x => P0 (jumpRev x)) :=
    ⟨fun x => hP0.nonneg _, by
      rw [Fintype.sum_equiv (Function.Involutive.toPerm _ (jumpRev_involutive (2 * ℓ)))
        (fun x => P0 (jumpRev x)) P0 (fun x => rfl), hP0.sum_one]⟩
  exact advLE_iid ((prodLaw_isProb unif_isProb hP0).push _)
    ((prodLaw_isProb unif_isProb hQ0).push _) Tq T₁
    ((causal_concealment F h ℓ hP0).2.2.2 T₁ TH e hhc hred) hclos

/-- Every polynomial number of records preserves computational indistinguishability:
`q(n) · 2 ε(n)` is negligible when `q` is polynomially bounded and `ε` is negligible. -/
theorem many_records_negligible {q : ℕ → ℕ} (hq : PolySize q) {ε : ℕ → ℝ} (hε : Negligible ε) :
    Negligible (fun n => (q n : ℝ) * (2 * ε n)) :=
  (hε.const_mul 2).mul_poly hq

/-! ### Seed reuse in the one-bit construction -/

omit [Fintype D] [DecidableEq D] in
lemma expect_prodLaw_comp {X : Type*} [Fintype X] {P0 : X → ℝ} {φ ψ : X → X}
    (hφ : Function.Involutive φ) (hψ : Function.Involutive ψ) (A : X × X → ℝ) :
    expect (prodLaw (fun x => P0 (φ x)) (fun x => P0 (ψ x))) A =
      expect (prodLaw P0 P0) (fun z => A (φ z.1, ψ z.2)) := by
  rw [expect_prodLaw, expect_prodLaw]
  refine Fintype.sum_equiv (Function.Involutive.toPerm φ hφ) _ _ (fun x => ?_)
  simp only [Function.Involutive.coe_toPerm, hφ x]
  congr 1
  exact Fintype.sum_equiv (Function.Involutive.toPerm ψ hψ) _ _ (fun y => by simp [hψ y])

lemma ones_thetaPow {m : ℕ} (b : Bool) (x : Fin m → Bool) :
    ones (thetaPow jumpRev b x) = if b then m - ones x else ones x := by
  cases b
  · rfl
  · have := ones_jumpRev x; simp only [thetaPow, if_true]; omega

lemma lowerTail_le_hoeffding {p : ℝ} (hp : 1 / 2 ≤ p) (h1 : p < 1) (m : ℕ) :
    lowerTail m p ≤ Real.exp (-2 * m * (p - 1 / 2) ^ 2) := by
  calc lowerTail m p ≤ (2 * Real.sqrt (p * (1 - p))) ^ m := lowerTail_le_chernoff hp h1 m
    _ ≤ Real.exp (-2 * (p - 1 / 2) ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) (two_sqrt_le_exp (by linarith) h1.le) m
    _ = Real.exp (-2 * m * (p - 1 / 2) ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf

lemma reuse_pt1 {m a c : ℕ} (ha : a ≤ m) (hc : c ≤ m) (b : Bool) :
    1 - ((if 2 * a ≤ m then (1 : ℝ) else 0) + (if 2 * c ≤ m then 1 else 0)) ≤
      (if (m < 2 * (if b = true then m - a else a) ↔ m < 2 * (if b = true then m - c else c))
        then (1 : ℝ) else 0) := by
  cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
    split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma reuse_pt2 {m a c : ℕ} (ha : a ≤ m) (hc : c ≤ m) (b : Bool) :
    (if (m < 2 * (if b = true then m - a else a) ↔
        m < 2 * (m - (if b = true then m - c else c))) then (1 : ℝ) else 0) ≤
      ((if 2 * a ≤ m then (1 : ℝ) else 0) + (if 2 * c ≤ m then 1 else 0)) := by
  cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
    split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- The seed-reuse attack: declare "same orientation as the labelled forward record" iff the
two visible currents have the same sign. -/
def reuseTest {m : ℕ} (z : (Fin m → Bool) × (Fin m → Bool)) : ℝ :=
  if (m < 2 * ones z.1 ↔ m < 2 * ones z.2) then 1 else 0

/-- **Seed reuse (one-bit construction).** If two blocks share the seed (masking bit `b`), the
first being known to be forward, the efficient test `reuseTest` accepts with probability at
least `1 - 2 P(K ≤ m/2)` when the second block is forward and at most `2 P(K ≤ m/2)` when it is
reversed, for either value of `b`; hence both orientation errors are at most
`2 P(K ≤ m/2) ≤ 2 e^{-2m(p-1/2)²}`. (The paper states the bound with `e_m(p)`; the deterministic
threshold test used here gives the stated `P(K ≤ m/2)` version.) -/
theorem seed_reuse_attack {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (b : Bool) :
    1 - 2 * lowerTail m p ≤
      expect (prodLaw (fun x => bernProd p m (thetaPow jumpRev b x))
        (fun x => bernProd p m (thetaPow jumpRev b x))) reuseTest ∧
    expect (prodLaw (fun x => bernProd p m (thetaPow jumpRev b x))
        (fun x => bernProd p m (jumpRev (thetaPow jumpRev b x)))) reuseTest ≤
      2 * lowerTail m p ∧
    2 * lowerTail m p ≤ 2 * Real.exp (-2 * m * (p - 1 / 2) ^ 2) := by
  have hP := bernProd_isProb (by linarith) hp1.le m
  have hinv := thetaPow_involutive (jumpRev_involutive m) b
  have hinv2 : Function.Involutive (fun x : Fin m → Bool => jumpRev (thetaPow jumpRev b x)) := by
    intro x
    cases b
    · exact jumpRev_involutive m x
    · simp [thetaPow, jumpRev_involutive m x]
  set g : (Fin m → Bool) → ℝ := fun x => if 2 * ones x ≤ m then 1 else 0
  have hg : expect (bernProd p m) g = lowerTail m p := rfl
  have hsum : expect (prodLaw (bernProd p m) (bernProd p m)) (fun z => g z.1 + g z.2) =
      2 * lowerTail m p := by
    rw [expect_add, expect_prodLaw, expect_prodLaw]
    simp only [← sum_mul, hP.sum_one, one_mul]
    change expect (bernProd p m) g + expect (bernProd p m) g = _
    rw [hg]; ring
  have hone : expect (prodLaw (bernProd p m) (bernProd p m)) (fun _ => (1 : ℝ)) = 1 :=
    expect_const _ (prodLaw_isProb hP hP) 1
  refine ⟨?_, ?_, by linarith [lowerTail_le_hoeffding hp hp1 m]⟩
  · rw [expect_prodLaw_comp hinv hinv]
    have hpt : ∀ z : (Fin m → Bool) × (Fin m → Bool),
        1 - (g z.1 + g z.2) ≤ reuseTest (thetaPow jumpRev b z.1, thetaPow jumpRev b z.2) := by
      intro z
      have h1 := ones_jumpRev z.1; have h2 := ones_jumpRev z.2
      simp only [g, reuseTest, ones_thetaPow]
      exact reuse_pt1 (by omega) (by omega) b
    have := expect_mono (prodLaw_isProb hP hP).nonneg hpt
    have e1 : expect (prodLaw (bernProd p m) (bernProd p m)) (fun z => 1 - (g z.1 + g z.2)) =
        1 - 2 * lowerTail m p := by
      have hlin := expect_add (prodLaw (bernProd p m) (bernProd p m)) (fun _ => (1 : ℝ))
        (fun z => -(g z.1 + g z.2))
      have hneg : expect (prodLaw (bernProd p m) (bernProd p m)) (fun z => -(g z.1 + g z.2)) =
          -(2 * lowerTail m p) := by
        rw [← hsum]; unfold expect; rw [← sum_neg_distrib]
        exact sum_congr rfl fun z _ => by ring
      rw [show (fun z : (Fin m → Bool) × (Fin m → Bool) => 1 - (g z.1 + g z.2)) =
        fun z => 1 + -(g z.1 + g z.2) by funext z; ring, hlin, hone, hneg]
      ring
    linarith
  · rw [expect_prodLaw_comp hinv hinv2]
    have hpt : ∀ z : (Fin m → Bool) × (Fin m → Bool),
        reuseTest (thetaPow jumpRev b z.1, jumpRev (thetaPow jumpRev b z.2)) ≤ g z.1 + g z.2 := by
      intro z
      have h1 := ones_jumpRev z.1; have h2 := ones_jumpRev z.2
      have h3 := ones_jumpRev (thetaPow jumpRev b z.2)
      simp only [g, reuseTest]
      rw [show ones (jumpRev (thetaPow jumpRev b z.2)) = m - ones (thetaPow jumpRev b z.2) by
        omega, ones_thetaPow, ones_thetaPow]
      exact reuse_pt2 (by omega) (by omega) b
    have := expect_mono (prodLaw_isProb hP hP).nonneg hpt
    linarith

/-! ### Mask reuse in the causal construction -/

/-- Observed bits at the used positions of `q` labelled forward blocks sharing the mask `K`:
for each mirror-pair index `k` and block `t`, the raw direction `X k t` XOR the mask bit `K k`. -/
def maskObs {ℓ q : ℕ} (K : Fin ℓ → Bool) (X : Fin ℓ → Fin q → Bool) : Fin ℓ → Fin q → Bool :=
  fun k t => xor (X k t) (K k)

/-- Coordinatewise majority-vote estimate of the mask (directions are biased towards `1`). -/
def maskEst {ℓ q : ℕ} (Z : Fin ℓ → Fin q → Bool) : Fin ℓ → Bool :=
  fun k => !(decide (q < 2 * ones (Z k)))

lemma ones_xor_true {q : ℕ} (c : Fin q → Bool) :
    ones (fun t => xor (c t) true) + ones c = q := by
  unfold ones
  rw [← sum_add_distrib]
  have : ∀ b : Bool, (!b).toNat + b.toNat = 1 := by decide
  simp [this]

lemma maskEst_correct {ℓ q : ℕ} (hq : Odd q) (K : Fin ℓ → Bool) (X : Fin ℓ → Fin q → Bool)
    (k : Fin ℓ) : maskEst (maskObs K X) k = K k ↔ q < 2 * ones (X k) := by
  obtain ⟨r, hr⟩ := hq
  unfold maskEst maskObs
  cases hK : K k
  · simp
  · have := ones_xor_true (X k)
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    constructor <;> intro h <;> omega

/-- **Mask reuse, exact formula** (Eq. (reuseexact)): with `q` odd, majority vote recovers the
entire mask with probability exactly `[1 - P(Bin(q,p) ≤ (q-1)/2)]^ℓ`. -/
theorem mask_recovery_exact {ℓ q : ℕ} (hq : Odd q) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K : Fin ℓ → Bool) :
    expect (iidLaw ℓ (bernProd p q))
      (fun X => if maskEst (maskObs K X) = K then 1 else 0) = (1 - lowerTail q p) ^ ℓ := by
  have hpt : ∀ X : Fin ℓ → Fin q → Bool, (if maskEst (maskObs K X) = K then (1 : ℝ) else 0) =
      ∏ k, (if q < 2 * ones (X k) then 1 else 0) := by
    intro X
    by_cases hall : ∀ k, q < 2 * ones (X k)
    · rw [if_pos (funext fun k => (maskEst_correct hq K X k).mpr (hall k))]
      exact (prod_eq_one fun k _ => if_pos (hall k)).symm
    · push_neg at hall
      obtain ⟨k, hk⟩ := hall
      rw [if_neg (fun h => absurd ((maskEst_correct hq K X k).mp (congrFun h k)) (by omega))]
      exact (prod_eq_zero (mem_univ k) (if_neg (by omega))).symm
  unfold expect iidLaw piLaw
  simp_rw [hpt, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun (_ : Fin ℓ) (c : Fin q → Bool) =>
    bernProd p q c * (if q < 2 * ones c then 1 else 0))]
  rw [prod_const, card_univ, Fintype.card_fin]
  congr 1
  unfold lowerTail binExp
  rw [eq_sub_iff_add_eq, ← sum_add_distrib]
  trans ∑ c, bernProd p q c
  · refine sum_congr rfl fun c _ => ?_
    dsimp only
    split_ifs <;> first | (exfalso; omega) | ring
  · exact (bernProd_isProb h0 h1 q).sum_one

/-- **Eq. (reuse)**: majority vote over `q` (odd) labelled blocks sharing a mask fails to
recover the mask with probability at most `ℓ e^{-2q(p-1/2)²}`; `q = O(log ℓ)` repetitions
suffice. -/
theorem mask_recovery_failure {ℓ q : ℕ} (hq : Odd q) {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1)
    (K : Fin ℓ → Bool) :
    expect (iidLaw ℓ (bernProd p q))
      (fun X => if maskEst (maskObs K X) = K then 0 else 1) ≤
      ℓ * Real.exp (-2 * q * (p - 1 / 2) ^ 2) := by
  have hP : IsProb (iidLaw ℓ (bernProd p q)) :=
    piLaw_isProb fun _ => bernProd_isProb (by linarith) hp1.le q
  have e : expect (iidLaw ℓ (bernProd p q)) (fun X => if maskEst (maskObs K X) = K then 0 else 1)
      = 1 - (1 - lowerTail q p) ^ ℓ := by
    calc _ = ∑ X, iidLaw ℓ (bernProd p q) X - ∑ X, iidLaw ℓ (bernProd p q) X *
          (if maskEst (maskObs K X) = K then 1 else 0) := by
          unfold expect; rw [← sum_sub_distrib]
          refine sum_congr rfl fun X _ => ?_
          by_cases hX : maskEst (maskObs K X) = K <;> simp [hX]
      _ = _ := by
          rw [hP.sum_one]; congr 1
          exact mask_recovery_exact hq (by linarith) hp1.le K
  rw [e]
  have hβ0 : 0 ≤ lowerTail q p := by
    unfold lowerTail binExp
    exact sum_nonneg fun c _ => mul_nonneg ((bernProd_isProb (by linarith) hp1.le q).nonneg c)
      (by dsimp only; split_ifs <;> norm_num)
  have hβ := lowerTail_le_hoeffding hp hp1 q
  have hbern := one_add_mul_le_pow (a := -lowerTail q p) (by
    have : lowerTail q p ≤ 1 := hβ.trans (by
      rw [Real.exp_le_one_iff]; nlinarith)
    linarith) ℓ
  have : 1 - (1 - lowerTail q p) ^ ℓ ≤ ℓ * lowerTail q p := by
    rw [sub_eq_add_neg 1 (lowerTail q p)]; linarith
  calc 1 - (1 - lowerTail q p) ^ ℓ ≤ ℓ * lowerTail q p := this
    _ ≤ ℓ * Real.exp (-2 * q * (p - 1 / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg _)

end Arrow

end SamplesPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Witness
    ════════════════════════════════════════════════════════════════════ -/

section WitnessPart

/-!
# Section 9: limits on efficient entropy-production witnesses

* The restricted variational divergence `D^var_{s,B}` (Eq. (restrictedDV)) over a score class.
* **Proposition `prop:dv`** (Eq. (dvbound)): `0 ≤ D^var ≤ 2B · Adv`, and the negligible corollary.
* The ring likelihood score lies in the polynomial range `[-am, am]`.
* **Corollary `cor:estimator`**: an accurate efficient signed estimator would yield a sign test
  with advantage `1 - o(1)`, contradicting computational concealment.
-/


open Finset Real Filter

namespace Arrow

variable {α : Type*} [Fintype α]

/-! ### The restricted variational divergence -/

/-- **Eq. (restrictedDV)**: the restricted Donsker–Varadhan divergence over a score class `S`. -/
noncomputable def restrictedDV (P Q : α → ℝ) (S : Set (α → ℝ)) : ℝ := sSup (dvObj P Q '' S)

/-- The randomized test associated with a score of range `[-B, B]`: accept with probability
`(f + B)/(2B)`. -/
noncomputable def scoreTest (B : ℝ) (f : α → ℝ) : α → ℝ := fun x => (f x + B) / (2 * B)

omit [Fintype α] in
lemma scoreTest_isTest {B : ℝ} (hB : 0 < B) {f : α → ℝ} (hf : ∀ x, |f x| ≤ B) :
    IsTest (scoreTest B f) := by
  intro x
  have := abs_le.mp (hf x)
  unfold scoreTest
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_le_one (by linarith)]; linarith

lemma expect_scoreTest {P : α → ℝ} (hP : IsProb P) (B : ℝ) (f : α → ℝ) :
    expect P (scoreTest B f) = (expect P f + B) / (2 * B) := by
  unfold expect scoreTest
  calc ∑ x, P x * ((f x + B) / (2 * B)) = ∑ x, (P x * f x + P x * B) / (2 * B) :=
        sum_congr rfl fun x _ => by ring
    _ = _ := by rw [← sum_div, sum_add_distrib, ← sum_mul, hP.sum_one, one_mul]

/-- The objective of a bounded score is at most `2B` times the acceptance-probability difference
of its randomized test (Jensen's inequality `log E_Q e^f ≥ E_Q f`). -/
theorem dvObj_le_scoreTest {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) {B : ℝ} (hB : 0 < B)
    (f : α → ℝ) :
    dvObj P Q f ≤ 2 * B * (expect P (scoreTest B f) - expect Q (scoreTest B f)) := by
  have hJ := expect_le_log_expect_exp hQ f
  rw [expect_scoreTest hP, expect_scoreTest hQ]
  unfold dvObj
  rw [show 2 * B * ((expect P f + B) / (2 * B) - (expect Q f + B) / (2 * B)) =
    expect P f - expect Q f by field_simp; ring]
  linarith

lemma dvObj_zero {P Q : α → ℝ} (hQ : IsProb Q) : dvObj P Q (fun _ => 0) = 0 := by
  unfold dvObj
  simp only [Real.exp_zero]
  rw [expect_const _ hQ 1, Real.log_one]
  simp [expect]

/-- **Proposition `prop:dv`** (Eq. (dvbound)). Let `S` be a score class containing the zero score
whose scores take values in `[-B, B]`, and whose associated randomized tests `(f+B)/(2B)` lie
in the test class `T` (the paper's `s + c_B` circuits). If every test of `T` has advantage at
most `b`, then `0 ≤ D^var_S(P‖Q) ≤ 2 B b`. -/
theorem restricted_dv_bound {P Q : α → ℝ} (hP : IsProb P) (hQ : IsProb Q) (S : Set (α → ℝ))
    (T : Set (α → ℝ)) {B : ℝ} (hB : 0 < B) (h0 : (fun _ => (0 : ℝ)) ∈ S)
    (hbd : ∀ f ∈ S, ∀ x, |f x| ≤ B) (hT : ∀ f ∈ S, scoreTest B f ∈ T) {b : ℝ}
    (hadv : AdvLE T P Q b) :
    0 ≤ restrictedDV P Q S ∧ restrictedDV P Q S ≤ 2 * B * b := by
  have hub : ∀ y ∈ dvObj P Q '' S, y ≤ 2 * B * b := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 := dvObj_le_scoreTest hP hQ hB f
    have h2 := hadv _ (hT f hf) (scoreTest_isTest hB (hbd f hf))
    unfold adv at h2
    have h3 := le_abs_self (expect P (scoreTest B f) - expect Q (scoreTest B f))
    nlinarith
  have hne : (dvObj P Q '' S).Nonempty := ⟨_, Set.mem_image_of_mem _ h0⟩
  refine ⟨?_, csSup_le hne hub⟩
  rw [← dvObj_zero (P := P) hQ]
  exact le_csSup ⟨_, hub⟩ (Set.mem_image_of_mem _ h0)

/-- A quantity squeezed between `0` and `2 B(n) b(n)` with `B` polynomially bounded and `b`
negligible is negligible. -/
lemma negligible_of_bound {Dv B b : ℕ → ℝ} (h0 : ∀ n, 0 ≤ Dv n) (h : ∀ n, Dv n ≤ 2 * B n * b n)
    (hB : PolyBounded B) (hb : Negligible b) : Negligible Dv := by
  refine ((hb.const_mul 2).mul_poly hB).mono (Eventually.of_forall fun n => ?_)
  rw [abs_of_nonneg (h0 n)]
  calc Dv n ≤ 2 * B n * b n := h n
    _ = B n * (2 * b n) := by ring
    _ ≤ _ := le_abs_self _

/-- **Proposition `prop:dv`, asymptotic part**: for a family of laws whose test classes have
negligible advantage, and score classes with polynomial range `B(n)` whose randomized tests lie
in those test classes, the restricted variational divergence is negligible. -/
theorem restricted_dv_negligible (A : ℕ → Type*) [∀ n, Fintype (A n)] (P Q : ∀ n, A n → ℝ)
    (hP : ∀ n, IsProb (P n)) (hQ : ∀ n, IsProb (Q n)) (S T : ∀ n, Set (A n → ℝ))
    (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (hBpoly : PolyBounded B)
    (h0 : ∀ n, (fun _ => (0 : ℝ)) ∈ S n) (hbd : ∀ n, ∀ f ∈ S n, ∀ x, |f x| ≤ B n)
    (hT : ∀ n, ∀ f ∈ S n, scoreTest (B n) f ∈ T n) (ε : ℕ → ℝ) (hε : Negligible ε)
    (hadv : ∀ n, AdvLE (T n) (P n) (Q n) (ε n)) :
    Negligible (fun n => restrictedDV (P n) (Q n) (S n)) :=
  negligible_of_bound (fun n => (restricted_dv_bound (hP n) (hQ n) _ _ (hB n) (h0 n) (hbd n)
    (hT n) (hadv n)).1) (fun n => (restricted_dv_bound (hP n) (hQ n) _ _ (hB n) (h0 n) (hbd n)
    (hT n) (hadv n)).2) hBpoly hε

/-! ### The ring score range -/

variable {D : Type*} [Fintype D] [DecidableEq D]

lemma affinity_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1) : 0 ≤ affinity p := by
  unfold affinity
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]; linarith

lemma ones_le {m : ℕ} (x : Fin m → Bool) : ones x ≤ m := by
  have := ones_jumpRev x; omega

/-- For the ring, the true likelihood score already lies in the polynomial range `[-am, am]`. -/
theorem ring_score_range [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 ≤ p)
    (hp1 : p < 1) (m : ℕ) (r : D × (Fin m → Bool)) :
    |llr (ringP F h p m) (ringQ F h p m) r| ≤ affinity p * m := by
  obtain ⟨y, z⟩ := r
  rw [ring_encoded_llr F h (by linarith) hp1, abs_mul, abs_of_nonneg (affinity_nonneg hp hp1)]
  have hk := ones_le (thetaPow jumpRev (h (F.symm y)) z)
  have hk' : (ones (thetaPow jumpRev (h (F.symm y)) z) : ℝ) ≤ m := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ ones (thetaPow jumpRev (h (F.symm y)) z) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩)
    (affinity_nonneg hp hp1)

/-! ### Corollary `cor:estimator` -/

/-- Expectations of functions of the decoded count under the encoded ring law are binomial
expectations. -/
lemma expect_ringP_ones [Nonempty D] (F : D ≃ D) (h : D → Bool) (p : ℝ) (m : ℕ) (g : ℕ → ℝ) :
    expect (ringP F h p m) (fun r => g (ones (thetaPow jumpRev (h (F.symm r.1)) r.2))) =
      binExp p m g := by
  unfold ringP encLaw
  rw [expect_push, expect_prodLaw]
  simp only [encoder, Equiv.symm_apply_apply, thetaPow_involutive (jumpRev_involutive m) _ _]
  rw [← sum_mul, unif_isProb.sum_one, one_mul]
  rfl

/-- The encoded entropy production `ℓ_m` under `P_m` has the law of `a(2K - m)`,
`K ~ Bin(m, p)`. -/
lemma expect_ringP_llr [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) (G : ℝ → ℝ) :
    expect (ringP F h p m) (fun r => G (llr (ringP F h p m) (ringQ F h p m) r)) =
      binExp p m (fun k => G (affinity p * (2 * (k : ℝ) - m))) := by
  rw [← expect_ringP_ones F h p m]
  unfold expect
  refine sum_congr rfl fun r _ => ?_
  obtain ⟨y, z⟩ := r
  dsimp only
  rw [ring_encoded_llr F h hp0 hp1]

/-- Under the reversed law, `ℓ_m` has the law of `-ℓ_m` under the forward law. -/
lemma expect_ringQ_llr [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) (G : ℝ → ℝ) :
    expect (ringQ F h p m) (fun r => G (llr (ringP F h p m) (ringQ F h p m) r)) =
      expect (ringP F h p m) (fun r => G (-llr (ringP F h p m) (ringQ F h p m) r)) := by
  have hτ : Function.Involutive (recRev (D := D) (jumpRev (m := m))) := by
    intro r; simp [recRev, jumpRev_involutive m r.2]
  have hodd := (ring_encoded_fluctuations F h hp0 hp1 m).1
  conv_lhs => rw [ringQ_eq_comp F h p m]
  unfold expect
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ hτ) _ _ (fun r => ?_)
  simp only [Function.Involutive.coe_toPerm]
  rw [← ringQ_eq_comp F h p m, hodd, neg_neg]

/-- The sign test of an estimator: declare "forward" iff `σ̂ > 0`. -/
noncomputable def signTest {β : Type*} (σh : β → ℝ) : β → ℝ := fun r => if 0 < σh r then 1 else 0

lemma signTest_isTest {β : Type*} (σh : β → ℝ) : IsTest (signTest σh) := fun r => by
  unfold signTest; split_ifs <;> norm_num

/-- Indicator of an estimation error of size at least `c`. -/
noncomputable def errInd {β : Type*} (σh σ : β → ℝ) (c : ℝ) : β → ℝ :=
  fun r => if c ≤ |σh r - σ r| then 1 else 0

/-- General sign-test bound: if `σ̂` is within `c` of `σ` except on an error event, then the sign
test accepts under `P` with probability at least `1 - P(err) - P(σ ≤ c)` and under `Q` with
probability at most `Q(err) + Q(σ ≥ -c)`. -/
theorem sign_test_bound {β : Type*} [Fintype β] {P Q : β → ℝ} (hP : IsProb P) (hQ : IsProb Q)
    (σh σ : β → ℝ) (c : ℝ) :
    1 - expect P (errInd σh σ c) - expect P (fun r => if σ r ≤ c then 1 else 0) -
        (expect Q (errInd σh σ c) + expect Q (fun r => if -c ≤ σ r then 1 else 0)) ≤
      expect P (signTest σh) - expect Q (signTest σh) := by
  have h1 : ∀ r, 1 + (-errInd σh σ c r + -(if σ r ≤ c then (1 : ℝ) else 0)) ≤ signTest σh r := by
    intro r
    unfold errInd signTest
    by_cases ha : 0 < σh r
    · rw [if_pos ha]; split_ifs <;> norm_num
    · rw [if_neg ha]
      by_cases hb : c ≤ |σh r - σ r|
      · rw [if_pos hb]; split_ifs <;> norm_num
      · rw [if_neg hb]
        have : σ r ≤ c := by
          have := (abs_lt.mp (not_le.mp hb)); linarith
        rw [if_pos this]; norm_num
  have h2 : ∀ r, signTest σh r ≤ errInd σh σ c r + (if -c ≤ σ r then (1 : ℝ) else 0) := by
    intro r
    unfold errInd signTest
    by_cases ha : 0 < σh r
    · rw [if_pos ha]
      by_cases hb : c ≤ |σh r - σ r|
      · rw [if_pos hb]; split_ifs <;> norm_num
      · rw [if_neg hb]
        have : -c ≤ σ r := by
          have := (abs_lt.mp (not_le.mp hb)); linarith
        rw [if_pos this]; norm_num
    · rw [if_neg ha]; split_ifs <;> norm_num
  have e1 := expect_mono hP.nonneg h1
  have e2 := expect_mono hQ.nonneg h2
  rw [expect_add, expect_const _ hP, expect_add] at e1
  rw [expect_add] at e2
  have n1 : expect P (fun r => -errInd σh σ c r) = -expect P (errInd σh σ c) := by
    unfold expect; rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => by ring
  have n2 : expect P (fun r => -(if σ r ≤ c then (1 : ℝ) else 0)) =
      -expect P (fun r => if σ r ≤ c then 1 else 0) := by
    unfold expect; rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => by ring
  rw [n1, n2] at e1
  linarith

/-- Wrong-side probability of the ring entropy production at the threshold `m d(p)/2`
(Chebyshev): `P_m(ℓ_m ≤ m d(p)/2) ≤ 16 p(1-p)/(m (2p-1)²)`. -/
theorem ring_wrong_side [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 0 < m) :
    expect (ringP F h p m) (fun r => if llr (ringP F h p m) (ringQ F h p m) r ≤
      m * drate p / 2 then 1 else 0) ≤ 16 * (p * (1 - p)) / (m * (2 * p - 1) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < affinity p := by
    unfold affinity; apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
  rw [expect_ringP_llr F h hp0 hp1 m (fun u => if u ≤ m * drate p / 2 then 1 else 0)]
  have ht : 0 < (2 * p - 1) / 4 := by linarith
  calc _ ≤ binExp p m (fun k => if (k : ℝ) ≤ m * (p - (2 * p - 1) / 4) then 1 else 0) := by
        apply binExp_mono hp0.le hp1.le
        intro k
        dsimp only
        split_ifs with h1 h2 <;> try norm_num
        apply h2
        have : affinity p * (2 * (k : ℝ) - m) ≤ affinity p * (m * (2 * p - 1) / 2) := by
          unfold drate at h1; unfold affinity at *; nlinarith
        have := le_of_mul_le_mul_left this ha
        linarith
    _ ≤ p * (1 - p) / (m * ((2 * p - 1) / 4) ^ 2) := lowerTail_chebyshev hp0.le hp1.le hm ht
    _ = 16 * (p * (1 - p)) / (m * (2 * p - 1) ^ 2) := by
        rw [div_pow]; field_simp; ring

/-- **Corollary `cor:estimator` (finite form)**: for any estimator `σ̂` of the encoded entropy
production, the sign test `σ̂ > 0` has advantage at least
`1 - P_m(|σ̂ - ℓ_m| ≥ m d/2) - Q_m(|σ̂ - ℓ_m| ≥ m d/2) - 32 p(1-p)/(m(2p-1)²)`. -/
theorem ring_sign_test [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 0 < m) (σh : D × (Fin m → Bool) → ℝ) :
    1 - expect (ringP F h p m) (errInd σh (llr (ringP F h p m) (ringQ F h p m)) (m * drate p / 2))
      - expect (ringQ F h p m) (errInd σh (llr (ringP F h p m) (ringQ F h p m)) (m * drate p / 2))
      - 32 * (p * (1 - p)) / (m * (2 * p - 1) ^ 2) ≤
      adv (ringP F h p m) (ringQ F h p m) (signTest σh) := by
  have hp0 : 0 < p := by linarith
  have hP := encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m)
  have hQ := encLaw_isProb F h jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) m)
  have hb := sign_test_bound hP hQ σh (llr (ringP F h p m) (ringQ F h p m)) (m * drate p / 2)
  have hw := ring_wrong_side F h hp hp1 hm
  have hq : expect (ringQ F h p m) (fun r => if -(m * drate p / 2) ≤
      llr (ringP F h p m) (ringQ F h p m) r then 1 else 0) =
      expect (ringP F h p m) (fun r => if llr (ringP F h p m) (ringQ F h p m) r ≤
        m * drate p / 2 then 1 else 0) := by
    rw [expect_ringQ_llr F h hp0 hp1 m (fun u => if -(m * drate p / 2) ≤ u then 1 else 0)]
    unfold expect
    refine sum_congr rfl fun r _ => ?_
    simp only [neg_le_neg_iff]
  unfold ringP ringQ at hq hw hb
  unfold adv ringP ringQ
  rw [hq] at hb
  have := le_abs_self (expect (encLaw F h jumpRev (bernProd p m)) (signTest σh) -
    expect (encLaw F h jumpRev (bernProd (1 - p) m)) (signTest σh))
  have h32 : 32 * (p * (1 - p)) / (m * (2 * p - 1) ^ 2) =
      2 * (16 * (p * (1 - p)) / (m * (2 * p - 1) ^ 2)) := by ring
  linarith

/-- **Corollary `cor:estimator` (asymptotic form)**: there is no family of estimators
`σ̂_n` of the encoded ring entropy production (`m = n` jumps) that is accurate to additive `o(n)`
with probability `1 - o(1)` under both `P_n` and `Q_n`, if the associated sign tests belong to
classes whose advantage `ε(n)` tends to zero (as guaranteed by Theorem `thm:ring` under the
hard-core assumption). -/
theorem no_signed_estimator (Dn : ℕ → Type*) [∀ n, Fintype (Dn n)] [∀ n, DecidableEq (Dn n)]
    [∀ n, Nonempty (Dn n)] (F : ∀ n, Dn n ≃ Dn n) (h : ∀ n, Dn n → Bool) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p < 1) (σh : ∀ n, Dn n × (Fin n → Bool) → ℝ)
    (e η : ℕ → ℝ) (he : Tendsto (fun n => e n / n) atTop (nhds 0))
    (hη : Tendsto η atTop (nhds 0))
    (hacc : ∀ n, expect (ringP (F n) (h n) p n) (fun r =>
        if e n < |σh n r - llr (ringP (F n) (h n) p n) (ringQ (F n) (h n) p n) r| then 1 else 0)
          ≤ η n ∧
      expect (ringQ (F n) (h n) p n) (fun r =>
        if e n < |σh n r - llr (ringP (F n) (h n) p n) (ringQ (F n) (h n) p n) r| then 1 else 0)
          ≤ η n)
    (TR : ∀ n, Set (Dn n × (Fin n → Bool) → ℝ)) (hsign : ∀ n, signTest (σh n) ∈ TR n)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hconc : ∀ n, AdvLE (TR n) (ringP (F n) (h n) p n) (ringQ (F n) (h n) p n) (ε n)) :
    False := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < drate p := drate_pos hp0 hp1 (by linarith)
  set C := 32 * (p * (1 - p)) / (2 * p - 1) ^ 2
  have hC : Tendsto (fun n : ℕ => C / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, e n / n < drate p / 2 ∧ η n < 1 / 8 ∧ ε n < 1 / 8 ∧
      C / n < 1 / 8 ∧ 0 < n := by
    filter_upwards [(he.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < drate p / 2))),
      hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      hC.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      eventually_gt_atTop 0] with n h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨n, h1, h2, h3, h4, h5⟩ := hsmall.exists
  have hn : (0 : ℝ) < n := by exact_mod_cast h5
  have hen : e n < n * drate p / 2 := by
    rw [div_lt_iff₀ hn] at h1; linarith
  have hP := encLaw_isProb (F n) (h n) jumpRev (bernProd_isProb hp0.le hp1.le n)
  have hQ := encLaw_isProb (F n) (h n) jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) n)
  have hmono : ∀ r, errInd (σh n) (llr (ringP (F n) (h n) p n) (ringQ (F n) (h n) p n))
      (n * drate p / 2) r ≤ (if e n < |σh n r - llr (ringP (F n) (h n) p n)
        (ringQ (F n) (h n) p n) r| then 1 else 0) := by
    intro r; unfold errInd
    split_ifs with ha hb <;> first | (exfalso; linarith) | norm_num
  have eP := expect_mono hP.nonneg hmono
  have eQ := expect_mono hQ.nonneg hmono
  have hs := ring_sign_test (F n) (h n) hp hp1 h5 (σh n)
  have hadv := hconc n _ (hsign n) (signTest_isTest _)
  have hCn : 32 * (p * (1 - p)) / (n * (2 * p - 1) ^ 2) = C / n := by
    simp only [C]; field_simp
  rw [hCn] at hs
  unfold ringP ringQ at *
  linarith [(hacc n).1, (hacc n).2]

end Arrow

end WitnessPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Noise
    ════════════════════════════════════════════════════════════════════ -/

section NoisePart

/-!
# Section 10.1–10.2: payload noise and contamination

* The binary symmetric channel `B_η` on payload strings commutes with complementation-reversal and
  with XOR by a fixed mask, hence (endpoint received exactly) with both encoders.
* **Theorem `thm:payload`**: the noisy encoded ring laws are the encoded ring laws with
  `p_η = η + (1-2η)p`; `D = m d(p_η)`, `TV = 1 - 2 e_m(p_η)`; efficient advantage is preserved
  (Eq. (compdpi)).
* The noise loss `m[d(p) - d(p_η)] ≥ 0`, and the evidence vanishes at `η = 1/2`.
* The expansion `d(1/2+u) = 8u² + O(u⁴)` and Eq. (noisethreshold).
* **Proposition `prop:contamination`** for the ring with `ε_m = e^{-√m}`.
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ### The binary symmetric channel -/

/-- Binary symmetric channel on one bit. -/
def bsc (η : ℝ) : Bool → Bool → ℝ := fun b b' => if b' = b then 1 - η else η

/-- Independent binary symmetric noise on each payload bit. -/
def bscN (η : ℝ) {n : ℕ} : (Fin n → Bool) → (Fin n → Bool) → ℝ :=
  fun x y => ∏ i, bsc η (x i) (y i)

lemma bscN_isChannel {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (n : ℕ) :
    IsChannel (bscN η (n := n)) := by
  refine ⟨fun x y => prod_nonneg fun i _ => ?_, fun x => ?_⟩
  · unfold bsc; split_ifs <;> linarith
  · unfold bscN
    rw [← Fintype.prod_sum (f := fun i b => bsc η (x i) b)]
    refine prod_eq_one fun i _ => ?_
    cases x i <;> simp [bsc]

/-- **Bias renormalization**: `B_η` maps `Ber(p)^{⊗n}` to `Ber(p_η)^{⊗n}`, `p_η = η + (1-2η)p`
(Eq. (peta)). -/
theorem chan_bscN_bernProd (η p : ℝ) (n : ℕ) :
    chan (bscN η) (bernProd p n) = bernProd (η + (1 - 2 * η) * p) n := by
  funext y
  unfold chan bernProd iidLaw piLaw bscN
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun i b => bern p b * bsc η b (y i))]
  refine prod_congr rfl fun i _ => ?_
  cases y i <;> simp [bern, bsc] <;> ring

lemma bsc_not (η : ℝ) (a b : Bool) : bsc η (!a) (!b) = bsc η a b := by
  cases a <;> cases b <;> rfl

lemma bsc_xor (η : ℝ) (a b c : Bool) : bsc η (xor a c) (xor b c) = bsc η a b := by
  cases a <;> cases b <;> cases c <;> rfl

lemma bscN_jumpRev (η : ℝ) {n : ℕ} (x y : Fin n → Bool) :
    bscN η (jumpRev x) (jumpRev y) = bscN η x y := by
  unfold bscN jumpRev
  simp_rw [bsc_not]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)

lemma bscN_thetaPow (η : ℝ) {n : ℕ} (c : Bool) (x y : Fin n → Bool) :
    bscN η (thetaPow jumpRev c x) (thetaPow jumpRev c y) = bscN η x y := by
  cases c
  · rfl
  · exact bscN_jumpRev η x y

lemma bscN_xorS (η : ℝ) {n : ℕ} (k x y : Fin n → Bool) :
    bscN η (xorS x k) (xorS y k) = bscN η x y := by
  unfold bscN xorS
  simp_rw [bsc_xor]

/-! ### Payload noise commutes with the encoders -/

/-- Payload noise with an exactly received public endpoint. -/
def payloadChan {X : Type*} (K : X → X → ℝ) : D × X → D × X → ℝ :=
  fun r r' => if r'.1 = r.1 then K r.2 r'.2 else 0

lemma payloadChan_isChannel {X : Type*} [Fintype X] {K : X → X → ℝ} (hK : IsChannel K) :
    IsChannel (payloadChan (D := D) K) := by
  refine ⟨fun r r' => ?_, fun r => ?_⟩
  · unfold payloadChan; split_ifs
    · exact hK.nonneg _ _
    · exact le_refl 0
  · unfold payloadChan
    rw [Fintype.sum_prod_type]
    simp only
    rw [sum_eq_single r.1 (fun b _ hb => by simp [hb]) (by simp)]
    simp [hK.sum_one]

/-- A channel invariant under a bijection commutes with the corresponding push-forward. -/
theorem chan_push_equiv {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) (L : α → α → ℝ)
    (hL : ∀ a b, L (e a) (e b) = L a b) (P : α → ℝ) :
    chan L (push e P) = push e (chan L P) := by
  rw [push_equiv, push_equiv]
  funext y
  unfold chan
  refine Fintype.sum_equiv e.symm _ _ (fun x => ?_)
  rw [← hL (e.symm x) (e.symm y)]
  simp

lemma chan_payload_prodLaw {X : Type*} [Fintype X] (K : X → X → ℝ) (U : D → ℝ) (P0 : X → ℝ) :
    chan (payloadChan K) (prodLaw U P0) = prodLaw U (chan K P0) := by
  funext r
  obtain ⟨y, z⟩ := r
  unfold chan prodLaw payloadChan
  rw [Fintype.sum_prod_type]
  simp only
  rw [sum_eq_single y (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp only [if_true]
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by ring

/-- **Payload noise commutes with the one-bit encoder** (proof of Theorem `thm:payload`): if the
payload channel is invariant under the reversal `θ`, then encoding followed by noise equals
encoding the noisy raw string. -/
theorem encLaw_noise {X : Type*} [Fintype X] [DecidableEq X] (F : D ≃ D) (h : D → Bool)
    {θ : X → X} (hθ : Function.Involutive θ) (K : X → X → ℝ)
    (hK : ∀ c x y, K (thetaPow θ c x) (thetaPow θ c y) = K x y) (P0 : X → ℝ) :
    chan (payloadChan K) (encLaw F h θ P0) = encLaw F h θ (chan K P0) := by
  unfold encLaw
  rw [show encoder F h θ = encoderEquiv F h θ hθ from rfl, chan_push_equiv,
    chan_payload_prodLaw]
  rintro ⟨s, x⟩ ⟨s', x'⟩
  show payloadChan K (F s, thetaPow θ (h s) x) (F s', thetaPow θ (h s') x') =
    payloadChan K (s, x) (s', x')
  unfold payloadChan
  simp only [EmbeddingLike.apply_eq_iff_eq]
  split_ifs with hs
  · subst hs; exact hK _ _ _
  · rfl

/-- **Payload noise commutes with the causal encoder**: unmasking commutes with the flips. -/
theorem causalLaw_noise (F : D ≃ D) (h : D → Bool) (ℓ : ℕ)
    (K : (Fin (2 * ℓ) → Bool) → (Fin (2 * ℓ) → Bool) → ℝ)
    (hK : ∀ k x y, K (xorS x k) (xorS y k) = K x y) (P0 : (Fin (2 * ℓ) → Bool) → ℝ) :
    chan (payloadChan K) (causalLaw F h ℓ P0) = causalLaw F h ℓ (chan K P0) := by
  unfold causalLaw
  rw [show causalEnc F h ℓ = causalEncEquiv F h ℓ from rfl, chan_push_equiv,
    chan_payload_prodLaw]
  rintro ⟨s, x⟩ ⟨s', x'⟩
  show payloadChan K ((F ^ ℓ) s, xorS x (mask (genBits F h ℓ s)))
    ((F ^ ℓ) s', xorS x' (mask (genBits F h ℓ s'))) = payloadChan K (s, x) (s', x')
  unfold payloadChan
  simp only [EmbeddingLike.apply_eq_iff_eq]
  split_ifs with hs
  · subst hs; exact hK _ _ _
  · rfl

/-- Effective bias after payload noise, Eq. (peta). -/
def pEta (η p : ℝ) : ℝ := η + (1 - 2 * η) * p

lemma pEta_one_sub (η p : ℝ) : η + (1 - 2 * η) * (1 - p) = 1 - pEta η p := by
  unfold pEta; ring

/-- The noisy encoded ring laws are the encoded ring laws with bias `p_η`. -/
theorem ring_noisy_laws (F : D ≃ D) (h : D → Bool) (η p : ℝ) (m : ℕ) :
    chan (payloadChan (bscN η)) (ringP F h p m) = ringP F h (pEta η p) m ∧
    chan (payloadChan (bscN η)) (ringQ F h p m) = ringQ F h (pEta η p) m := by
  have hK : ∀ c (x y : Fin m → Bool), bscN η (thetaPow jumpRev c x) (thetaPow jumpRev c y) =
      bscN η x y := bscN_thetaPow η
  refine ⟨?_, ?_⟩
  · unfold ringP
    rw [encLaw_noise F h (jumpRev_involutive m) _ hK, chan_bscN_bernProd]
    rfl
  · unfold ringQ
    rw [encLaw_noise F h (jumpRev_involutive m) _ hK, chan_bscN_bernProd, pEta_one_sub]

lemma pEta_bounds {η p : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) (hp : 1 / 2 < p) (hp1 : p < 1) :
    1 / 2 < pEta η p ∧ pEta η p < 1 ∧ pEta η p ≤ p := by
  unfold pEta
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Theorem `thm:payload`** (Eqs. (noisykl), (noisytv)): for `0 ≤ η < 1/2` and
`1/2 < p < 1`, after independent payload noise (endpoint unchanged)
`D(P_{m,η}‖Q_{m,η}) = m d(p_η)` and `TV(P_{m,η}, Q_{m,η}) = 1 - 2 e_m(p_η)`; and every class of
noisy-record tests whose composition with the noise channel lies in a class `T` inherits the
noiseless efficient bound (Eq. (compdpi)). -/
theorem payload_noise_law [Nonempty D] (F : D ≃ D) (h : D → Bool) {η p : ℝ} (hη0 : 0 ≤ η)
    (hη : η < 1 / 2) (hp : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) :
    KL (chan (payloadChan (bscN η)) (ringP F h p m)) (chan (payloadChan (bscN η)) (ringQ F h p m))
      = m * drate (pEta η p) ∧
    TV (chan (payloadChan (bscN η)) (ringP F h p m)) (chan (payloadChan (bscN η)) (ringQ F h p m))
      = 1 - 2 * bayesErrBin m (pEta η p) ∧
    0 < drate (pEta η p) ∧
    ∀ (T T' : Set (D × (Fin m → Bool) → ℝ)) (b : ℝ), AdvLE T (ringP F h p m) (ringQ F h p m) b →
      (∀ A ∈ T', (fun r => ∑ r', payloadChan (bscN η) r r' * A r') ∈ T) →
      AdvLE T' (chan (payloadChan (bscN η)) (ringP F h p m))
        (chan (payloadChan (bscN η)) (ringQ F h p m)) b := by
  obtain ⟨h1, h2, -⟩ := pEta_bounds hη0 hη hp hp1
  obtain ⟨eP, eQ⟩ := ring_noisy_laws F h η p m
  obtain ⟨hKL, hd, hTV, -⟩ := ring_statistics F h h1 h2 m
  refine ⟨by rw [eP, eQ, hKL], by rw [eP, eQ, hTV], hd, fun T T' b hb hclos => ?_⟩
  exact advLE_chan (payloadChan_isChannel (bscN_isChannel hη0 (by linarith) m)) _ _ T T' hb hclos

/-! ### The noise loss -/

/-- `d` is nondecreasing on `[1/2, 1)`. -/
theorem drate_mono {q p : ℝ} (hq : 1 / 2 ≤ q) (hqp : q ≤ p) (hp1 : p < 1) :
    drate q ≤ drate p := by
  unfold drate
  have h1 : 0 ≤ Real.log (q / (1 - q)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : Real.log (q / (1 - q)) ≤ Real.log (p / (1 - p)) := by
    apply Real.log_le_log (div_pos (by linarith) (by linarith))
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  exact mul_le_mul (by linarith) h2 h1 (by linarith)

/-- **Eq. (noiseloss)**: payload noise destroys the nonnegative amount `m[d(p) - d(p_η)]` of
accessible divergence, while the core entropy production `m d(p)` is unchanged. -/
theorem noise_loss_nonneg {η p : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) (hp : 1 / 2 < p)
    (hp1 : p < 1) (m : ℕ) : 0 ≤ m * (drate p - drate (pEta η p)) := by
  obtain ⟨h1, -, h3⟩ := pEta_bounds hη0 hη hp hp1
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith [drate_mono h1.le h3 hp1])

/-- At `η = 1/2` the directional evidence vanishes completely. -/
theorem noise_half (p : ℝ) : drate (pEta (1 / 2) p) = 0 := by
  unfold drate pEta; ring_nf

/-! ### Weak-bias expansion -/

lemma log_ratio_expansion {x : ℝ} (h : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - Real.log (1 - x) - 2 * x| ≤ 4 * |x| ^ 3 := by
  have h1 := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by linarith) 2
  have h2 := Real.abs_log_sub_add_sum_range_le (show |-x| < 1 by rw [abs_neg]; linarith) 2
  simp [Finset.sum_range_succ] at h1 h2
  have hx : 0 ≤ |x| := abs_nonneg x
  have hd : 0 < 1 - |x| := by linarith
  have hb : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ hd]; nlinarith [pow_nonneg hx 3]
  have e : Real.log (1 + x) - Real.log (1 - x) - 2 * x =
      (x + x ^ 2 / (1 + 1) + Real.log (1 - x)) * (-1) +
        (-x + x ^ 2 / (1 + 1) + Real.log (1 + x)) := by ring
  rw [e]
  calc _ ≤ |(x + x ^ 2 / (1 + 1) + Real.log (1 - x)) * (-1)| +
        |(-x + x ^ 2 / (1 + 1) + Real.log (1 + x))| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul, abs_neg, abs_one, mul_one]; linarith

/-- **Expansion `d(1/2+u) = 8u² + O(u⁴)`**: explicitly `|d(1/2+u) - 8u²| ≤ 64 u⁴` for
`|u| ≤ 1/4`. -/
theorem drate_expansion {u : ℝ} (hu : |u| ≤ 1 / 4) :
    |drate (1 / 2 + u) - 8 * u ^ 2| ≤ 64 * u ^ 4 := by
  have hx : |2 * u| ≤ 1 / 2 := by rw [abs_mul]; norm_num; linarith
  have hL := log_ratio_expansion hx
  have hu1 : -(1 / 4) ≤ u ∧ u ≤ 1 / 4 := abs_le.mp hu
  have e : drate (1 / 2 + u) = 2 * u * (Real.log (1 + 2 * u) - Real.log (1 - 2 * u)) := by
    unfold drate
    rw [show (1 / 2 + u) / (1 - (1 / 2 + u)) = (1 + 2 * u) / (1 - 2 * u) by field_simp; ring,
      Real.log_div (by linarith) (by linarith)]
    ring
  rw [e, show 2 * u * (Real.log (1 + 2 * u) - Real.log (1 - 2 * u)) - 8 * u ^ 2 =
    2 * u * (Real.log (1 + 2 * u) - Real.log (1 - 2 * u) - 2 * (2 * u)) by ring, abs_mul]
  calc |2 * u| * |Real.log (1 + 2 * u) - Real.log (1 - 2 * u) - 2 * (2 * u)|
      ≤ |2 * u| * (4 * |2 * u| ^ 3) := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
    _ = 64 * u ^ 4 := by
        rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        have : |u| ^ 4 = u ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
        rw [← this]; ring

/-- **Eq. (noisethreshold)**: with `η = 1/2 - ε` (`0 < ε ≤ 1/4`), the noisy divergence is
`32 m ε² (p-1/2)² + O(m ε⁴)`; explicitly the error is at most `64 m ε⁴`. -/
theorem noise_threshold [Nonempty D] (F : D ≃ D) (h : D → Bool) {ε p : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 4) (hp : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) :
    |KL (chan (payloadChan (bscN (1 / 2 - ε))) (ringP F h p m))
        (chan (payloadChan (bscN (1 / 2 - ε))) (ringQ F h p m)) -
      32 * m * ε ^ 2 * (p - 1 / 2) ^ 2| ≤ 64 * m * ε ^ 4 := by
  rw [(payload_noise_law F h (by linarith) (by linarith) hp hp1 m).1]
  have hpe : pEta (1 / 2 - ε) p = 1 / 2 + 2 * ε * (p - 1 / 2) := by unfold pEta; ring
  rw [hpe]
  have hu : |2 * ε * (p - 1 / 2)| ≤ 1 / 4 := by
    rw [abs_le]; constructor <;> nlinarith
  have hE := drate_expansion hu
  have hmn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [show (m : ℝ) * drate (1 / 2 + 2 * ε * (p - 1 / 2)) - 32 * m * ε ^ 2 * (p - 1 / 2) ^ 2 =
    m * (drate (1 / 2 + 2 * ε * (p - 1 / 2)) - 8 * (2 * ε * (p - 1 / 2)) ^ 2) by ring, abs_mul,
    abs_of_nonneg hmn]
  have h4 : (2 * ε * (p - 1 / 2)) ^ 4 ≤ ε ^ 4 := by
    rw [mul_pow, show (2 : ℝ) * ε = ε * 2 by ring, mul_pow, mul_assoc, ← mul_pow]
    have : (2 * (p - 1 / 2)) ^ 4 ≤ 1 := by
      rw [show (1 : ℝ) = 1 ^ 4 by norm_num]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4
    nlinarith [pow_pos hε0 4]
  calc (m : ℝ) * |drate (1 / 2 + 2 * ε * (p - 1 / 2)) - 8 * (2 * ε * (p - 1 / 2)) ^ 2|
      ≤ m * (64 * (2 * ε * (p - 1 / 2)) ^ 4) := mul_le_mul_of_nonneg_left hE hmn
    _ ≤ m * (64 * ε ^ 4) := by nlinarith
    _ = 64 * m * ε ^ 4 := by ring

/-! ### Proposition `prop:contamination` for the ring -/

/-- **Proposition `prop:contamination`, ring application**: with `ε_m = e^{-√m}` (`m ≥ 1`),
the contaminated ring laws have `D ≤ √m` (rather than `Θ(m)`), total variation
`(1 - 2ε_m)(1 - 2e_m(p))`, each contaminated law is within `ε_m` of the original, and `ε_m` is
negligible. -/
theorem ring_contamination [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    KL (mix (Real.exp (-Real.sqrt m)) (ringP F h p m) (ringQ F h p m))
        (mix (Real.exp (-Real.sqrt m)) (ringQ F h p m) (ringP F h p m)) ≤ Real.sqrt m ∧
    TV (mix (Real.exp (-Real.sqrt m)) (ringP F h p m) (ringQ F h p m))
        (mix (Real.exp (-Real.sqrt m)) (ringQ F h p m) (ringP F h p m)) =
      (1 - 2 * Real.exp (-Real.sqrt m)) * (1 - 2 * bayesErrBin m p) ∧
    TV (mix (Real.exp (-Real.sqrt m)) (ringP F h p m) (ringQ F h p m)) (ringP F h p m) ≤
      Real.exp (-Real.sqrt m) := by
  have hp0 : 0 < p := by linarith
  have hP := encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m)
  have hQ := encLaw_isProb F h jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) m)
  have hs : 1 ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact_mod_cast hm
  set ε := Real.exp (-Real.sqrt m)
  have hε0 : 0 < ε := Real.exp_pos _
  have hε : ε < 1 / 2 := by
    calc ε ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ < 1 / 2 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
        linarith
  refine ⟨?_, ?_, contam_TV_close _ _ hP hQ hε0.le⟩
  · calc _ ≤ Real.log ((1 - ε) / ε) := contam_KL_le hP hQ hε0 hε
      _ ≤ Real.log (1 / ε) := Real.log_le_log (div_pos (by linarith) hε0)
          (div_le_div_of_nonneg_right (by linarith) hε0.le)
      _ = Real.sqrt m := by
          rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  · rw [contam_TV _ _ hε.le, (ring_statistics F h hp hp1 m).2.2.1]

/-- `e^{-√n}` is negligible. -/
theorem exp_neg_sqrt_negligible : Negligible (fun n : ℕ => Real.exp (-Real.sqrt n)) := by
  intro c
  have key : Tendsto (fun x : ℝ => x ^ (2 * c) * Real.exp (-x)) atTop (nhds 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * c)
    exact this
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have := (key.comp hs).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [abs_of_pos (Real.exp_pos _), le_div_iff₀ (by positivity)]
  have : Real.sqrt n ^ (2 * c) = (n : ℝ) ^ c := by
    rw [pow_mul, Real.sq_sqrt hnpos.le]
  rw [this] at hn
  linarith [mul_comm (Real.exp (-Real.sqrt n)) ((n : ℝ) ^ c)]

end Arrow

end NoisePart


/-! ════════════════════════════════════════════════════════════════════
    Part: Reliability
    ════════════════════════════════════════════════════════════════════ -/

section ReliabilityPart

/-!
# Section 10.3: an exact asymptotic reliability law

**Theorem `thm:reliability`**: for symmetric orientation contamination of the encoded ring laws
with `ε_m → 0` and `-(1/m) log ε_m → γ ∈ [0, ∞]`,
`(1/m) D(P_{m,ε_m} ‖ Q_{m,ε_m}) → min(d(p), γ)`.

The proof proceeds through an exact formula: the contaminated divergence equals
`(1 - 2ε) E[g_ε(σ)]`, where `σ = a(2K - m)`, `K ~ Bin(m,p)`, and `g_ε` is the contaminated
likelihood (Eq. (clippedlikelihood)).
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ### The contaminated likelihood `g_ε` -/

/-- The contaminated log-likelihood as a function of the clean one, Eq. (clippedlikelihood). -/
noncomputable def gfun (ε s : ℝ) : ℝ :=
  Real.log (((1 - ε) * Real.exp s + ε) / ((1 - ε) + ε * Real.exp s))

/-- Agreement with the form `σ + log(1-ε+εe^{-σ}) - log(1-ε+εe^{σ})` of Eq. (clippedlikelihood). -/
theorem gfun_eq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (s : ℝ) :
    gfun ε s = s + Real.log (1 - ε + ε * Real.exp (-s)) - Real.log (1 - ε + ε * Real.exp s) := by
  unfold gfun
  have he := Real.exp_pos s
  have hen := Real.exp_pos (-s)
  have hA : 0 < 1 - ε + ε * Real.exp (-s) := by have := mul_pos h0 hen; linarith
  have hB : 0 < 1 - ε + ε * Real.exp s := by have := mul_pos h0 he; linarith
  rw [show (1 - ε) * Real.exp s + ε = Real.exp s * (1 - ε + ε * Real.exp (-s)) by
    rw [mul_add, Real.exp_neg]; field_simp,
    Real.log_div (by positivity) hB.ne', Real.log_mul he.ne' hA.ne', Real.log_exp]

lemma gfun_odd (ε s : ℝ) : gfun ε (-s) = -gfun ε s := by
  unfold gfun
  rw [← Real.log_inv, inv_div]
  congr 1
  have he := Real.exp_pos s
  rw [Real.exp_neg]
  field_simp

lemma gfun_arg_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (s : ℝ) :
    0 < ((1 - ε) * Real.exp s + ε) / ((1 - ε) + ε * Real.exp s) := by
  have := Real.exp_pos s
  apply div_pos <;> nlinarith

lemma gfun_mono {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {s t : ℝ} (hst : s ≤ t) :
    gfun ε s ≤ gfun ε t := by
  unfold gfun
  apply Real.log_le_log (gfun_arg_pos h0 (by linarith) s)
  have hs := Real.exp_pos s
  have hle : Real.exp s ≤ Real.exp t := Real.exp_le_exp.mpr hst
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - 2 * ε by linarith) (sub_nonneg.mpr hle)]

lemma gfun_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gfun ε s := by
  have := gfun_mono h0 h1 hs
  unfold gfun at this ⊢
  simpa using this

lemma gfun_ge_self {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {s : ℝ} (hs : s ≤ 0) : s ≤ gfun ε s := by
  unfold gfun
  have he := Real.exp_pos s
  have he1 : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr hs
  calc s = Real.log (Real.exp s) := (Real.log_exp s).symm
    _ ≤ _ := by
      apply Real.log_le_log he
      rw [le_div_iff₀ (by nlinarith)]
      nlinarith [mul_nonneg h0.le (mul_nonneg he.le (sub_nonneg.mpr he1))]

/-- Clipping estimate: `g_ε(s) ≥ min(s, -log ε) + log(1-ε) - log 2`. -/
lemma gfun_ge_min {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) (s : ℝ) :
    min s (-Real.log ε) + Real.log (1 - ε) - Real.log 2 ≤ gfun ε s := by
  have he := Real.exp_pos s
  have h1e : 0 < 1 - ε := by linarith
  have hden : 0 < (1 - ε) + ε * Real.exp s := by positivity
  have step : s + Real.log (1 - ε) - Real.log ((1 - ε) + ε * Real.exp s) ≤ gfun ε s := by
    have e : Real.log (Real.exp s * (1 - ε) / ((1 - ε) + ε * Real.exp s)) =
        s + Real.log (1 - ε) - Real.log ((1 - ε) + ε * Real.exp s) := by
      rw [Real.log_div (by positivity) hden.ne', Real.log_mul he.ne' h1e.ne', Real.log_exp]
    rw [← e]
    unfold gfun
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by linarith [mul_comm (Real.exp s) (1 - ε)]) hden.le
  by_cases hc : ε * Real.exp s ≤ 1
  · have : Real.log ((1 - ε) + ε * Real.exp s) ≤ Real.log 2 :=
      Real.log_le_log hden (by linarith)
    have := min_le_left s (-Real.log ε)
    linarith
  · push_neg at hc
    have e : Real.log (2 * ε * Real.exp s) = Real.log 2 + Real.log ε + s := by
      rw [Real.log_mul (by positivity) he.ne', Real.log_mul (by norm_num) h0.ne', Real.log_exp]
    have : Real.log ((1 - ε) + ε * Real.exp s) ≤ Real.log 2 + Real.log ε + s := by
      rw [← e]
      exact Real.log_le_log hden (by linarith)
    have := min_le_right s (-Real.log ε)
    linarith

/-- Combined pointwise lower bound used in the proof of Theorem `thm:reliability`. -/
lemma gfun_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {A S s : ℝ} (hA : 0 ≤ A)
    (hs : -A ≤ s) :
    let G := min S (-Real.log ε) + Real.log (1 - ε) - Real.log 2
    G - (|G| + A) * (if s < S then 1 else 0) ≤ gfun ε s := by
  intro G
  have hG := le_abs_self G
  split_ifs with h
  · by_cases hs0 : 0 ≤ s
    · have := gfun_nonneg h0 h1 hs0; linarith
    · have := gfun_ge_self h0 h1 (le_of_lt (not_le.mp hs0)); linarith
  · push_neg at h
    have := gfun_mono h0 h1 h
    have := gfun_ge_min h0 h1 S
    simp only [G] at *
    linarith

/-! ### The exact formula -/

lemma ringQ_pos [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (r : D × (Fin m → Bool)) : 0 < ringQ F h p m r := by
  rw [ringQ_eq_comp]; exact ringP_pos F h hp0 hp1 m _

/-- **Exact contaminated divergence**: `D(P_{m,ε}‖Q_{m,ε}) = (1-2ε) E g_ε(a(2K-m))`,
`K ~ Bin(m,p)`. -/
theorem contam_KL_exact [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) (ε : ℝ) :
    KL (mix ε (ringP F h p m) (ringQ F h p m)) (mix ε (ringQ F h p m) (ringP F h p m)) =
      (1 - 2 * ε) * binExp p m (fun k => gfun ε (affinity p * (2 * (k : ℝ) - m))) := by
  set P := ringP F h p m
  set Q := ringQ F h p m
  set σ := llr P Q
  have hP : ∀ r, 0 < P r := ringP_pos F h hp0 hp1 m
  have hQ : ∀ r, 0 < Q r := ringQ_pos F h hp0 hp1 m
  have hPQ : ∀ r, P r = Q r * Real.exp (σ r) := by
    intro r
    simp only [σ, llr]
    rw [Real.exp_log (div_pos (hP r) (hQ r))]
    field_simp [(hQ r).ne']
  have hpt : ∀ r, Real.log (mix ε P Q r / mix ε Q P r) = gfun ε (σ r) := by
    intro r
    unfold mix gfun
    rw [hPQ r]
    congr 1
    have := hQ r
    field_simp
  have hKL : KL (mix ε P Q) (mix ε Q P) =
      (1 - ε) * expect P (fun r => gfun ε (σ r)) + ε * expect Q (fun r => gfun ε (σ r)) := by
    unfold KL expect
    simp_rw [hpt]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    unfold mix; ring
  rw [hKL, expect_ringQ_llr F h hp0 hp1 m (gfun ε)]
  simp_rw [gfun_odd]
  have e : expect P (fun r => -gfun ε (σ r)) = -expect P (fun r => gfun ε (σ r)) := by
    unfold expect; rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => by ring
  rw [e, expect_ringP_llr F h hp0 hp1 m (gfun ε)]
  ring

/-! ### Finite-`m` bounds -/

/-- Upper bounds: `D(P_{m,ε}‖Q_{m,ε}) ≤ m d(p)` (data processing) and `≤ log((1-ε)/ε)`
(Proposition `prop:contamination`). -/
theorem contam_KL_upper [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) (m : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    KL (mix ε (ringP F h p m) (ringQ F h p m)) (mix ε (ringQ F h p m) (ringP F h p m)) ≤
      m * drate p ∧
    KL (mix ε (ringP F h p m) (ringQ F h p m)) (mix ε (ringQ F h p m) (ringP F h p m)) ≤
      -Real.log ε := by
  have hp0 : 0 < p := by linarith
  have hP := encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m)
  have hQ := encLaw_isProb F h jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) m)
  have hτ : Function.Involutive (recRev (D := D) (jumpRev (m := m))) := by
    intro r; simp [recRev, jumpRev_involutive m r.2]
  refine ⟨?_, ?_⟩
  · obtain ⟨c1, c2⟩ := chan_contamChan ε (ringP F h p m) _ hτ
    rw [← ringQ_eq_comp] at c1 c2
    rw [← c1, ← c2, ← (ring_statistics F h hp hp1 m).1]
    exact KL_chan_le (contamChan_isChannel h0.le (by linarith) _) hP.nonneg hQ.nonneg
      (fun r hr => absurd hr (ringQ_pos F h hp0 hp1 m r).ne')
  · calc _ ≤ Real.log ((1 - ε) / ε) := contam_KL_le hP hQ h0 h1
      _ ≤ Real.log (1 / ε) := Real.log_le_log (div_pos (by linarith) h0)
          (div_le_div_of_nonneg_right (by linarith) h0.le)
      _ = -Real.log ε := by rw [one_div, Real.log_inv]

/-- Lower bound: for `δ > 0` and `m ≥ 1`,
`D/m ≥ (1-2ε)[G/m - (|G|/m + a) C_δ/m]` where `G = min(m(d-δ), -log ε) + log(1-ε) - log 2`
and `C_δ = 4a² p(1-p)/δ²` (Chebyshev). -/
theorem contam_KL_lower [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 0 < m) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {δ : ℝ}
    (hδ : 0 < δ) :
    let G := min (m * (drate p - δ)) (-Real.log ε) + Real.log (1 - ε) - Real.log 2
    (1 - 2 * ε) * (G - (|G| + affinity p * m) *
        (p * (1 - p) / (m * (δ / (2 * affinity p)) ^ 2))) ≤
      KL (mix ε (ringP F h p m) (ringQ F h p m)) (mix ε (ringQ F h p m) (ringP F h p m)) := by
  intro G
  have hp0 : 0 < p := by linarith
  have ha : 0 < affinity p := by
    unfold affinity; apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set a := affinity p
  set S := (m : ℝ) * (drate p - δ)
  have hA : 0 ≤ a * m := by positivity
  rw [contam_KL_exact F h hp0 hp1 m ε]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have hpt : ∀ k : ℕ, k ≤ m → G - (|G| + a * m) *
      (if (k : ℝ) ≤ m * (p - δ / (2 * a)) then 1 else 0) ≤ gfun ε (a * (2 * (k : ℝ) - m)) := by
    intro k hk
    have hk' : (k : ℝ) ≥ 0 := Nat.cast_nonneg k
    have hlow := gfun_lower h0 h1 hA (S := S) (s := a * (2 * (k : ℝ) - m)) (by nlinarith)
    simp only at hlow
    refine le_trans ?_ hlow
    have hG := le_abs_self G
    by_cases h2 : a * (2 * (k : ℝ) - m) < S
    · rw [if_pos h2]
      have : (k : ℝ) ≤ m * (p - δ / (2 * a)) := by
        have hd : drate p = a * (2 * p - 1) := by simp only [a]; unfold drate affinity; ring
        simp only [S] at h2
        rw [hd] at h2
        have : 2 * a * (k : ℝ) ≤ 2 * a * (m * (p - δ / (2 * a))) := by
          rw [show 2 * a * (m * (p - δ / (2 * a))) = a * (2 * m * p) - m * δ by field_simp]
          nlinarith
        exact le_of_mul_le_mul_left this (by positivity)
      rw [if_pos this]
    · rw [if_neg h2]
      split_ifs <;> nlinarith [abs_nonneg G]
  have hcheb := lowerTail_chebyshev hp0.le hp1.le hm (show 0 < δ / (2 * a) by positivity)
  calc G - (|G| + a * m) * (p * (1 - p) / (m * (δ / (2 * a)) ^ 2))
      ≤ G - (|G| + a * m) * binExp p m
          (fun k => if (k : ℝ) ≤ m * (p - δ / (2 * a)) then 1 else 0) := by
        have : 0 ≤ |G| + a * m := by positivity
        nlinarith
    _ = binExp p m (fun k => G - (|G| + a * m) *
          (if (k : ℝ) ≤ m * (p - δ / (2 * a)) then 1 else 0)) := by
        rw [show (fun k : ℕ => G - (|G| + a * m) *
            (if (k : ℝ) ≤ m * (p - δ / (2 * a)) then 1 else 0)) =
          fun k : ℕ => G * 1 + (-(|G| + a * m)) *
            (if (k : ℝ) ≤ m * (p - δ / (2 * a)) then 1 else 0) by funext k; ring,
          binExp_add, binExp_const_mul, binExp_const_mul, binExp_one]
        ring
    _ ≤ _ := by
        unfold binExp
        refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt _ (ones_le x)) ?_
        exact (bernProd_isProb hp0.le hp1.le m).nonneg x

/-! ### The asymptotic reliability law -/

section Asymptotic

variable (Dm : ℕ → Type*) [∀ m, Fintype (Dm m)] [∀ m, DecidableEq (Dm m)] [∀ m, Nonempty (Dm m)]
  (F : ∀ m, Dm m ≃ Dm m) (h : ∀ m, Dm m → Bool)

/-- The contaminated ring divergence at length `m` and contamination level `ε`. -/
noncomputable def contamKL (p : ℝ) (ε : ℕ → ℝ) (m : ℕ) : ℝ :=
  KL (mix (ε m) (ringP (F m) (h m) p m) (ringQ (F m) (h m) p m))
    (mix (ε m) (ringQ (F m) (h m) p m) (ringP (F m) (h m) p m))

lemma eventually_eps_small {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0)) :
    ∀ᶠ m : ℕ in atTop, ε m < 1 / 2 :=
  hε.eventually (gt_mem_nhds (by norm_num))

/-- Lower half of the proof of Theorem `thm:reliability`. -/
theorem contamKL_lower_eventually {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {ε : ℕ → ℝ}
    (hε0 : ∀ m, 0 < ε m) (hε : Tendsto ε atTop (nhds 0)) {δ : ℝ} (hδ : 0 < δ) {M : ℝ}
    (hM : Tendsto (fun m : ℕ => min (drate p - δ) (-Real.log (ε m) / m)) atTop (nhds M))
    {b : ℝ} (hb : b < M) :
    ∀ᶠ m : ℕ in atTop, b < contamKL Dm F h p ε m / m := by
  set a := affinity p
  set C := p * (1 - p) / (δ / (2 * a)) ^ 2
  set G : ℕ → ℝ := fun m =>
    min (m * (drate p - δ)) (-Real.log (ε m)) + Real.log (1 - ε m) - Real.log 2
  have hG : Tendsto (fun m : ℕ => G m / m) atTop (nhds M) := by
    have hlog : Tendsto (fun m : ℕ => (Real.log (1 - ε m) - Real.log 2) / m) atTop (nhds 0) := by
      have h1 : Tendsto (fun m : ℕ => Real.log (1 - ε m) - Real.log 2) atTop
          (nhds (Real.log (1 - 0) - Real.log 2)) :=
        ((tendsto_const_nhds.sub hε).log (by norm_num)).sub tendsto_const_nhds
      exact h1.div_atTop tendsto_natCast_atTop_atTop
    have := hM.add hlog
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [G]
    rw [add_sub_assoc, add_div]
    congr 1
    rw [← min_div_div_right hmpos.le, mul_div_cancel_left₀ _ hmpos.ne']
  have hL : Tendsto (fun m : ℕ => (1 - 2 * ε m) * (G m / m - (|G m / m| + a) * (C / m)))
      atTop (nhds ((1 - 2 * 0) * (M - (|M| + a) * 0))) := by
    refine (tendsto_const_nhds.sub (hε.const_mul 2)).mul (hG.sub ?_)
    exact (hG.abs.add tendsto_const_nhds).mul (tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop)
  simp only [mul_zero, sub_zero, one_mul] at hL
  filter_upwards [hL.eventually (lt_mem_nhds hb), eventually_eps_small hε,
    eventually_gt_atTop 0] with m h1 h2 hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlow := contam_KL_lower (F m) (h m) hp hp1 hm (hε0 m) h2 hδ
  simp only at hlow
  refine lt_of_lt_of_le h1 ?_
  rw [le_div_iff₀ hmpos]
  unfold contamKL
  refine le_trans (le_of_eq ?_) hlow
  simp only [G, C, a]
  rw [abs_div, abs_of_pos hmpos]
  field_simp

/-- Upper half: eventually `D/m ≤ min(d(p), -(1/m) log ε_m)`. -/
theorem contamKL_upper_eventually {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {ε : ℕ → ℝ}
    (hε0 : ∀ m, 0 < ε m) (hε : Tendsto ε atTop (nhds 0)) :
    ∀ᶠ m : ℕ in atTop, contamKL Dm F h p ε m / m ≤ min (drate p) (-Real.log (ε m) / m) := by
  filter_upwards [eventually_eps_small hε, eventually_gt_atTop 0] with m h2 hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨u1, u2⟩ := contam_KL_upper (F m) (h m) hp hp1 m (hε0 m) h2
  refine le_min ?_ (div_le_div_of_nonneg_right u2 hmpos.le)
  rw [div_le_iff₀ hmpos]; unfold contamKL; linarith

/-- **Theorem `thm:reliability`** (Eq. (reliabilitylaw)), finite exponent `γ`: if `ε_m → 0`,
`ε_m > 0` and `-(1/m) log ε_m → γ`, then `(1/m) D(P_{m,ε_m}‖Q_{m,ε_m}) → min(d(p), γ)`.
(The case `γ = 0` covers all subexponential contamination, e.g. `ε_m = e^{-√m}`.) -/
theorem reliability_law {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {ε : ℕ → ℝ}
    (hε0 : ∀ m, 0 < ε m) (hε : Tendsto ε atTop (nhds 0)) {γ : ℝ}
    (hγ : Tendsto (fun m : ℕ => -Real.log (ε m) / m) atTop (nhds γ)) :
    Tendsto (fun m : ℕ => contamKL Dm F h p ε m / m) atTop (nhds (min (drate p) γ)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · set δ := (min (drate p) γ - b) / 2 with hδdef
    have hδ : 0 < δ := by linarith
    have hM : Tendsto (fun m : ℕ => min (drate p - δ) (-Real.log (ε m) / m)) atTop
        (nhds (min (drate p - δ) γ)) := tendsto_const_nhds.min hγ
    refine contamKL_lower_eventually Dm F h hp hp1 hε0 hε hδ hM ?_
    have h1 := min_le_left (drate p) γ
    have h2 := min_le_right (drate p) γ
    rcases min_choice (drate p - δ) γ with h | h <;> rw [h] <;> linarith
  · have hlim : Tendsto (fun m : ℕ => min (drate p) (-Real.log (ε m) / m)) atTop
        (nhds (min (drate p) γ)) := tendsto_const_nhds.min hγ
    filter_upwards [contamKL_upper_eventually Dm F h hp hp1 hε0 hε,
      hlim.eventually (gt_mem_nhds hb)] with m h1 h2
    linarith

/-- **Theorem `thm:reliability`**, the case `γ = ∞` (natural convention `min(d, ∞) = d`): if
`-(1/m) log ε_m → ∞`, the full divergence density `d(p)` is retained. -/
theorem reliability_law_infinite {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {ε : ℕ → ℝ}
    (hε0 : ∀ m, 0 < ε m) (hε : Tendsto ε atTop (nhds 0))
    (hγ : Tendsto (fun m : ℕ => -Real.log (ε m) / m) atTop atTop) :
    Tendsto (fun m : ℕ => contamKL Dm F h p ε m / m) atTop (nhds (drate p)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · set δ := (drate p - b) / 2 with hδdef
    have hδ : 0 < δ := by linarith
    have hM : Tendsto (fun m : ℕ => min (drate p - δ) (-Real.log (ε m) / m)) atTop
        (nhds (drate p - δ)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hγ.eventually (eventually_ge_atTop (drate p - δ))] with m hm
      exact (min_eq_left hm).symm
    exact contamKL_lower_eventually Dm F h hp hp1 hε0 hε hδ hM (by linarith)
  · filter_upwards [contamKL_upper_eventually Dm F h hp hp1 hε0 hε] with m h1
    exact lt_of_le_of_lt (h1.trans (min_le_left _ _)) hb

/-- Subexponential contamination such as the negligible `ε_m = e^{-√m}` has zero limiting
divergence per jump. -/
theorem reliability_sqrt {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    Tendsto (fun m : ℕ => contamKL Dm F h p (fun m => Real.exp (-Real.sqrt m)) m / m) atTop
      (nhds 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hε : Tendsto (fun m : ℕ => Real.exp (-Real.sqrt m)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hγ : Tendsto (fun m : ℕ => -Real.log (Real.exp (-Real.sqrt m)) / m) atTop (nhds 0) := by
    refine (tendsto_inv_atTop_zero.comp hs).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [Function.comp, Real.log_exp, neg_neg]
    have : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
    rw [eq_div_iff hmpos.ne']
    nth_rewrite 2 [← Real.mul_self_sqrt hmpos.le]
    field_simp
  have := reliability_law Dm F h hp hp1 (fun m => Real.exp_pos _) hε hγ
  rwa [min_eq_right (drate_pos (by linarith) hp1 (by linarith)).le] at this

end Asymptotic

end Arrow

end ReliabilityPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Readout
    ════════════════════════════════════════════════════════════════════ -/

section ReadoutPart

/-!
# Section 10.4–10.5: protecting the public endpoint, and a logical reliability criterion

* Eq. (endpointfail): majority decoding of an `r`-fold repetition code on `d` endpoint bits fails
  with probability at most `d e^{-2r(1/2-η_Y)²}`.
* **Theorem `thm:readout`**: with the repetition-coded endpoint and independent payload noise,
  an explicit unrestricted decoder has both orientation errors at most
  `α = d e^{-2r(1/2-η_Y)²} + P(Bin(m, p_η) ≤ m/2)`; hence `TV ≥ 1 - 2α`,
  `D ≥ (1-2α) log((1-α)/α)` (Eq. (binarylower)), `D ≤ m d(p)`, and efficient advantage is
  preserved by the (efficient) channel.
* The end-to-end transfer criterion (Eq. (transferadv)) and its divergence lower bound.
-/


open Finset Real Filter

namespace Arrow

/-! ### The repetition code -/

/-- Transmission of the `d` endpoint bits, each repeated `r` times, through independent binary
symmetric noise. -/
def repChan (η : ℝ) {d r : ℕ} (y : Fin d → Bool) (w : Fin d → Fin r → Bool) : ℝ :=
  ∏ i, ∏ t, bsc η (y i) (w i t)

/-- Blockwise majority decoding. -/
def majDec {d r : ℕ} (w : Fin d → Fin r → Bool) : Fin d → Bool := fun i => decide (r < 2 * ones (w i))

lemma bsc_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (a b : Bool) : 0 ≤ bsc η a b := by
  unfold bsc; split_ifs <;> linarith

lemma repChan_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {d r : ℕ} (y : Fin d → Bool)
    (w : Fin d → Fin r → Bool) : 0 ≤ repChan η y w :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => bsc_nonneg h0 h1 _ _

lemma repChan_sum (η : ℝ) {d r : ℕ} (y : Fin d → Bool) : ∑ w : Fin d → Fin r → Bool, repChan η (r := r) y w = 1 := by
  unfold repChan
  rw [← Fintype.prod_sum (f := fun i (c : Fin r → Bool) => ∏ t, bsc η (y i) (c t))]
  refine prod_eq_one fun i _ => ?_
  rw [← Fintype.prod_sum (f := fun _ b => bsc η (y i) b)]
  refine prod_eq_one fun t _ => ?_
  cases y i <;> simp [bsc]

lemma repChan_maskObs (η : ℝ) {d r : ℕ} (y : Fin d → Bool) (c : Fin d → Fin r → Bool) :
    repChan η y (maskObs (fun i => !(y i)) c) = iidLaw d (bernProd (1 - η) r) c := by
  unfold repChan maskObs iidLaw piLaw bernProd iidLaw piLaw
  refine prod_congr rfl fun i _ => prod_congr rfl fun t _ => ?_
  cases hy : y i <;> cases hc : c i t <;> simp [bsc, bern, hy]

lemma majDec_maskObs {d r : ℕ} (y : Fin d → Bool) (c : Fin d → Fin r → Bool) :
    majDec (maskObs (fun i => !(y i)) c) = y ↔
      maskEst (maskObs (fun i => !(y i)) c) = fun i => !(y i) := by
  unfold majDec maskEst
  constructor <;> intro hh <;> funext i <;> have := congrFun hh i <;> simp only at this ⊢
  · rw [this]
  · cases hy : y i <;> rw [hy] at this <;> simpa using this

lemma maskObs_involutive {d r : ℕ} (K : Fin d → Bool) :
    Function.Involutive (maskObs (q := r) K) := by
  intro c; funext i t; simp [maskObs]

/-- **Eq. (endpointfail)**: for odd `r` and `0 < η_Y < 1/2`, blockwise majority decoding of the
repeated endpoint fails with probability at most `d e^{-2r(1/2-η_Y)²}`, whatever the endpoint. -/
theorem endpoint_failure {d r : ℕ} (hr : Odd r) {η : ℝ} (h0 : 0 < η) (h1 : η < 1 / 2)
    (y : Fin d → Bool) :
    ∑ w : Fin d → Fin r → Bool, repChan η y w * (if majDec w = y then 0 else 1) ≤
      d * Real.exp (-2 * r * (1 / 2 - η) ^ 2) := by
  set K : Fin d → Bool := fun i => !(y i)
  have hre := Fintype.sum_equiv (Function.Involutive.toPerm _ (maskObs_involutive (r := r) K))
    (fun c => repChan η y (maskObs K c) * (if majDec (maskObs K c) = y then 0 else 1))
    (fun w => repChan η y w * (if majDec w = y then 0 else 1)) (fun c => rfl)
  rw [← hre]
  have := mask_recovery_failure hr (p := 1 - η) (by linarith) (by linarith) K
  rw [show (1 - η - 1 / 2) = 1 / 2 - η by ring] at this
  refine le_trans (le_of_eq ?_) this
  unfold expect
  refine sum_congr rfl fun c _ => ?_
  dsimp only
  simp only [K]
  rw [repChan_maskObs]
  congr 1
  exact if_congr (majDec_maskObs y c) rfl rfl

/-! ### The noisy readout theorem -/

variable {d r m : ℕ}

/-- The full readout channel: repetition-coded endpoint and independent payload noise. -/
def readChan (ηY η : ℝ) :
    (Fin d → Bool) × (Fin m → Bool) → (Fin d → Fin r → Bool) × (Fin m → Bool) → ℝ :=
  fun yz wz => repChan ηY yz.1 wz.1 * bscN η yz.2 wz.2

lemma readChan_isChannel {ηY η : ℝ} (hY0 : 0 ≤ ηY) (hY1 : ηY ≤ 1) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    IsChannel (readChan (d := d) (r := r) (m := m) ηY η) := by
  refine ⟨fun x y => mul_nonneg (repChan_nonneg hY0 hY1 _ _)
    ((bscN_isChannel h0 h1 m).nonneg _ _), fun x => ?_⟩
  unfold readChan
  rw [Fintype.sum_prod_type]
  simp only
  rw [← sum_mul_sum, repChan_sum, (bscN_isChannel h0 h1 m).sum_one, one_mul]

/-- The ideal orientation test on noisy payload with the true endpoint. -/
noncomputable def idealTest (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool) :
    (Fin d → Bool) × (Fin m → Bool) → ℝ :=
  fun yz => if m < 2 * ones (thetaPow jumpRev (h (F.symm yz.1)) yz.2) then 1 else 0

/-- The unrestricted readout decoder: majority-decode the endpoint, invert the permutation,
decode the noisy raw directions and apply the majority test. -/
noncomputable def readTest (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool) :
    (Fin d → Fin r → Bool) × (Fin m → Bool) → ℝ :=
  fun wz => idealTest F h (majDec wz.1, wz.2)

lemma readTest_isTest (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool) :
    IsTest (readTest (r := r) (m := m) F h) := fun wz => by
  unfold readTest idealTest; split_ifs <;> norm_num

/-- Failure probability of the endpoint decoder for a given endpoint. -/
noncomputable def endFail (ηY : ℝ) (y : Fin d → Bool) : ℝ :=
  ∑ w : Fin d → Fin r → Bool, repChan ηY y w * (if majDec w = y then 0 else 1)

lemma inner_split {ηY η : ℝ} (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool)
    (hY0 : 0 ≤ ηY) (hY1 : ηY ≤ 1) (h0 : 0 ≤ η) (h1 : η ≤ 1) (x : (Fin d → Bool) × (Fin m → Bool)) :
    |∑ wz, readChan (r := r) ηY η x wz * readTest F h wz -
      ∑ r', payloadChan (bscN η) x r' * idealTest F h r'| ≤ endFail (r := r) ηY x.1 := by
  obtain ⟨y, z⟩ := x
  have hpay : ∑ r', payloadChan (bscN η) (y, z) r' * idealTest F h r' =
      ∑ z', bscN η z z' * idealTest F h (y, z') := by
    rw [Fintype.sum_prod_type]
    simp only [payloadChan]
    rw [sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hsplit : ∑ wz, readChan (r := r) ηY η (y, z) wz * readTest F h wz -
      ∑ z', bscN η z z' * idealTest F h (y, z') =
      ∑ w : Fin d → Fin r → Bool, ∑ z', repChan ηY y w * bscN η z z' *
        (readTest F h (w, z') - idealTest F h (y, z')) := by
    rw [Fintype.sum_prod_type]
    simp only [readChan]
    have : ∑ z', bscN η z z' * idealTest F h (y, z') =
        ∑ w : Fin d → Fin r → Bool, ∑ z', repChan ηY y w * bscN η z z' * idealTest F h (y, z') := by
      have e : ∑ w : Fin d → Fin r → Bool, ∑ z', repChan ηY y w * bscN η z z' *
          idealTest F h (y, z') =
          (∑ w : Fin d → Fin r → Bool, repChan ηY y w) * ∑ z', bscN η z z' * idealTest F h (y, z') := by
        rw [sum_mul_sum]
        exact sum_congr rfl fun w _ => sum_congr rfl fun z' _ => by ring
      rw [e, repChan_sum, one_mul]
    rw [this, ← sum_sub_distrib]
    refine sum_congr rfl fun w _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun z' _ => by ring
  rw [hpay, hsplit]
  have hpt : ∀ (w : Fin d → Fin r → Bool) (z' : Fin m → Bool), |repChan ηY y w * bscN η z z' *
      (readTest F h (w, z') - idealTest F h (y, z'))| ≤
      repChan ηY y w * bscN η z z' * (if majDec w = y then 0 else 1) := by
    intro w z'
    rw [abs_mul, abs_of_nonneg (mul_nonneg (repChan_nonneg hY0 hY1 _ _)
      ((bscN_isChannel h0 h1 m).nonneg _ _))]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (repChan_nonneg hY0 hY1 _ _)
      ((bscN_isChannel h0 h1 m).nonneg _ _))
    unfold readTest
    split_ifs with hw
    · simp [hw]
    · unfold idealTest; split_ifs <;> norm_num
  calc _ ≤ ∑ w : Fin d → Fin r → Bool, ∑ z', |repChan ηY y w * bscN η z z' *
        (readTest F h (w, z') - idealTest F h (y, z'))| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ w : Fin d → Fin r → Bool, ∑ z', repChan ηY y w * bscN η z z' * (if majDec w = y then 0 else 1) :=
        sum_le_sum fun w _ => sum_le_sum fun z' _ => hpt w z'
    _ = endFail ηY y := by
        unfold endFail
        refine sum_congr rfl fun w _ => ?_
        rw [show ∑ z', repChan ηY y w * bscN η z z' * (if majDec w = y then (0 : ℝ) else 1) =
          (repChan ηY y w * (if majDec w = y then 0 else 1)) * ∑ z', bscN η z z' by
          rw [mul_sum]; exact sum_congr rfl fun z' _ => by ring,
          (bscN_isChannel h0 h1 m).sum_one, mul_one]

lemma binExp_one_sub (q : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binExp (1 - q) m f = binExp q m (fun k => f (m - k)) := by
  unfold binExp
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ (jumpRev_involutive m)) _ _
    (fun x => ?_)
  simp only [Function.Involutive.coe_toPerm]
  rw [bernProd_jumpRev]
  have := ones_jumpRev x
  rw [show m - ones (jumpRev x) = ones x by omega]

/-- **Theorem `thm:readout` (decoder errors)**: for odd `r`, `0 < η_Y < 1/2`, `0 ≤ η < 1/2`
and `1/2 < p < 1`, the explicit decoder has forward acceptance at least `1 - α` and reverse
acceptance at most `α`, where `α = d e^{-2r(1/2-η_Y)²} + P(Bin(m, p_η) ≤ m/2)`. -/
theorem readout_errors (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool)
    (hr : Odd r) {ηY η p : ℝ} (hY0 : 0 < ηY) (hY1 : ηY < 1 / 2) (h0 : 0 ≤ η) (h1 : η < 1 / 2)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    1 - (d * Real.exp (-2 * r * (1 / 2 - ηY) ^ 2) + lowerTail m (pEta η p)) ≤
      expect (chan (readChan ηY η) (ringP F h p m)) (readTest (r := r) F h) ∧
    expect (chan (readChan ηY η) (ringQ F h p m)) (readTest (r := r) F h) ≤
      d * Real.exp (-2 * r * (1 / 2 - ηY) ^ 2) + lowerTail m (pEta η p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨he1, he2, -⟩ := pEta_bounds h0 h1 hp hp1
  set δ := d * Real.exp (-2 * r * (1 / 2 - ηY) ^ 2)
  have hP := encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m)
  have hQ := encLaw_isProb F h jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) m)
  obtain ⟨eP, eQ⟩ := ring_noisy_laws F h η p m
  have hfail : ∀ y, endFail (r := r) ηY y ≤ δ := fun y => endpoint_failure hr hY0 hY1 y
  -- the noisy ideal test
  have hidP : expect (chan (payloadChan (bscN η)) (ringP F h p m)) (idealTest F h) =
      1 - lowerTail m (pEta η p) := by
    rw [eP]
    have := expect_ringP_ones F h (pEta η p) m (fun k => if m < 2 * k then 1 else 0)
    unfold idealTest
    rw [this, eq_sub_iff_add_eq]
    unfold lowerTail
    rw [← binExp_add]
    trans binExp (pEta η p) m (fun _ => 1)
    · congr 1; funext k; split_ifs <;> first | (exfalso; omega) | norm_num
    · exact binExp_one _ _
  have hidQ : expect (chan (payloadChan (bscN η)) (ringQ F h p m)) (idealTest F h) ≤
      lowerTail m (pEta η p) := by
    rw [eQ]
    have := expect_ringP_ones F h (1 - pEta η p) m (fun k => if m < 2 * k then 1 else 0)
    unfold ringP at this
    unfold ringQ idealTest
    rw [this, binExp_one_sub]
    unfold lowerTail
    refine binExp_mono (by linarith) he2.le m (fun k => ?_)
    dsimp only
    split_ifs <;> first | (exfalso; omega) | norm_num
  have key : ∀ (R : (Fin d → Bool) × (Fin m → Bool) → ℝ), IsProb R →
      |expect (chan (readChan ηY η) R) (readTest (r := r) F h) -
        expect (chan (payloadChan (bscN η)) R) (idealTest F h)| ≤ δ := by
    intro R hR
    rw [expect_chan, expect_chan]
    unfold expect
    rw [← sum_sub_distrib]
    calc _ ≤ ∑ x, |R x * ∑ wz, readChan (r := r) ηY η x wz * readTest F h wz -
          R x * ∑ r', payloadChan (bscN η) x r' * idealTest F h r'| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, R x * δ := sum_le_sum fun x _ => by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hR.nonneg x)]
          exact mul_le_mul_of_nonneg_left ((inner_split F h hY0.le (by linarith) h0
            (by linarith) x).trans (hfail x.1)) (hR.nonneg x)
      _ = δ := by rw [← sum_mul, hR.sum_one, one_mul]
  have k1 := abs_le.mp (key _ hP)
  have k2 := abs_le.mp (key _ hQ)
  unfold ringP at hidP k1
  unfold ringQ at hidQ k2
  unfold ringP
  unfold ringQ
  constructor <;> linarith [k1.1, k2.2]

lemma absCont_chan {α β : Type*} [Fintype α] [Fintype β] {C : α → β → ℝ} (hC : IsChannel C) {P Q : α → ℝ}
    (hQ : ∀ x, 0 < Q x) : AbsCont (chan C P) (chan C Q) := by
  intro y hy
  unfold chan at hy ⊢
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg (hQ x).le (hC.nonneg x y))).mp hy
  refine sum_eq_zero fun x hx => ?_
  have := h0 x hx
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (hQ x).ne'
  · rw [h, mul_zero]

/-- **Theorem `thm:readout`**: with the repetition-coded endpoint (odd `r`, `0 < η_Y < 1/2`) and
independent payload noise (`0 ≤ η < 1/2`), and `α = d e^{-2r(1/2-η_Y)²} + P(Bin(m,p_η) ≤ m/2)`:
* `α ≤ d e^{-2r(1/2-η_Y)²} + e^{-2m(p_η-1/2)²}` (so `α = e^{-Ω(m)}` for `r = Θ(m)` and
  polynomial `d`);
* `TV(P̂_m, Q̂_m) ≥ 1 - 2α`;
* if `0 < α < 1/2`, `D(P̂_m‖Q̂_m) ≥ (1-2α) log((1-α)/α)` (Eq. (binarylower));
* `D(P̂_m‖Q̂_m) ≤ m d(p)`;
* efficient indistinguishability is inherited by every test class whose composition with the
  readout channel lies in a class with small advantage (Eq. (compdpi)). -/
theorem readout_theorem (F : (Fin d → Bool) ≃ (Fin d → Bool)) (h : (Fin d → Bool) → Bool)
    (hr : Odd r) {ηY η p : ℝ} (hY0 : 0 < ηY) (hY1 : ηY < 1 / 2) (h0 : 0 ≤ η) (h1 : η < 1 / 2)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    let α := d * Real.exp (-2 * r * (1 / 2 - ηY) ^ 2) + lowerTail m (pEta η p)
    let Ph := chan (readChan (r := r) ηY η) (ringP F h p m)
    let Qh := chan (readChan (r := r) ηY η) (ringQ F h p m)
    α ≤ d * Real.exp (-2 * r * (1 / 2 - ηY) ^ 2) + Real.exp (-2 * m * (pEta η p - 1 / 2) ^ 2) ∧
    1 - 2 * α ≤ TV Ph Qh ∧
    (0 < α → α < 1 / 2 → (1 - 2 * α) * Real.log ((1 - α) / α) ≤ KL Ph Qh) ∧
    KL Ph Qh ≤ m * drate p ∧
    ∀ (T : Set ((Fin d → Bool) × (Fin m → Bool) → ℝ))
      (T' : Set ((Fin d → Fin r → Bool) × (Fin m → Bool) → ℝ)) (b : ℝ),
      AdvLE T (ringP F h p m) (ringQ F h p m) b →
      (∀ A ∈ T', (fun x => ∑ y, readChan ηY η x y * A y) ∈ T) → AdvLE T' Ph Qh b := by
  intro α Ph Qh
  have hp0 : 0 < p := by linarith
  obtain ⟨he1, he2, -⟩ := pEta_bounds h0 h1 hp hp1
  have hC := readChan_isChannel (d := d) (r := r) (m := m) hY0.le (by linarith : ηY ≤ 1) h0
    (by linarith : η ≤ 1)
  have hP := encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m)
  have hQ := encLaw_isProb F h jumpRev (bernProd_isProb (by linarith : (0:ℝ) ≤ 1 - p)
    (by linarith) m)
  have hPh : IsProb Ph := hP.chan hC
  have hQh : IsProb Qh := hQ.chan hC
  obtain ⟨e1, e2⟩ := readout_errors (r := r) (m := m) F h hr hY0 hY1 h0 h1 hp hp1
  have hA := readTest_isTest (r := r) (m := m) F h
  refine ⟨?_, ?_, fun ha0 ha1 => ?_, ?_, fun T T' b hb hclos => ?_⟩
  · simp only [α]
    linarith [lowerTail_le_hoeffding he1.le he2 m]
  · have := adv_le_TV hPh hQh hA
    unfold adv at this
    have := le_abs_self (expect Ph (readTest F h) - expect Qh (readTest F h))
    simp only [α, Ph, Qh] at *
    linarith
  · exact KL_ge_of_test_errors hPh hQh (absCont_chan hC (ringQ_pos F h hp0 hp1 m)) hA ha0 ha1
      e1 e2
  · rw [← (ring_statistics F h hp hp1 m).1]
    exact KL_chan_le hC hP.nonneg hQ.nonneg
      (fun r hr => absurd hr (ringQ_pos F h hp0 hp1 m r).ne')
  · exact advLE_chan hC _ _ T T' hb hclos

/-- The binary lower bound is linear in `-log α`: for `0 < α ≤ 1/4`,
`(1-2α) log((1-α)/α) ≥ (log(1/α) - log(4/3))/2`. Combined with `α ≤ e^{-cm}` this gives the
`Ω(m)` lower bound of Theorem `thm:readout`. -/
theorem binary_lower_linear {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1 / 4) :
    (Real.log (1 / α) - Real.log (4 / 3)) / 2 ≤ (1 - 2 * α) * Real.log ((1 - α) / α) := by
  have hl : Real.log ((1 - α) / α) = Real.log (1 / α) - Real.log (1 / (1 - α)) := by
    rw [Real.log_div (by linarith) h0.ne', one_div, one_div, Real.log_inv, Real.log_inv]; ring
  have h2 : Real.log (1 / (1 - α)) ≤ Real.log (4 / 3) :=
    Real.log_le_log (by apply div_pos <;> linarith) (by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have h3 : Real.log (4 / 3) ≤ Real.log (1 / α) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h0]; linarith)
  have h4 : 0 ≤ Real.log ((1 - α) / α) := by rw [hl]; linarith
  rw [hl] at h4 ⊢
  nlinarith

/-! ### The end-to-end logical reliability criterion -/

/-- **Eq. (transferadv) and its divergence consequence**: if imperfect records `P̃, Q̃` are within
`δ` in total variation of the ideal records (e.g. via a coupling, `TV_le_of_coupling`), then every
test's advantage changes by at most `2δ`; and an ideal test with both errors at most `e` has errors
at most `e + δ` on the imperfect records, so that for `0 < e + δ < 1/2`,
`D(P̃‖Q̃) ≥ (1 - 2(e+δ)) log((1-(e+δ))/(e+δ))`. -/
theorem logical_reliability {α : Type*} [Fintype α] {P Q P' Q' : α → ℝ} (hP : IsProb P)
    (hQ : IsProb Q) (hP' : IsProb P') (hQ' : IsProb Q') (hPQ' : AbsCont P' Q') {δ : ℝ}
    (h1 : TV P' P ≤ δ) (h2 : TV Q' Q ≤ δ) :
    (∀ A, IsTest A → adv P' Q' A ≤ adv P Q A + 2 * δ) ∧
    ∀ (A : α → ℝ), IsTest A → ∀ e : ℝ, 1 - e ≤ expect P A → expect Q A ≤ e →
      0 < e + δ → e + δ < 1 / 2 →
      (1 - 2 * (e + δ)) * Real.log ((1 - (e + δ)) / (e + δ)) ≤ KL P' Q' := by
  refine ⟨fun A hA => adv_transfer hP hQ hP' hQ' hA h1 h2, fun A hA e he1 he2 ha0 ha1 => ?_⟩
  have c1 := abs_le.mp (expect_close hP hP' hA h1)
  have c2 := abs_le.mp (expect_close hQ hQ' hA h2)
  exact KL_ge_of_test_errors hP' hQ' hPQ' hA ha0 ha1 (by linarith [c1.1]) (by linarith [c2.2])

end Arrow

end ReadoutPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Numerics
    ════════════════════════════════════════════════════════════════════ -/

section NumericsPart

/-!
# Section 13: exact checks of the reported numbers

The paper's finite examples are checked here exactly (rational arithmetic) or with rigorous
decimal enclosures for the logarithms (via the alternating-free series for
`log((1+x)/(1-x))` with an explicit remainder bound):

* one-bit toy (`m = 8`, `p = 3/4`): `D = 4 log 3 ≃ 4.39444915`, `TV = 0.85888671875`;
* causal toy (`ℓ = 3`, `m = 6`, `p = 3/4`): `D = 3 log 3 ≃ 3.29583687`, `TV = 0.79296875`;
* noisy check (`η = 0.13`, `m = 6`): `m d(p_η) = 2.22 log(137/63) ≃ 1.72459856`;
* ring fluctuation example (`m = 20`, `p = 0.65`): mean `20 d(0.65) = 6 log(13/7) ≃ 3.71424`;
* clocked example (`μ = 80`, `p = 3/4`): full-core value `80 d(3/4) = 40 log 3 ≃ 43.9444915`.

Monte-Carlo and plotted values in the paper (sampled means, sampled exponential averages,
figure curves, the overflow value at `L = 120`) are illustrations and are not re-derived here.
-/


open Finset Real

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Rigorous series enclosure: `log(1+x) - log(1-x)` differs from its degree-`n` Taylor
polynomial by at most `2|x|^{n+1}/(1-|x|)`. -/
lemma log_ratio_series {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |Real.log (1 + x) - Real.log (1 - x) -
      ∑ i ∈ range n, (x ^ (i + 1) - (-x) ^ (i + 1)) / (i + 1)| ≤
      2 * (|x| ^ (n + 1) / (1 - |x|)) := by
  have h1 := Real.abs_log_sub_add_sum_range_le hx n
  have h2 := Real.abs_log_sub_add_sum_range_le (show |-x| < 1 by rwa [abs_neg]) n
  rw [abs_neg, sub_neg_eq_add] at h2
  have e : Real.log (1 + x) - Real.log (1 - x) -
      ∑ i ∈ range n, (x ^ (i + 1) - (-x) ^ (i + 1)) / (i + 1) =
      (∑ i ∈ range n, (-x) ^ (i + 1) / (i + 1) + Real.log (1 + x)) -
      (∑ i ∈ range n, x ^ (i + 1) / (i + 1) + Real.log (1 - x)) := by
    simp only [sub_div, sum_sub_distrib]; ring
  rw [e]
  have := abs_sub (∑ i ∈ range n, (-x) ^ (i + 1) / (i + 1) + Real.log (1 + x))
      (∑ i ∈ range n, x ^ (i + 1) / (i + 1) + Real.log (1 - x))
  linarith

/-- A rigorous enclosure of `log 3` to within `10^{-11}`. -/
lemma log_three_enclosure : |Real.log 3 - 1.09861228866811| < 1e-11 := by
  have h := log_ratio_series (x := 1 / 2) (by norm_num [abs_of_pos]) 40
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← Real.log_div (by norm_num) (by norm_num), show (3 / 2 : ℝ) / (1 / 2) = 3 by norm_num] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_lt]
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

lemma drate_three_quarters : drate (3 / 4) = Real.log 3 / 2 := by
  unfold drate; norm_num; ring

/-! ### One-bit toy example (`m = 8`, `p = 3/4`) -/

theorem toy_onebit_values [Nonempty D] (F : D ≃ D) (h : D → Bool) :
    KL (ringP F h (3 / 4) 8) (ringQ F h (3 / 4) 8) = 4 * Real.log 3 ∧
    TV (ringP F h (3 / 4) 8) (ringQ F h (3 / 4) 8) = 0.85888671875 ∧
    |4 * Real.log 3 - 4.39444915| < 1e-8 := by
  obtain ⟨hKL, -, hTV, -⟩ := ring_statistics F h (p := 3 / 4) (by norm_num) (by norm_num) 8
  refine ⟨?_, ?_, ?_⟩
  · rw [hKL, drate_three_quarters]; push_cast; ring
  · rw [hTV, bayesErrBin_eq_sum]
    simp only [sum_range_succ, sum_range_zero, binPmf]
    norm_num [Nat.choose]
  · have := abs_lt.mp log_three_enclosure
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]

/-! ### Causal toy example (`ℓ = 3`, `m = 6`, `p = 3/4`) -/

theorem toy_causal_values [Nonempty D] (F : D ≃ D) (h : D → Bool) :
    KL (causalLaw F h 3 (bernProd (3 / 4) 6))
        (causalLaw F h 3 (fun x => bernProd (3 / 4) 6 (jumpRev x))) = 3 * Real.log 3 ∧
    TV (causalLaw F h 3 (bernProd (3 / 4) 6))
        (causalLaw F h 3 (fun x => bernProd (3 / 4) 6 (jumpRev x))) = 0.79296875 ∧
    |3 * Real.log 3 - 3.29583687| < 1e-8 := by
  obtain ⟨hKL, hTV, -⟩ := causal_concealment F h 3
    (bernProd_isProb (p := 3 / 4) (by norm_num) (by norm_num) 6)
  have e : (fun x => bernProd (3 / 4) 6 (jumpRev x)) = bernProd (1 - 3 / 4) 6 := by
    funext x; rw [bernProd_jumpRev]
  refine ⟨?_, ?_, ?_⟩
  · rw [hKL, e, KL_bernProd (by norm_num) (by norm_num), drate_three_quarters]; push_cast; ring
  · rw [hTV, e, TV_bernProd (by norm_num) (by norm_num), bayesErrBin_eq_sum]
    simp only [sum_range_succ, sum_range_zero, binPmf]
    norm_num [Nat.choose]
  · have := abs_lt.mp log_three_enclosure
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]

/-! ### Noisy check (`η = 0.13`, `m = 6`, `p = 3/4`) -/

theorem toy_noisy_value [Nonempty D] (F : D ≃ D) (h : D → Bool) :
    pEta 0.13 (3 / 4) = 0.685 ∧
    KL (chan (payloadChan (bscN 0.13)) (ringP F h (3 / 4) 6))
        (chan (payloadChan (bscN 0.13)) (ringQ F h (3 / 4) 6)) = 2.22 * Real.log (137 / 63) ∧
    |2.22 * Real.log (137 / 63) - 1.72459856| < 1e-8 := by
  have hpe : pEta 0.13 (3 / 4) = 0.685 := by unfold pEta; norm_num
  refine ⟨hpe, ?_, ?_⟩
  · rw [(payload_noise_law F h (η := 0.13) (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 6).1, hpe]
    unfold drate; norm_num; ring
  · have h := log_ratio_series (x := 37 / 100) (by norm_num [abs_of_pos]) 30
    rw [← Real.log_div (by norm_num) (by norm_num),
      show (1 + 37 / 100 : ℝ) / (1 - 37 / 100) = 137 / 63 by norm_num] at h
    simp only [sum_range_succ, sum_range_zero] at h
    norm_num [abs_of_pos] at h
    rw [abs_lt]
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]

/-! ### Fluctuation example (`m = 20`, `p = 0.65`) and clocked example (`μ = 80`) -/

theorem toy_fluctuation_mean :
    20 * drate 0.65 = 6 * Real.log (13 / 7) ∧ |6 * Real.log (13 / 7) - 3.71424| < 1e-5 := by
  refine ⟨by unfold drate; norm_num; ring, ?_⟩
  have h := log_ratio_series (x := 3 / 10) (by norm_num [abs_of_pos]) 16
  rw [← Real.log_div (by norm_num) (by norm_num),
    show (1 + 3 / 10 : ℝ) / (1 - 3 / 10) = 13 / 7 by norm_num] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_lt]
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem toy_clocked_full_core :
    80 * drate (3 / 4) = 40 * Real.log 3 ∧ |40 * Real.log 3 - 43.9444915| < 1e-7 := by
  refine ⟨by rw [drate_three_quarters]; ring, ?_⟩
  have := abs_lt.mp log_three_enclosure
  rw [abs_lt]; constructor <;> linarith [this.1, this.2]

/-- The exact mask-recovery probability at the paper's parameters (`64` mask bits, `p = 0.7`)
for `q = 1` training record is `0.7^64`, an instance of Eq. (reuseexact). -/
theorem toy_reuse_q1 : (1 - lowerTail 1 0.7) ^ 64 = (0.7 : ℝ) ^ 64 := by
  unfold lowerTail
  rw [binExp_succ, binExp_zero, binExp_zero]
  norm_num

end Arrow

end NumericsPart


/-! ════════════════════════════════════════════════════════════════════
    Part: WeakDrive
    ════════════════════════════════════════════════════════════════════ -/

section WeakDrivePart

/-!
# Appendix `app:weakdrive`: other statistical distances and the weak-driving crossover

* Eq. (renyiring): `D_α(P_m‖Q_m) = m/(α-1) · log[p^α(1-p)^{1-α} + (1-p)^α p^{1-α}]`.
* Eq. (hellinger): `ρ_m = [2√(p(1-p))]^m`, and Eq. (hellingertv): `1 - ρ_m ≤ TV ≤ √(1-ρ_m²)`.
* Eq. (weakexpansion): `p - 1/2 = a/4 + O(a³)` and `D = m a²/2 + O(m a⁴)`.
* The weak-driving regimes `a_m √m → λ`, `→ ∞`, `→ 0`; Eq. (weakthreshold); and the CLT limit
  Eq. (weakclt), which takes the binomial central limit theorem as an explicit hypothesis.
-/


open Finset Real Filter

namespace Arrow

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ### Rényi divergence and Hellinger affinity of the ring family -/

lemma rpow_pair {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (α : ℝ) :
    P ^ α * Q ^ (1 - α) = P * Real.exp ((α - 1) * Real.log (P / Q)) := by
  calc P ^ α * Q ^ (1 - α) = Real.exp (Real.log P * α + Real.log Q * (1 - α)) := by
        rw [Real.rpow_def_of_pos hP, Real.rpow_def_of_pos hQ, ← Real.exp_add]
    _ = Real.exp (Real.log P) * Real.exp ((α - 1) * (Real.log P - Real.log Q)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = _ := by rw [Real.exp_log hP, Real.log_div hP.ne' hQ.ne']

lemma renyi_bracket {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (α : ℝ) :
    (1 - p) * Real.exp (-(α - 1) * affinity p) + p * Real.exp ((α - 1) * affinity p) =
      p ^ α * (1 - p) ^ (1 - α) + (1 - p) ^ α * p ^ (1 - α) := by
  have hq : 0 < 1 - p := by linarith
  rw [rpow_pair hp0 hq, rpow_pair hq hp0]
  unfold affinity
  rw [show (1 - p) / p = (p / (1 - p))⁻¹ by rw [inv_div], Real.log_inv]
  ring_nf

/-- The Rényi sum of the encoded ring laws equals the binomial moment generating function. -/
theorem ring_renyi_sum [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) (α : ℝ) :
    ∑ r, ringP F h p m r ^ α * ringQ F h p m r ^ (1 - α) =
      (p ^ α * (1 - p) ^ (1 - α) + (1 - p) ^ α * p ^ (1 - α)) ^ m := by
  have hP := ringP_pos F h hp0 hp1 m
  have hQ := ringQ_pos F h hp0 hp1 m
  rw [← renyi_bracket hp0 hp1, ← mgf_sigma p (α - 1) m,
    ← expect_ringP_llr F h hp0 hp1 m (fun s => Real.exp ((α - 1) * s))]
  unfold expect llr
  exact sum_congr rfl fun r _ => rpow_pair (hP r) (hQ r) α

/-- **Eq. (renyiring)**: the Rényi divergence of order `α ≠ 1` of the encoded ring laws. -/
theorem ring_renyi [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (α : ℝ) :
    renyi α (ringP F h p m) (ringQ F h p m) =
      m / (α - 1) * Real.log (p ^ α * (1 - p) ^ (1 - α) + (1 - p) ^ α * p ^ (1 - α)) := by
  unfold renyi
  rw [ring_renyi_sum F h hp0 hp1, Real.log_pow]
  ring

/-- **Eq. (hellinger)**: `ρ_m = Σ √(P_m Q_m) = [2√(p(1-p))]^m`. -/
theorem ring_hellinger [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) :
    hellinger (ringP F h p m) (ringQ F h p m) = (2 * Real.sqrt (p * (1 - p))) ^ m := by
  have hP := ringP_pos F h hp0 hp1 m
  have hQ := ringQ_pos F h hp0 hp1 m
  have hq : 0 < 1 - p := by linarith
  unfold hellinger
  have e : ∀ r, Real.sqrt (ringP F h p m r * ringQ F h p m r) =
      ringP F h p m r ^ (1 / 2 : ℝ) * ringQ F h p m r ^ (1 - 1 / 2 : ℝ) := by
    intro r
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (hP r).le (hQ r).le]; norm_num
  simp_rw [e]
  rw [ring_renyi_sum F h hp0 hp1]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hp0.le hq.le]
  norm_num
  ring

/-- **Eq. (hellingertv)** for the ring family. -/
theorem ring_hellinger_TV [Nonempty D] (F : D ≃ D) (h : D → Bool) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (m : ℕ) :
    1 - (2 * Real.sqrt (p * (1 - p))) ^ m ≤ TV (ringP F h p m) (ringQ F h p m) ∧
    TV (ringP F h p m) (ringQ F h p m) ≤ Real.sqrt (1 - ((2 * Real.sqrt (p * (1 - p))) ^ m) ^ 2) := by
  rw [← ring_hellinger F h hp0 hp1]
  exact hellinger_TV_bounds (encLaw_isProb F h jumpRev (bernProd_isProb hp0.le hp1.le m))
    (encLaw_isProb F h jumpRev (bernProd_isProb (by linarith) (by linarith) m))

/-! ### Weak-driving expansions -/

/-- The jump bias for affinity `a`, `p = e^a/(1+e^a)`. -/
noncomputable def biasOf (a : ℝ) : ℝ := Real.exp a / (1 + Real.exp a)

lemma biasOf_bounds (a : ℝ) : 0 < biasOf a ∧ biasOf a < 1 := by
  unfold biasOf
  have := Real.exp_pos a
  exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

/-- **Eq. (weakexpansion)**, first part: `|p - 1/2 - a/4| ≤ |a|³` for `|a| ≤ 1`. -/
theorem bias_expansion {a : ℝ} (ha : |a| ≤ 1) : |biasOf a - 1 / 2 - a / 4| ≤ |a| ^ 3 := by
  have hb := Real.exp_bound ha (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at hb
  norm_num at hb
  set R := Real.exp a - (1 + a + a ^ 2 / 2)
  have he := Real.exp_pos a
  have hden : 0 < 4 * (Real.exp a + 1) := by positivity
  have e : biasOf a - 1 / 2 - a / 4 = (2 * R - a ^ 3 / 2 - a * R) / (4 * (Real.exp a + 1)) := by
    unfold biasOf
    simp only [R]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have ha3 : 0 ≤ |a| ^ 3 := by positivity
  have hR : |R| ≤ |a| ^ 3 * (2 / 9) := hb
  calc |2 * R - a ^ 3 / 2 - a * R| ≤ |2 * R| + |a ^ 3 / 2| + |a * R| := by
        have := abs_sub (2 * R - a ^ 3 / 2) (a * R)
        have := abs_sub (2 * R) (a ^ 3 / 2)
        linarith
    _ = 2 * |R| + |a| ^ 3 / 2 + |a| * |R| := by
        rw [abs_mul, abs_mul, abs_div, abs_pow]; norm_num
    _ ≤ 2 * (|a| ^ 3 * (2 / 9)) + |a| ^ 3 / 2 + 1 * (|a| ^ 3 * (2 / 9)) := by
        gcongr
    _ ≤ |a| ^ 3 * (4 * (Real.exp a + 1)) := by nlinarith

lemma two_bias_sub_one (a : ℝ) : 2 * biasOf a - 1 = Real.tanh (a / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  unfold biasOf
  have h1 := Real.exp_pos (a / 2)
  have h2 := Real.exp_pos (-(a / 2))
  have e : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(a / 2)) * Real.exp (a / 2) = 1 := by rw [← Real.exp_add]; simp
  rw [e]
  field_simp
  nlinarith [e2]

/-- **Eq. (weakexpansion)**, second part: `|d(p) - a²/2| ≤ 2a⁴` for `|a| ≤ 1`, so that
`D(P_m‖Q_m) = m d(p) = m a²/2 + O(m a⁴)`. -/
theorem drate_weak_expansion {a : ℝ} (ha : |a| ≤ 1) :
    |drate (biasOf a) - a ^ 2 / 2| ≤ 2 * a ^ 4 := by
  have hd : drate (biasOf a) = a * (2 * biasOf a - 1) := by
    unfold drate biasOf
    rw [show Real.exp a / (1 + Real.exp a) / (1 - Real.exp a / (1 + Real.exp a)) = Real.exp a by
      have := Real.exp_pos a; field_simp; ring, Real.log_exp]
    ring
  rw [hd, show a * (2 * biasOf a - 1) - a ^ 2 / 2 = 2 * a * (biasOf a - 1 / 2 - a / 4) by ring,
    abs_mul, abs_mul]
  have := bias_expansion ha
  have h4 : |a| ^ 4 = a ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  calc |2| * |a| * |biasOf a - 1 / 2 - a / 4| ≤ 2 * |a| * |a| ^ 3 := by
        rw [show |(2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * a ^ 4 := by rw [← h4]; ring

/-! ### Weak-driving regimes -/

section Regimes

variable {aSeq : ℕ → ℝ} (ha0 : Tendsto aSeq atTop (nhds 0))
include ha0

lemma eventually_abs_le_one : ∀ᶠ m in atTop, |aSeq m| ≤ 1 := by
  have := (continuous_abs.tendsto 0).comp ha0
  simp only [abs_zero] at this
  exact this.eventually (eventually_le_nhds (by norm_num))

/-- The divergence `m d(p_m)` is `m a_m²/2 + O(m a_m⁴)`; if `a_m √m → λ` then it converges to
`λ²/2`. -/
theorem weak_divergence_limit {lam : ℝ}
    (hlam : Tendsto (fun m : ℕ => aSeq m * Real.sqrt m) atTop (nhds lam)) :
    Tendsto (fun m : ℕ => m * drate (biasOf (aSeq m))) atTop (nhds (lam ^ 2 / 2)) := by
  have hsq : ∀ m : ℕ, (aSeq m * Real.sqrt m) ^ 2 = m * aSeq m ^ 2 := by
    intro m; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; ring
  have h1 : Tendsto (fun m : ℕ => m * aSeq m ^ 2 / 2) atTop (nhds (lam ^ 2 / 2)) := by
    have := (hlam.pow 2).div_const 2
    simpa [hsq] using this
  have h2 : Tendsto (fun m : ℕ => 2 * (m * aSeq m ^ 2) * aSeq m ^ 2) atTop (nhds 0) := by
    have := ((hlam.pow 2).const_mul 2).mul (ha0.pow 2)
    simp only [hsq] at this
    simpa using this
  refine tendsto_of_tendsto_of_dist (f₁ := fun m : ℕ => m * aSeq m ^ 2 / 2) h1 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ h2
  filter_upwards [eventually_abs_le_one ha0] with m hm
  rw [Real.dist_eq, show (m : ℝ) * aSeq m ^ 2 / 2 - m * drate (biasOf (aSeq m)) =
    -(m * (drate (biasOf (aSeq m)) - aSeq m ^ 2 / 2)) by ring, abs_neg, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg m)]
  have := drate_weak_expansion hm
  calc (m : ℝ) * |drate (biasOf (aSeq m)) - aSeq m ^ 2 / 2| ≤ m * (2 * aSeq m ^ 4) :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg m)
    _ = 2 * (m * aSeq m ^ 2) * aSeq m ^ 2 := by ring

/-- In the weak regime the divergence density per jump vanishes: `d(p_m) → 0`. -/
theorem weak_density_zero : Tendsto (fun m : ℕ => drate (biasOf (aSeq m))) atTop (nhds 0) := by
  have h1 : Tendsto (fun m : ℕ => aSeq m ^ 2 / 2) atTop (nhds 0) := by
    simpa using (ha0.pow 2).div_const 2
  have h2 : Tendsto (fun m : ℕ => 2 * aSeq m ^ 4) atTop (nhds 0) := by
    simpa using (ha0.pow 4).const_mul 2
  refine tendsto_of_tendsto_of_dist h1 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ h2)
  filter_upwards [eventually_abs_le_one ha0] with m hm
  rw [dist_comm, Real.dist_eq]
  exact drate_weak_expansion hm

/-- If `a_m √m → 0` the divergence vanishes. -/
theorem weak_divergence_zero
    (hlam : Tendsto (fun m : ℕ => aSeq m * Real.sqrt m) atTop (nhds 0)) :
    Tendsto (fun m : ℕ => m * drate (biasOf (aSeq m))) atTop (nhds 0) := by
  have := weak_divergence_limit ha0 hlam
  simpa using this

/-- If `a_m √m → ∞` (with `a_m → 0⁺`), the divergence diverges and the optimal orientation error
tends to zero (Hoeffding). -/
theorem weak_strong_regime (hpos : ∀ m, 0 < aSeq m)
    (hlam : Tendsto (fun m : ℕ => aSeq m * Real.sqrt m) atTop atTop) :
    Tendsto (fun m : ℕ => m * drate (biasOf (aSeq m))) atTop atTop ∧
    Tendsto (fun m : ℕ => bayesErrBin m (biasOf (aSeq m))) atTop (nhds 0) := by
  have hsq : ∀ m : ℕ, (aSeq m * Real.sqrt m) ^ 2 = m * aSeq m ^ 2 := by
    intro m; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; ring
  have hm2 : Tendsto (fun m : ℕ => m * aSeq m ^ 2) atTop atTop := by
    have := (tendsto_pow_atTop (two_ne_zero)).comp hlam
    exact this.congr fun m => by simp only [Function.comp]; exact hsq m
  have ev := eventually_abs_le_one ha0
  have hsmall : ∀ᶠ m in atTop, aSeq m ^ 2 ≤ 1 / 8 := by
    have := (ha0.pow 2).eventually (eventually_le_nhds (show (0 : ℝ) ^ 2 < 1 / 8 by norm_num))
    exact this
  -- lower bounds: d(p) ≥ a²/2 - 2a⁴ ≥ a²/4, and p - 1/2 ≥ a/4 - a³ ≥ a/8
  have hd : ∀ᶠ m : ℕ in atTop, m * aSeq m ^ 2 / 4 ≤ m * drate (biasOf (aSeq m)) := by
    filter_upwards [ev, hsmall] with m hm hs
    have := abs_le.mp (drate_weak_expansion hm)
    have : aSeq m ^ 2 / 4 ≤ drate (biasOf (aSeq m)) := by nlinarith [sq_nonneg (aSeq m)]
    have hmn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  refine ⟨tendsto_atTop_mono' atTop hd (hm2.atTop_div_const (by norm_num)), ?_⟩
  have hb : ∀ᶠ m : ℕ in atTop, aSeq m / 8 ≤ biasOf (aSeq m) - 1 / 2 := by
    filter_upwards [ev, hsmall] with m hm hs
    have h1 := abs_le.mp (bias_expansion hm)
    rw [abs_of_pos (hpos m)] at h1
    have : aSeq m ^ 3 ≤ aSeq m / 8 := by nlinarith [hpos m]
    linarith [h1.1]
  have hexp : Tendsto (fun m : ℕ => Real.exp (-2 * m * (aSeq m / 8) ^ 2)) atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun m : ℕ => (m * aSeq m ^ 2) / 32) atTop atTop :=
      hm2.atTop_div_const (by norm_num)
    refine (tendsto_neg_atTop_atBot.comp this).congr fun m => ?_
    simp only [Function.comp]; ring
  refine squeeze_zero' ?_ ?_ hexp
  · exact Eventually.of_forall fun m => bayesErrBin_nonneg (biasOf_bounds _).1.le
      (biasOf_bounds _).2.le m
  · filter_upwards [hb] with m hbm
    have hp : 1 / 2 ≤ biasOf (aSeq m) := by linarith [hpos m]
    refine (bayesErrBin_le_hoeffding hp (biasOf_bounds _).2 m).trans ?_
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ aSeq m / 8 := by linarith [hpos m]
    have : (aSeq m / 8) ^ 2 ≤ (biasOf (aSeq m) - 1 / 2) ^ 2 := pow_le_pow_left₀ h0 hbm 2
    have hmn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

end Regimes

/-- **Eq. (weakthreshold)**: the centered decision threshold
`(m/2 - m p_m)/√(m p_m(1-p_m))` equals `-a_m√m/2 + o(1)` when `a_m → 0⁺` and `a_m√m → λ`. -/
theorem weak_threshold {aSeq : ℕ → ℝ} (ha0 : Tendsto aSeq atTop (nhds 0)) (hpos : ∀ m, 0 < aSeq m)
    {lam : ℝ} (hlam : Tendsto (fun m : ℕ => aSeq m * Real.sqrt m) atTop (nhds lam)) :
    Tendsto (fun m : ℕ => (m / 2 - m * biasOf (aSeq m)) /
        Real.sqrt (m * biasOf (aSeq m) * (1 - biasOf (aSeq m))) -
      (-(aSeq m * Real.sqrt m) / 2)) atTop (nhds 0) := by
  set p := fun m => biasOf (aSeq m)
  -- (p - 1/2)/a → 1/4
  have hratio : Tendsto (fun m => (p m - 1 / 2) / aSeq m) atTop (nhds (1 / 4)) := by
    have hsq : Tendsto (fun m => aSeq m ^ 2) atTop (nhds 0) := by simpa using ha0.pow 2
    refine tendsto_of_tendsto_of_dist (f₁ := fun _ => (1 : ℝ) / 4) tendsto_const_nhds ?_
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hsq
    filter_upwards [eventually_abs_le_one ha0] with m hm
    rw [Real.dist_eq, show (1 : ℝ) / 4 - (p m - 1 / 2) / aSeq m =
      -((p m - 1 / 2 - aSeq m / 4) / aSeq m) by field_simp [(hpos m).ne']; ring, abs_neg,
      abs_div, abs_of_pos (hpos m), div_le_iff₀ (hpos m)]
    have := bias_expansion hm
    rw [abs_of_pos (hpos m)] at this
    calc _ ≤ aSeq m ^ 3 := this
      _ = aSeq m ^ 2 * aSeq m := by ring
  -- p → 1/2 and √(p(1-p)) → 1/2
  have hp : Tendsto p atTop (nhds (1 / 2)) := by
    have := (hratio.mul ha0).add_const (1 / 2)
    rw [mul_zero, zero_add] at this
    refine this.congr fun m => ?_
    field_simp [(hpos m).ne']; ring
  have hs : Tendsto (fun m => Real.sqrt (p m * (1 - p m))) atTop (nhds (1 / 2)) := by
    have := (hp.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).sqrt
    rw [show Real.sqrt (1 / 2 * (1 - 1 / 2)) = 1 / 2 by
      rw [show (1 : ℝ) / 2 * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)] at this
    exact this
  have hlim := hlam.mul (((hratio.div hs (by norm_num)).sub_const (1 / 2)))
  rw [show (1 : ℝ) / 4 / (1 / 2) - 1 / 2 = 0 by norm_num, mul_zero] at hlim
  have hlim' := hlim.neg
  rw [neg_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hb0, hb1⟩ := biasOf_bounds (aSeq m)
  have hpq : 0 < p m * (1 - p m) := mul_pos hb0 (by linarith)
  have hsq : Real.sqrt (m * p m * (1 - p m)) = Real.sqrt m * Real.sqrt (p m * (1 - p m)) := by
    rw [mul_assoc, Real.sqrt_mul hmpos.le]
  simp only [p, Pi.div_apply] at hsq hpq ⊢
  rw [hsq]
  have hm' : (m : ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hmpos.le).symm
  have h1 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have h2 : 0 < Real.sqrt (biasOf (aSeq m) * (1 - biasOf (aSeq m))) := Real.sqrt_pos.mpr hpq
  generalize Real.sqrt m = sm at hm' h1 ⊢
  generalize Real.sqrt (biasOf (aSeq m) * (1 - biasOf (aSeq m))) = sq at h2 ⊢
  rw [hm']
  field_simp [(hpos m).ne']
  ring

/-- **Eq. (weakclt)**, conditional on the binomial central limit theorem: if
`e_m(p_m) → Φ(-λ/2)` (the CLT statement, taken as a hypothesis) for a distribution function
with `Φ(-x) = 1 - Φ(x)`, then `TV(P_m, Q_m) → 2Φ(λ/2) - 1`. -/
theorem weak_clt_TV [Nonempty D] (F : D ≃ D) (h : D → Bool) {aSeq : ℕ → ℝ}
    (hpos : ∀ m, 0 < aSeq m) (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = 1 - Φ x) {lam : ℝ}
    (hclt : Tendsto (fun m : ℕ => bayesErrBin m (biasOf (aSeq m))) atTop (nhds (Φ (-lam / 2)))) :
    Tendsto (fun m : ℕ => TV (ringP F h (biasOf (aSeq m)) m) (ringQ F h (biasOf (aSeq m)) m))
      atTop (nhds (2 * Φ (lam / 2) - 1)) := by
  have hTV : ∀ m : ℕ, TV (ringP F h (biasOf (aSeq m)) m) (ringQ F h (biasOf (aSeq m)) m) =
      1 - 2 * bayesErrBin m (biasOf (aSeq m)) := by
    intro m
    have hb := biasOf_bounds (aSeq m)
    have hhalf : 1 / 2 < biasOf (aSeq m) := by
      have := bias_gt_half (hpos m); unfold biasOf; exact this
    exact (ring_statistics F h hhalf hb.2 m).2.2.1
  simp_rw [hTV]
  have := (hclt.const_mul 2).const_sub 1
  rw [show -lam / 2 = -(lam / 2) by ring, hΦ] at this
  convert this using 2
  ring

end Arrow

end WeakDrivePart


/-! ════════════════════════════════════════════════════════════════════
    Part: Kolmogorov
    ════════════════════════════════════════════════════════════════════ -/

section KolmogorovPart

/-!
# Section 11: description length is not decoding time

We model a description method abstractly: `U l p` is the (possibly undefined) output of the
program `p ∈ {0,1}^l`. An object `y` is *describable within `k` bits* if some program of length
`≤ k` outputs it; this is `K_U(y) ≤ k` for the description complexity of `U` (plain or prefix:
the counting argument only uses that there are at most `2^l` programs of length `l`).

* Eq. (complexitycount): for the uniformly distributed endpoint `Y ∈ {0,1}^d`,
  `P[K(Y) < d - c] < 2^{-c}`.
* Eq. (kinvariance): if a bijection `E` and its inverse can each be applied to a program's
  output with additive overhead `c_E` (the computable-composition property of a universal
  machine, taken as a hypothesis), then descriptions of `x` and `E x` differ in length by at most
  a constant.
-/


open Finset

namespace Arrow

/-- `y` has a description of length `< k` under the description method `U`. -/
def DescLT {Y : Type*} (U : ∀ l : ℕ, (Fin l → Bool) → Option Y) (y : Y) (k : ℕ) : Prop :=
  ∃ l < k, ∃ p : Fin l → Bool, U l p = some y

/-- `y` has a description of length `≤ k` under `U`. -/
def DescLE {Y : Type*} (U : ∀ l : ℕ, (Fin l → Bool) → Option Y) (y : Y) (k : ℕ) : Prop :=
  ∃ l ≤ k, ∃ p : Fin l → Bool, U l p = some y

lemma geom_two_sum (k : ℕ) : ∑ l ∈ range k, 2 ^ l = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- **Counting argument**: fewer than `2^k` objects have descriptions of length `< k`. -/
theorem card_descLT_lt {Y : Type*} [Fintype Y] [DecidableEq Y]
    (U : ∀ l : ℕ, (Fin l → Bool) → Option Y) (k : ℕ) [DecidablePred (fun y => DescLT U y k)] :
    (univ.filter (fun y => DescLT U y k)).card < 2 ^ k := by
  classical
  have hsub : univ.filter (fun y => DescLT U y k) ⊆
      (range k).biUnion (fun l => univ.filter (fun y => ∃ p : Fin l → Bool, U l p = some y)) := by
    intro y hy
    obtain ⟨l, hl, p, hp⟩ := (mem_filter.mp hy).2
    exact mem_biUnion.mpr ⟨l, mem_range.mpr hl, mem_filter.mpr ⟨mem_univ _, p, hp⟩⟩
  have hcard : ∀ l, (univ.filter (fun y => ∃ p : Fin l → Bool, U l p = some y)).card ≤ 2 ^ l := by
    intro l
    calc _ ≤ (univ : Finset (Fin l → Bool)).card := by
          refine card_le_card_of_injOn (fun y => if h : ∃ p : Fin l → Bool, U l p = some y
            then h.choose else fun _ => false) (fun _ _ => mem_univ _) ?_
          intro y1 hy1 y2 hy2 he
          have h1 := (mem_filter.mp hy1).2
          have h2 := (mem_filter.mp hy2).2
          simp only [h1, h2, dite_true] at he
          have e1 := h1.choose_spec
          have e2 := h2.choose_spec
          rw [he] at e1
          exact Option.some_injective _ (e1.symm.trans e2)
      _ = 2 ^ l := by simp
  calc _ ≤ ((range k).biUnion
        (fun l => univ.filter (fun y => ∃ p : Fin l → Bool, U l p = some y))).card := card_le_card hsub
    _ ≤ ∑ l ∈ range k, (univ.filter (fun y => ∃ p : Fin l → Bool, U l p = some y)).card :=
        card_biUnion_le
    _ ≤ ∑ l ∈ range k, 2 ^ l := sum_le_sum fun l _ => hcard l
    _ = 2 ^ k - 1 := geom_two_sum k
    _ < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos k) one_pos

/-- **Eq. (complexitycount)**: if the endpoint `Y` is uniform on `{0,1}^d` (as it is, `F` being
a permutation of uniformly random seeds), then for every description method and every `c ≤ d`,
`P[K(Y) < d - c] < 2^{-c}`. -/
theorem complexity_count {d : ℕ} (U : ∀ l : ℕ, (Fin l → Bool) → Option (Fin d → Bool)) {c : ℕ}
    (hc : c ≤ d) :
    expect (unif (Fin d → Bool)) (fun y => by
      classical exact if DescLT U y (d - c) then 1 else 0) < (1 / 2 : ℝ) ^ c := by
  classical
  have hcard := card_descLT_lt U (d - c)
  have hD : (Fintype.card (Fin d → Bool) : ℝ) = 2 ^ d := by simp
  unfold expect unif
  rw [hD]
  rw [← mul_sum, sum_boole]
  have hlt : ((univ.filter (fun y => DescLT U y (d - c))).card : ℝ) < 2 ^ (d - c) := by
    exact_mod_cast hcard
  have h2 : (2 : ℝ) ^ d = 2 ^ (d - c) * 2 ^ c := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  rw [h2, one_div_pow]
  have hpos : (0 : ℝ) < 2 ^ (d - c) := by positivity
  have hpos2 : (0 : ℝ) < 2 ^ c := by positivity
  rw [one_div, mul_comm, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- **Eq. (kinvariance)**: suppose post-composition with `E` and with `E⁻¹` can be realized on
programs with additive length overheads `c₁` and `c₂` (the composition property of a universal
description method with the uniformly computable encoder and its exhaustive-search inverse).
Then `K(E x) ≤ K(x) + c₁` and `K(x) ≤ K(E x) + c₂`. -/
theorem complexity_invariance {X : Type*} (U : ∀ l : ℕ, (Fin l → Bool) → Option X) (E : X ≃ X)
    (c₁ c₂ : ℕ)
    (hE : ∀ l (p : Fin l → Bool), ∃ p' : Fin (l + c₁) → Bool, U (l + c₁) p' = (U l p).map E)
    (hEinv : ∀ l (p : Fin l → Bool), ∃ p' : Fin (l + c₂) → Bool,
      U (l + c₂) p' = (U l p).map E.symm) (x : X) (k : ℕ) :
    (DescLE U x k → DescLE U (E x) (k + c₁)) ∧ (DescLE U (E x) k → DescLE U x (k + c₂)) := by
  refine ⟨fun ⟨l, hl, p, hp⟩ => ?_, fun ⟨l, hl, p, hp⟩ => ?_⟩
  · obtain ⟨p', hp'⟩ := hE l p
    exact ⟨l + c₁, by omega, p', by rw [hp', hp]; rfl⟩
  · obtain ⟨p', hp'⟩ := hEinv l p
    exact ⟨l + c₂, by omega, p', by rw [hp', hp]; simp⟩

end Arrow

end KolmogorovPart


/-! ════════════════════════════════════════════════════════════════════
    Part: Algorithms
    ════════════════════════════════════════════════════════════════════ -/

section AlgorithmsPart

/-!
# Appendix `app:algorithms`: sampling algorithms and finite precision

* The exact digital sampler for `p = 3/4`: two fair bits, output `0` only if both are `0`.
* The block construction's samplers are the defining push-forwards (`encLaw`); sampling the
  reverse law replaces `j` by `θ_m j` before encoding (`ringQ_eq`).
* Rounding a finite law to a dyadic grid changes total variation by at most `N · 2^{-b}/2`, and a
  sampler within total variation `δ` changes every advantage by at most `2δ`.
-/


open Finset Real

namespace Arrow

/-- **Exact digital sampler for `p = 3/4`**: drawing two fair bits and outputting `0` only when
both are `0` produces exactly `Ber(3/4)`. -/
theorem sampler_three_quarters :
    push (fun z : Bool × Bool => z.1 || z.2) (unif (Bool × Bool)) = bern (3 / 4) := by
  funext b
  unfold push unif bern
  have h3 : (univ.filter fun x : Bool × Bool => x.1 = true ∨ x.2 = true).card = 3 := by decide
  have h1 : (univ.filter fun x : Bool × Bool => x.1 = false ∧ x.2 = false).card = 1 := by decide
  cases b
  · simp [h1]; norm_num
  · simp [h3]; norm_num

/-- The reverse sampler: encoding `θ_m j` instead of `j` samples the reversed law. -/
theorem reverse_sampler {D : Type*} [Fintype D] [DecidableEq D] (F : D ≃ D) (h : D → Bool)
    (p : ℝ) (m : ℕ) :
    ringQ F h p m = encLaw F h jumpRev (fun j => bernProd p m (jumpRev j)) :=
  ringQ_eq F h p m

/-- **Grid rounding**: if each of the probabilities of a finite law is approximated to within
`ε`, the total-variation error is at most `|α| ε / 2`. -/
theorem TV_le_of_pointwise {α : Type*} [Fintype α] {P Q : α → ℝ} {ε : ℝ}
    (h : ∀ x, |P x - Q x| ≤ ε) : TV P Q ≤ Fintype.card α * ε / 2 := by
  unfold TV
  have : ∑ x, |P x - Q x| ≤ ∑ _x : α, ε := sum_le_sum fun x _ => h x
  simp only [sum_const, card_univ, nsmul_eq_mul] at this
  linarith

/-- **Negligible sampler approximation**: a distinguisher's advantage on approximate samplers
within total variation `δ` of the ideal laws is at least its ideal advantage minus `2δ`. -/
theorem adv_approx_sampler {α : Type*} [Fintype α] {P Q P' Q' : α → ℝ} (hP : IsProb P)
    (hQ : IsProb Q) (hP' : IsProb P') (hQ' : IsProb Q') {A : α → ℝ} (hA : IsTest A) {δ : ℝ}
    (h1 : TV P' P ≤ δ) (h2 : TV Q' Q ≤ δ) : adv P Q A - 2 * δ ≤ adv P' Q' A := by
  have h1' : TV P P' ≤ δ := by unfold TV at *; simp_rw [abs_sub_comm (P _)]; exact h1
  have h2' : TV Q Q' ≤ δ := by unfold TV at *; simp_rw [abs_sub_comm (Q _)]; exact h2
  have := adv_transfer hP' hQ' hP hQ hA h1' h2'
  linarith

end Arrow

end AlgorithmsPart


/-! ════════════════════════════════════════════════════════════════════
    Part: NoGo
    ════════════════════════════════════════════════════════════════════ -/

section NoGoPart

/-!
# Section 3: why an ordinary observed Markov chain does not suffice

**Proposition `prop:nogo`**. For a fully observed discrete-time Markov path the likelihood is the
product Eq. (markovlikelihood) of polynomially many rational factors. We formalize:

* the Markov path law `ρ₀(x₀) ∏ K_i(x_{i-1}, x_i)` and its normalization;
* the exact-arithmetic decision: with factors written as integer fractions of bit length `≤ B`,
  the two products are fractions whose numerators and denominators have bit length `≤ (m+1)B`,
  and the likelihood-ratio decision `Q(x) < P(x)` is the integer comparison `C·B' < A·D'`;
* the conclusion: if the likelihood-ratio test belongs to the efficient class (as the exact
  computation shows), a family with unrestricted advantage `TV → 1` cannot have efficient
  advantage tending to zero.
-/


open Finset Filter

namespace Arrow

/-! ### Markov path laws -/

/-- The law of a Markov path `(x₀, …, x_m)`, Eq. (markovlikelihood). -/
noncomputable def markovLaw {S : Type*} {m : ℕ} (ρ0 : S → ℝ) (K : Fin m → S → S → ℝ) :
    (Fin (m + 1) → S) → ℝ :=
  fun x => ρ0 (x 0) * ∏ i : Fin m, K i (x i.castSucc) (x i.succ)

lemma markovLaw_snoc {S : Type*} {m : ℕ} (ρ0 : S → ℝ) (K : Fin (m + 1) → S → S → ℝ)
    (y : Fin (m + 1) → S) (s : S) :
    markovLaw ρ0 K (Fin.snoc y s) =
      markovLaw ρ0 (fun i => K i.castSucc) y * K (Fin.last m) (y (Fin.last m)) s := by
  unfold markovLaw
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc y s : Fin (m + 2) → S) 0 = y 0 := by
    rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl, Fin.snoc_castSucc]
  have h1 : ∀ i : Fin m, (Fin.snoc y s : Fin (m + 2) → S) i.castSucc.succ = y i.succ := by
    intro i
    rw [show i.castSucc.succ = i.succ.castSucc from (Fin.succ_castSucc i).symm, Fin.snoc_castSucc]
  simp only [Fin.snoc_castSucc, h0, h1, Fin.succ_last, Fin.snoc_last]
  ring

/-- Markov path laws are probability laws. -/
theorem markovLaw_isProb {S : Type*} [Fintype S] {ρ0 : S → ℝ} (hρ : IsProb ρ0) :
    ∀ {m : ℕ} {K : Fin m → S → S → ℝ}, (∀ i, IsChannel (K i)) → IsProb (markovLaw ρ0 K)
  | 0, K, _ => by
    refine ⟨fun x => ?_, ?_⟩
    · unfold markovLaw; simp [hρ.nonneg]
    · unfold markovLaw
      simp only [Finset.univ_eq_empty, prod_empty, mul_one]
      rw [← hρ.sum_one]
      exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ (fun x => rfl)
  | m + 1, K, hK => by
    have ih := markovLaw_isProb hρ (m := m) (K := fun i => K i.castSucc) (fun i => hK _)
    refine ⟨fun x => ?_, ?_⟩
    · unfold markovLaw
      exact mul_nonneg (hρ.nonneg _) (prod_nonneg fun i _ => (hK i).nonneg _ _)
    · rw [← (Fin.snocEquiv (fun _ : Fin (m + 2) => S)).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, markovLaw_snoc]
      rw [← ih.sum_one]
      refine sum_congr rfl fun y _ => ?_
      rw [← mul_sum, (hK _).sum_one, mul_one]

/-! ### Exact rational evaluation -/

/-- A product of integer fractions is the fraction of the products, with bit lengths adding up:
if every `|a_i| ≤ 2^B` and `0 < b_i ≤ 2^B`, the product of `k` such fractions is `A/B'` with
`|A| ≤ 2^{kB}` and `0 < B' ≤ 2^{kB}`. -/
theorem prod_fractions {k : ℕ} (a : Fin k → ℤ) (b : Fin k → ℤ) {B : ℕ}
    (ha : ∀ i, |a i| ≤ 2 ^ B) (hb : ∀ i, 0 < b i ∧ b i ≤ 2 ^ B) :
    (∏ i, ((a i : ℝ) / b i)) = (∏ i, a i : ℤ) / (∏ i, b i : ℤ) ∧
    |∏ i, a i| ≤ 2 ^ (k * B) ∧ 0 < ∏ i, b i ∧ ∏ i, b i ≤ 2 ^ (k * B) := by
  refine ⟨?_, ?_, prod_pos fun i _ => (hb i).1, ?_⟩
  · push_cast; rw [prod_div_distrib]
  · rw [abs_prod]
    calc ∏ i, |a i| ≤ ∏ _i : Fin k, (2 : ℤ) ^ B :=
          prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ha i)
      _ = 2 ^ (k * B) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  · calc ∏ i, b i ≤ ∏ _i : Fin k, (2 : ℤ) ^ B :=
          prod_le_prod (fun i _ => (hb i).1.le) (fun i _ => (hb i).2)
      _ = 2 ^ (k * B) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- The likelihood-ratio decision `Q < P` between two fractions with positive denominators is the
integer cross-multiplication comparison. -/
theorem lr_decision_cross {A B C D : ℤ} (hB : 0 < B) (hD : 0 < D) :
    ((C : ℝ) / D < (A : ℝ) / B) ↔ C * B < A * D := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_lt_div_iff₀ hD' hB']
  exact_mod_cast Iff.rfl

/-! ### The no-go conclusion -/

/-- **Proposition `prop:nogo`** (decision-theoretic content): if the exact likelihood-ratio test
of the full-path laws belongs to the efficient class `T_n` for every `n` (which the exact
rational evaluation above provides for polynomial-size Markov data), then a family whose
unrestricted advantage `TV(P_n, Q_n)` tends to `1` cannot have efficient advantage bounds `ε_n`
tending to `0`. -/
theorem nogo_markov (α : ℕ → Type*) [∀ n, Fintype (α n)] (P Q : ∀ n, α n → ℝ)
    (hP : ∀ n, IsProb (P n)) (hQ : ∀ n, IsProb (Q n)) (T : ∀ n, Set (α n → ℝ))
    (hT : ∀ n, lrTest (P n) (Q n) ∈ T n) (hTV : Tendsto (fun n => TV (P n) (Q n)) atTop (nhds 1))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) (hadv : ∀ n, AdvLE (T n) (P n) (Q n) (ε n)) :
    False := by
  have hle : ∀ n, TV (P n) (Q n) ≤ ε n := by
    intro n
    have := hadv n _ (hT n) (lrTest_isTest _ _)
    unfold adv at this
    rw [expect_lrTest (hP n) (hQ n)] at this
    exact (le_abs_self _).trans this
  have := le_of_tendsto_of_tendsto hTV hε (Eventually.of_forall hle)
  norm_num at this

/-- **Coordinate-change criterion**: tests transport exactly along a recoding `E`: the advantage of
`A` on the recoded laws equals that of `A ∘ E` on the original laws (and, for a bijection, of
`B ∘ E⁻¹` in the other direction). Hence if both `E` and `E⁻¹` are efficient, a recoding cannot
create a computational separation. -/
theorem recoding_transport {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (E : α → β)
    (P Q : α → ℝ) (A : β → ℝ) : adv (push E P) (push E Q) A = adv P Q (fun x => A (E x)) := by
  unfold adv; rw [expect_push, expect_push]

end Arrow

end NoGoPart
