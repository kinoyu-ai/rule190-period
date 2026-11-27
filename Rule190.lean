/-!
# Exact Eventual Period of Elementary Cellular Automaton Rule 190 on a Cyclic Ring (OEIS A334501)

This file gives a self-contained, dependency-free Lean 4 proof resolving the open conjectures
on OEIS A334501 ("Eventual period of a single cell in rule 190 cellular automaton in a cyclic
universe of width n", N. J. A. Sloane, May 2020; conjectures by Colin Barker, May 9, 2020).

## Main Results

For every positive ring width `n ≥ 1`, let `evolve n : Nat → Config n` be the orbit of
Elementary Cellular Automaton Rule 190 on a cyclic ring of width `n` started from a single
live cell at index `0`. Define:

    a334501 n :=
      if n ≤ 3 then 1
      else if n % 4 = 0 then 4
      else n

We prove:
1. `eventualPeriod_global`: For every `n ≥ 1`, `a334501 n` is the exact (minimal) eventual
   period of the global configuration orbit `evolve n`.
2. `eventualPeriod_cell`: For every `n ≥ 1` and every cell `i : Fin n`, `a334501 n` is also
   the exact (minimal) eventual period of the individual cell trajectory `t ↦ evolve n t i`.
3. `colin_barker_gf_identity`: For every `n : Nat`, the coefficient of `x^n` in
   `(1 - 2x^4 + x^8) * ∑_{k ≥ 1} a334501(k) x^k` matches Colin Barker's conjectured numerator
   `x*(1 + x + x^2 + 4x^3 + 3x^4 + 4x^5 + 5x^6 - 4x^7 - x^9 - 2x^10)`.
4. `colin_barker_recurrence` & `colin_barker_n_gt_8_counterexamples`: The recurrence
   `a(n) = 2*a(n-4) - a(n-8)` holds for all `n ≥ 12`, while `n = 10` and `n = 11` are
   counterexamples to the `n > 8` bound stated in OEIS A334501.
-/

namespace Rule190

/-- Standard Wolfram Elementary Cellular Automaton lookup from a rule number `0..255`. -/
def wolframRule (rule : Nat) (l c r : Bool) : Bool :=
  let idx := (if l then 4 else 0) + (if c then 2 else 0) + (if r then 1 else 0)
  (rule / 2 ^ idx) % 2 == 1

/-- Elementary Cellular Automaton Rule 190 (`10111110₂`). -/
def rule190 (l c r : Bool) : Bool :=
  wolframRule 190 l c r

/-- Equivalent boolean characterization of Rule 190: output is `true` iff `r` is `true` or `l ≠ c`. -/
theorem rule190_eq (l c r : Bool) : rule190 l c r = (r || (l != c)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-- A configuration on a cyclic ring of width `n`. -/
abbrev Config (n : Nat) := Fin n → Bool

/-- Left neighbor index `(i - 1) mod n` on the cyclic ring. -/
def leftIdx {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- Right neighbor index `(i + 1) mod n` on the cyclic ring. -/
def rightIdx {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

theorem leftIdx_val {n : Nat} (i : Fin n) :
    (leftIdx i).val = if i.val = 0 then n - 1 else i.val - 1 := by
  simp only [leftIdx]
  have hi := i.isLt
  split
  · next h =>
    have : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h]; exact this
  · next h =>
    have h1 : i.val + n - 1 = (i.val - 1) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem rightIdx_val {n : Nat} (i : Fin n) :
    (rightIdx i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  simp only [rightIdx]
  have hi := i.isLt
  split
  · next h => exact Nat.mod_eq_of_lt h
  · next h =>
    have h1 : i.val + 1 = n := by omega
    rw [h1, Nat.mod_self]

theorem leftIdx_rightIdx {n : Nat} (i : Fin n) : leftIdx (rightIdx i) = i := by
  apply Fin.ext
  rw [leftIdx_val, rightIdx_val]
  have hi := i.isLt
  split <;> split <;> omega

theorem rightIdx_leftIdx {n : Nat} (i : Fin n) : rightIdx (leftIdx i) = i := by
  apply Fin.ext
  rw [rightIdx_val, leftIdx_val]
  have hi := i.isLt
  split <;> split <;> omega

/-- One synchronous step of Rule 190 on the cyclic ring of width `n`. -/
def step {n : Nat} (s : Config n) : Config n :=
  fun i => rule190 (s (leftIdx i)) (s i) (s (rightIdx i))

/-- Initial configuration with a single live cell at position `0`. -/
def singleCell (n : Nat) : Config n :=
  fun i => decide (i.val = 0)

/-- Time evolution of Rule 190 starting from `singleCell n`. -/
def evolve (n : Nat) : Nat → Config n
  | 0 => singleCell n
  | t + 1 => step (evolve n t)

/-- Cyclic left shift by `k` cells: `(shiftLeft k s) i = s ((i + k) mod n)`. -/
def shiftLeft {n : Nat} (k : Nat) (s : Config n) : Config n :=
  fun i => s ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

theorem shiftLeft_zero {n : Nat} (s : Config n) : shiftLeft 0 s = s := by
  funext i
  simp only [shiftLeft, Nat.add_zero]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem shiftLeft_add {n : Nat} (a b : Nat) (s : Config n) :
    shiftLeft a (shiftLeft b s) = shiftLeft (a + b) s := by
  funext i
  simp only [shiftLeft]
  congr 1
  apply Fin.ext
  have : ((i.val + a) % n + b) % n = (i.val + a + b) % n := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  simp only [Nat.add_assoc] at this ⊢
  exact this

theorem shiftLeft_one_eq_rightIdx {n : Nat} (s : Config n) (i : Fin n) :
    shiftLeft 1 s i = s (rightIdx i) := rfl

theorem shiftLeft_n {n : Nat} (s : Config n) : shiftLeft n s = s := by
  funext i
  simp only [shiftLeft]
  congr 1
  apply Fin.ext
  simp only [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- `p` is an eventual period of `f : Nat → α`. -/
def IsEventuallyPeriodic {α : Type} (f : Nat → α) (p : Nat) : Prop :=
  0 < p ∧ ∃ t₀ : Nat, ∀ t : Nat, t₀ ≤ t → f (t + p) = f t

/-- `p` is the minimal (exact) eventual period of `f : Nat → α`. -/
def HasEventualPeriod {α : Type} (f : Nat → α) (p : Nat) : Prop :=
  IsEventuallyPeriodic f p ∧ ∀ q : Nat, IsEventuallyPeriodic f q → p ≤ q

/-- Closed-form formula for OEIS A334501. -/
def a334501 (n : Nat) : Nat :=
  if n ≤ 3 then 1
  else if n % 4 = 0 then 4
  else n

/-! ### Part 1: Small Ring Widths (`n = 1, 2, 3`) -/

theorem step_allTrue {n : Nat} : step (fun (_ : Fin n) => true) = fun _ => true := by
  funext i
  simp [step, rule190_eq]

theorem step_singleCell_small (n : Nat) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) :
    step (singleCell n) = fun _ => true := by
  funext i
  simp only [step, rule190_eq, singleCell]
  rw [leftIdx_val, rightIdx_val]
  have hi := i.isLt
  have hcase : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hcase with h | h | h
  · simp [h]; omega
  · have h2 : n = 2 ∨ n = 3 := by omega
    rcases h2 with rfl | rfl <;> simp [h]
  · have h3 : n = 3 := by omega
    subst h3
    simp [h]

theorem evolve_small (n : Nat) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (t : Nat) (ht : 1 ≤ t) :
    evolve n t = fun _ => true := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  induction k with
  | zero => exact step_singleCell_small n hn1 hn3
  | succ k ih =>
    change step (evolve n (k + 1)) = _
    rw [ih (by omega), step_allTrue]

/-! ### Part 2: Exact Light Cone Expansion (`n ≥ 4`, `0 ≤ t ≤ n / 2`) -/

/-- Exact configuration inside the Rule 190 light cone at time `t` on a ring of width `n`. -/
def lightCone (n t : Nat) (i : Fin n) : Bool :=
  if i.val ≤ t then
    (i.val + t) % 4 != 3
  else if n - t ≤ i.val then
    (i.val + t - n) % 4 != 3
  else
    false

theorem lightCone_zero (n : Nat) (_hn : 4 ≤ n) : lightCone n 0 = singleCell n := by
  funext i
  simp only [lightCone, singleCell]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · simp [h0]
  · have h1 : ¬ (i.val ≤ 0) := by omega
    simp [h0, h1]

/-- Core local rule identity inside the `1110`-periodic interior of the light cone. -/
private theorem rule190_interior (a : Nat) :
    rule190 (a % 4 != 3) ((a + 1) % 4 != 3) ((a + 2) % 4 != 3) = ((a + 2) % 4 != 3) := by
  rw [rule190_eq]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  have h1 : (a + 1) % 4 = (a % 4 + 1) % 4 := by omega
  have h2 : (a + 2) % 4 = (a % 4 + 2) % 4 := by omega
  rw [h1, h2]
  generalize a % 4 = r at h ⊢
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | r + 4 => omega

/-- Core local rule identity at the right light-cone frontier `i = t`. -/
private theorem rule190_right_frontier (t : Nat) (ht : 1 ≤ t) :
    rule190 ((2 * t - 1) % 4 != 3) ((2 * t) % 4 != 3) false = ((2 * t + 1) % 4 != 3) := by
  rw [rule190_eq]
  have hmod : (2 * t) % 4 = 0 ∨ (2 * t) % 4 = 2 := by omega
  rcases hmod with h | h
  · have hm : (2 * t - 1) % 4 = 3 := by omega
    have hp : (2 * t + 1) % 4 = 1 := by omega
    simp [h, hm, hp]
  · have hm : (2 * t - 1) % 4 = 1 := by omega
    have hp : (2 * t + 1) % 4 = 3 := by omega
    simp [h, hm, hp]

/-- One step of Rule 190 advances `lightCone n t` to `lightCone n (t + 1)` whenever `2*t + 2 ≤ n`. -/
theorem step_lightCone (n t : Nat) (hn : 4 ≤ n) (ht : 2 * t + 2 ≤ n) :
    step (lightCone n t) = lightCone n (t + 1) := by
  funext i
  simp only [step]
  have hi := i.isLt
  -- Split into the exact geometric regions of the expanding light cone
  by_cases h_zero : i.val = 0
  · -- Region 1: center `i = 0`
    have hl : (leftIdx i).val = n - 1 := by rw [leftIdx_val]; simp [h_zero]
    have hr : (rightIdx i).val = 1 := by rw [rightIdx_val]; simp [h_zero]; omega
    by_cases ht0 : t = 0
    · subst ht0
      simp only [lightCone, h_zero, hl, hr]
      have h1 : ¬ (n - 1 ≤ 0) := by omega
      have h3 : ¬ (1 ≤ 0) := by omega
      simp [h1, h3, rule190_eq]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      have hl_val : lightCone n (k + 1) (leftIdx i) = (k % 4 != 3) := by
        simp only [lightCone, hl]
        have h1 : ¬ (n - 1 ≤ k + 1) := by omega
        have h2 : n - (k + 1) ≤ n - 1 := by omega
        have h3 : n - 1 + (k + 1) - n = k := by omega
        simp [h1, h2, h3]
      have hc_val : lightCone n (k + 1) i = ((k + 1) % 4 != 3) := by
        simp only [lightCone, h_zero]
        simp
      have hr_val : lightCone n (k + 1) (rightIdx i) = ((k + 2) % 4 != 3) := by
        simp only [lightCone, hr]
        have h1 : 1 ≤ k + 1 := by omega
        have h2 : 1 + (k + 1) = k + 2 := by omega
        simp [h1, h2]
      have htgt : lightCone n (k + 1 + 1) i = ((k + 2) % 4 != 3) := by
        simp only [lightCone, h_zero]
        have h2 : k + 1 + 1 = k + 2 := by omega
        simp [h2]
      rw [hl_val, hc_val, hr_val, htgt]
      exact rule190_interior k
  · by_cases h_lt_t : i.val < t
    · -- Region 2: positive interior `0 < i < t`
      have hl : (leftIdx i).val = i.val - 1 := by rw [leftIdx_val]; simp [h_zero]
      have hr : (rightIdx i).val = i.val + 1 := by rw [rightIdx_val]; split <;> omega
      have hl_val : lightCone n t (leftIdx i) = ((i.val - 1 + t) % 4 != 3) := by
        simp only [lightCone, hl]
        have hle : i.val - 1 ≤ t := by omega
        simp [hle]
      have hc_val : lightCone n t i = ((i.val + t) % 4 != 3) := by
        simp only [lightCone]
        have hle : i.val ≤ t := by omega
        simp [hle]
      have hr_val : lightCone n t (rightIdx i) = ((i.val + 1 + t) % 4 != 3) := by
        simp only [lightCone, hr]
        have hle : i.val + 1 ≤ t := by omega
        simp [hle]
      have htgt : lightCone n (t + 1) i = ((i.val + (t + 1)) % 4 != 3) := by
        simp only [lightCone]
        have hle : i.val ≤ t + 1 := by omega
        simp [hle]
      rw [hl_val, hc_val, hr_val, htgt]
      have h1 : i.val + t = (i.val - 1 + t) + 1 := by omega
      have h2 : i.val + 1 + t = (i.val - 1 + t) + 2 := by omega
      have h3 : i.val + (t + 1) = (i.val - 1 + t) + 2 := by omega
      rw [h1, h2, h3]
      exact rule190_interior (i.val - 1 + t)
    · by_cases h_eq_t : i.val = t
      · -- Region 3: right frontier `i = t` (with `t ≥ 1` since `i ≠ 0`)
        have ht1 : 1 ≤ t := by omega
        have hl : (leftIdx i).val = t - 1 := by rw [leftIdx_val]; split <;> omega
        have hr : (rightIdx i).val = t + 1 := by rw [rightIdx_val]; split <;> omega
        have hl_val : lightCone n t (leftIdx i) = ((2 * t - 1) % 4 != 3) := by
          simp only [lightCone, hl]
          have h1 : t - 1 ≤ t := by omega
          have h2 : t - 1 + t = 2 * t - 1 := by omega
          simp [h1, h2]
        have hc_val : lightCone n t i = ((2 * t) % 4 != 3) := by
          simp only [lightCone, h_eq_t]
          have h2 : t + t = 2 * t := by omega
          simp [h2]
        have hr_val : lightCone n t (rightIdx i) = false := by
          simp only [lightCone, hr]
          have h1 : ¬ (t + 1 ≤ t) := by omega
          have h2 : ¬ (n - t ≤ t + 1) := by omega
          simp [h1, h2]
        have htgt : lightCone n (t + 1) i = ((2 * t + 1) % 4 != 3) := by
          simp only [lightCone, h_eq_t]
          have h1 : t ≤ t + 1 := by omega
          have h2 : t + (t + 1) = 2 * t + 1 := by omega
          simp [h1, h2]
        rw [hl_val, hc_val, hr_val, htgt]
        exact rule190_right_frontier t ht1
      · by_cases h_eq_t1 : i.val = t + 1
        · -- Region 4: new right edge `i = t + 1`
          have hl : (leftIdx i).val = t := by rw [leftIdx_val]; split <;> omega
          have hl_val : lightCone n t (leftIdx i) = true := by
            simp only [lightCone, hl]
            have hmod : (t + t) % 4 ≠ 3 := by omega
            simp [hmod]
          have hc_val : lightCone n t i = false := by
            simp only [lightCone, h_eq_t1]
            have h1 : ¬ (t + 1 ≤ t) := by omega
            have h2 : ¬ (n - t ≤ t + 1) := by omega
            simp [h1, h2]
          have htgt : lightCone n (t + 1) i = true := by
            simp only [lightCone, h_eq_t1]
            have hmod : (t + 1 + (t + 1)) % 4 ≠ 3 := by omega
            simp [hmod]
          rw [hl_val, hc_val, htgt, rule190_eq]
          simp
        · by_cases h_gap : i.val < n - (t + 1)
          · -- Region 5: outside the next light cone (`t + 1 < i < n - (t + 1)`)
            have hl : (leftIdx i).val = i.val - 1 := by rw [leftIdx_val]; simp [h_zero]
            have hr : (rightIdx i).val = i.val + 1 := by rw [rightIdx_val]; split <;> omega
            have hl_val : lightCone n t (leftIdx i) = false := by
              simp only [lightCone, hl]
              have h1 : ¬ (i.val - 1 ≤ t) := by omega
              have h2 : ¬ (n - t ≤ i.val - 1) := by omega
              simp [h1, h2]
            have hc_val : lightCone n t i = false := by
              simp only [lightCone]
              have h1 : ¬ (i.val ≤ t) := by omega
              have h2 : ¬ (n - t ≤ i.val) := by omega
              simp [h1, h2]
            have hr_val : lightCone n t (rightIdx i) = false := by
              simp only [lightCone, hr]
              have h1 : ¬ (i.val + 1 ≤ t) := by omega
              have h2 : ¬ (n - t ≤ i.val + 1) := by omega
              simp [h1, h2]
            have htgt : lightCone n (t + 1) i = false := by
              simp only [lightCone]
              have h1 : ¬ (i.val ≤ t + 1) := by omega
              have h2 : ¬ (n - (t + 1) ≤ i.val) := by omega
              simp [h1, h2]
            rw [hl_val, hc_val, hr_val, htgt]
            rfl
          · by_cases h_eq_nt1 : i.val = n - (t + 1)
            · -- Region 6: new left edge `i = n - (t + 1)` (with `i > t + 1`)
              have hr_val : lightCone n t (rightIdx i) = true := by
                by_cases ht0 : t = 0
                · subst ht0
                  have hr : (rightIdx i).val = 0 := by rw [rightIdx_val]; split <;> omega
                  simp only [lightCone, hr]; simp
                · have hr : (rightIdx i).val = n - t := by rw [rightIdx_val]; split <;> omega
                  simp only [lightCone, hr]
                  have h1 : ¬ (n - t ≤ t) := by omega
                  have h3 : n - t + t - n = 0 := by omega
                  simp [h1, h3]
              have htgt : lightCone n (t + 1) i = true := by
                simp only [lightCone, h_eq_nt1]
                have h1 : ¬ (n - (t + 1) ≤ t + 1) := by omega
                have h3 : n - (t + 1) + (t + 1) - n = 0 := by omega
                simp [h1, h3]
              rw [hr_val, htgt, rule190_eq]
              simp
            · by_cases h_eq_nt : i.val = n - t
              · -- Region 7: previous left frontier `i = n - t` (requires `t ≥ 1` since `i < n`)
                have hl : (leftIdx i).val = n - t - 1 := by rw [leftIdx_val]; split <;> omega
                have hl_val : lightCone n t (leftIdx i) = false := by
                  simp only [lightCone, hl]
                  have h1 : ¬ (n - t - 1 ≤ t) := by omega
                  have h2 : ¬ (n - t ≤ n - t - 1) := by omega
                  simp [h1, h2]
                have hc_val : lightCone n t i = true := by
                  simp only [lightCone, h_eq_nt]
                  have h1 : ¬ (n - t ≤ t) := by omega
                  have h3 : n - t + t - n = 0 := by omega
                  simp [h1, h3]
                have htgt : lightCone n (t + 1) i = true := by
                  simp only [lightCone, h_eq_nt]
                  have h1 : ¬ (n - t ≤ t + 1) := by omega
                  have h2 : n - (t + 1) ≤ n - t := by omega
                  have h3 : n - t + (t + 1) - n = 1 := by omega
                  simp [h1, h2, h3]
                rw [hl_val, hc_val, htgt, rule190_eq]
                simp
              · -- Region 8: negative interior `n - t < i < n`
                have hl : (leftIdx i).val = i.val - 1 := by rw [leftIdx_val]; simp [h_zero]
                have hl_val : lightCone n t (leftIdx i) = ((i.val - 1 + t - n) % 4 != 3) := by
                  simp only [lightCone, hl]
                  have h1 : ¬ (i.val - 1 ≤ t) := by omega
                  have h2 : n - t ≤ i.val - 1 := by omega
                  simp [h1, h2]
                have hc_val : lightCone n t i = ((i.val + t - n) % 4 != 3) := by
                  simp only [lightCone]
                  have h1 : ¬ (i.val ≤ t) := by omega
                  have h2 : n - t ≤ i.val := by omega
                  simp [h1, h2]
                have hr_val : lightCone n t (rightIdx i) = ((i.val + 1 + t - n) % 4 != 3) := by
                  simp only [lightCone]
                  rw [rightIdx_val]
                  split
                  · next hlt =>
                    have h1 : ¬ (i.val + 1 ≤ t) := by omega
                    have h2 : n - t ≤ i.val + 1 := by omega
                    simp [h1, h2]
                  · next hge =>
                    have h1 : 0 ≤ t := Nat.zero_le _
                    have h2 : 0 + t = i.val + 1 + t - n := by omega
                    simp [h1, h2]
                have htgt : lightCone n (t + 1) i = ((i.val + (t + 1) - n) % 4 != 3) := by
                  simp only [lightCone]
                  have h1 : ¬ (i.val ≤ t + 1) := by omega
                  have h2 : n - (t + 1) ≤ i.val := by omega
                  simp [h1, h2]
                rw [hl_val, hc_val, hr_val, htgt]
                have h1 : i.val + t - n = (i.val - 1 + t - n) + 1 := by omega
                have h2 : i.val + 1 + t - n = (i.val - 1 + t - n) + 2 := by omega
                have h3 : i.val + (t + 1) - n = (i.val - 1 + t - n) + 2 := by omega
                rw [h1, h2, h3]
                exact rule190_interior (i.val - 1 + t - n)

/-- For all `n ≥ 4` and all `t ≤ n / 2`, the state at time `t` is exactly `lightCone n t`. -/
theorem evolve_eq_lightCone (n t : Nat) (hn : 4 ≤ n) (ht : t ≤ n / 2) :
    evolve n t = lightCone n t := by
  induction t with
  | zero => exact (lightCone_zero n hn).symm
  | succ t ih =>
    simp only [evolve]
    rw [ih (by omega)]
    exact step_lightCone n t hn (by omega)

/-! ### Part 3: Attractor `110`-Safety and Left-Shift Dynamics (`t ≥ n / 2`) -/

/-- A configuration is `110`-safe if every `false` cell is preceded by two `true` cells. -/
def Is110Safe {n : Nat} (s : Config n) : Prop :=
  ∀ i : Fin n, s i = false → s (leftIdx i) = true ∧ s (leftIdx (leftIdx i)) = true

/-- On any `110`-safe configuration, Rule 190 acts as a pure cyclic left shift by `1`. -/
theorem step_eq_shiftLeft_one {n : Nat} (s : Config n) (hs : Is110Safe s) :
    step s = shiftLeft 1 s := by
  funext i
  simp only [step, rule190_eq, shiftLeft_one_eq_rightIdx]
  cases hr : s (rightIdx i)
  · have hsafe := hs (rightIdx i) hr
    rw [leftIdx_rightIdx] at hsafe
    rw [hsafe.1, hsafe.2]
    rfl
  · rfl

/-- Cyclic left shift by `1` preserves `110`-safety. -/
theorem shiftLeft_one_safe {n : Nat} (s : Config n) (hs : Is110Safe s) :
    Is110Safe (shiftLeft 1 s) := by
  intro i hi
  simp only [shiftLeft_one_eq_rightIdx] at hi ⊢
  have h1 : rightIdx (leftIdx i) = i := rightIdx_leftIdx i
  have h2 : rightIdx (leftIdx (leftIdx i)) = leftIdx i := rightIdx_leftIdx (leftIdx i)
  rw [h1, h2]
  have hsafe := hs (rightIdx i) hi
  rw [leftIdx_rightIdx] at hsafe
  exact hsafe

/-- Helper: at `t = n / 2`, `lightCone n (n / 2)` covers the whole ring with no zero gap. -/
theorem lightCone_half_val (n : Nat) (_hn : 4 ≤ n) (i : Fin n) :
    lightCone n (n / 2) i =
      if i.val ≤ n / 2 then (i.val + n / 2) % 4 != 3
      else (i.val + n / 2 - n) % 4 != 3 := by
  simp only [lightCone]
  split
  · rfl
  · next h =>
    have hge : n - n / 2 ≤ i.val := by omega
    simp [hge]

/-- At `t = n / 2`, the configuration `lightCone n (n / 2)` is `110`-safe for all `n ≥ 4`. -/
theorem lightCone_half_safe (n : Nat) (hn : 4 ≤ n) : Is110Safe (lightCone n (n / 2)) := by
  intro i hi
  have hi_lt := i.isLt
  rw [lightCone_half_val n hn] at hi
  by_cases hle : i.val ≤ n / 2
  · simp only [hle, ite_true, bne_eq_false_iff_eq] at hi
    -- Here `i ≤ n/2` and `(i + n/2) % 4 = 3`
    by_cases h0 : i.val = 0
    · -- `i = 0`, so `(n/2) % 4 = 3`, hence `n/2 ≥ 3` and `n ≥ 6`
      have h1 : (leftIdx i).val = n - 1 := by rw [leftIdx_val]; simp [h0]
      have h2 : (leftIdx (leftIdx i)).val = n - 2 := by
        rw [leftIdx_val, h1]; split <;> omega
      constructor
      · rw [lightCone_half_val n hn, h1]
        have hgt : ¬ (n - 1 ≤ n / 2) := by omega
        simp [hgt]; omega
      · rw [lightCone_half_val n hn, h2]
        have hgt : ¬ (n - 2 ≤ n / 2) := by omega
        simp [hgt]; omega
    · by_cases h1eq : i.val = 1
      · -- `i = 1`, so `(1 + n/2) % 4 = 3`, i.e., `(n/2) % 4 = 2`
        have h1 : (leftIdx i).val = 0 := by rw [leftIdx_val]; simp [h1eq]
        have h2 : (leftIdx (leftIdx i)).val = n - 1 := by rw [leftIdx_val, h1]; simp
        constructor
        · rw [lightCone_half_val n hn, h1]
          simp; omega
        · rw [lightCone_half_val n hn, h2]
          have hgt : ¬ (n - 1 ≤ n / 2) := by omega
          simp [hgt]; omega
      · -- `2 ≤ i ≤ n/2`
        have h1 : (leftIdx i).val = i.val - 1 := by rw [leftIdx_val]; simp [h0]
        have h2 : (leftIdx (leftIdx i)).val = i.val - 2 := by
          rw [leftIdx_val, h1]; split <;> omega
        constructor
        · rw [lightCone_half_val n hn, h1]
          have hle1 : i.val - 1 ≤ n / 2 := by omega
          simp [hle1]; omega
        · rw [lightCone_half_val n hn, h2]
          have hle2 : i.val - 2 ≤ n / 2 := by omega
          simp [hle2]; omega
  · simp only [hle, ite_false, bne_eq_false_iff_eq] at hi
    -- Here `i > n/2` and `(i + n/2 - n) % 4 = 3`, so `i ≥ n - n/2 + 3 ≥ n/2 + 3`
    have h1 : (leftIdx i).val = i.val - 1 := by rw [leftIdx_val]; split <;> omega
    have h2 : (leftIdx (leftIdx i)).val = i.val - 2 := by
      rw [leftIdx_val, h1]; split <;> omega
    constructor
    · rw [lightCone_half_val n hn, h1]
      have hgt1 : ¬ (i.val - 1 ≤ n / 2) := by omega
      simp [hgt1]; omega
    · rw [lightCone_half_val n hn, h2]
      have hgt2 : ¬ (i.val - 2 ≤ n / 2) := by omega
      simp [hgt2]; omega

/-- From time `t = n / 2` onward, Rule 190 simply shifts `lightCone n (n / 2)` left by `1` per step. -/
theorem evolve_after_half (n k : Nat) (hn : 4 ≤ n) :
    evolve n (n / 2 + k) = shiftLeft k (lightCone n (n / 2)) := by
  suffices h : evolve n (n / 2 + k) = shiftLeft k (lightCone n (n / 2)) ∧
      Is110Safe (evolve n (n / 2 + k)) from h.1
  induction k with
  | zero =>
    rw [Nat.add_zero, shiftLeft_zero, evolve_eq_lightCone n (n / 2) hn (Nat.le_refl _)]
    exact ⟨rfl, lightCone_half_safe n hn⟩
  | succ k ih =>
    have hstep : evolve n (n / 2 + (k + 1)) = step (evolve n (n / 2 + k)) := by
      rw [← Nat.add_assoc]; rfl
    rw [hstep, step_eq_shiftLeft_one _ ih.2, ih.1]
    constructor
    · rw [shiftLeft_add, Nat.add_comm 1 k]
    · exact shiftLeft_one_safe _ (ih.1 ▸ ih.2)

/-! ### Part 4: Exact Spatial Period of the Attractor `lightCone n (n / 2)` -/

/-- When `4 ∣ n`, the attractor has a uniform period-4 crystal formula `(i + n/2) % 4 ≠ 3`. -/
theorem lightCone_half_mod4_zero (n : Nat) (hn : 4 ≤ n) (h4 : n % 4 = 0) (i : Fin n) :
    lightCone n (n / 2) i = ((i.val + n / 2) % 4 != 3) := by
  rw [lightCone_half_val n hn]
  split
  · rfl
  · next h =>
    have hmod : (i.val + n / 2 - n) % 4 = (i.val + n / 2) % 4 := by omega
    rw [hmod]

/-- When `4 ∣ n`, shifting the attractor left by `4` leaves it invariant. -/
theorem shiftLeft_four_of_mod4_zero (n : Nat) (hn : 4 ≤ n) (h4 : n % 4 = 0) :
    shiftLeft 4 (lightCone n (n / 2)) = lightCone n (n / 2) := by
  funext i
  simp only [shiftLeft]
  rw [lightCone_half_mod4_zero n hn h4, lightCone_half_mod4_zero n hn h4]
  have hmod : ((i.val + 4) % n + n / 2) % 4 = (i.val + n / 2) % 4 := by
    have hdvd : (i.val + 4) % n % 4 = (i.val + 4) % 4 := by
      have h1 : 4 ∣ n := Nat.dvd_of_mod_eq_zero h4
      exact Nat.mod_mod_of_dvd (i.val + 4) h1
    omega
  rw [hmod]

/-- When `4 ∣ n`, any cyclic shift leaving the attractor invariant must be a multiple of `4`. -/
theorem four_dvd_of_shiftLeft_eq (n q : Nat) (hn : 4 ≤ n) (h4 : n % 4 = 0)
    (hq : shiftLeft q (lightCone n (n / 2)) = lightCone n (n / 2)) :
    4 ∣ q := by
  let i0Val := (3 + 4 - (n / 2) % 4) % 4
  have hi0_lt : i0Val < n := by omega
  let i0 : Fin n := ⟨i0Val, hi0_lt⟩
  have hEq := congrFun hq i0
  simp only [shiftLeft] at hEq
  rw [lightCone_half_mod4_zero n hn h4, lightCone_half_mod4_zero n hn h4] at hEq
  have h0 : (i0Val + n / 2) % 4 = 3 := by omega
  have h1 : ((i0Val + q) % n + n / 2) % 4 = 3 := by
    rw [h0] at hEq
    simpa using hEq
  have hdvd : (i0Val + q) % n % 4 = (i0Val + q) % 4 :=
    Nat.mod_mod_of_dvd (i0Val + q) (Nat.dvd_of_mod_eq_zero h4)
  have hq0 : q % 4 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hq0

/-- Position of the unique topological defect in the attractor when `4 ∤ n`. -/
def defectIdx (n : Nat) : Nat :=
  n / 2 - (2 * (n / 2) + 1) % 4

theorem defectIdx_lt (n : Nat) (hn : 4 ≤ n) (_h4 : n % 4 ≠ 0) : defectIdx n < n := by
  unfold defectIdx; omega

/--
Unique Defect Witness Lemma: when `n ≥ 4` and `4 ∤ n`, the index `defectIdx n` is the UNIQUE
cell `i : Fin n` such that `S i = false` and `S ((i + 4) mod n) = true`.
-/
theorem unique_defect_witness (n : Nat) (hn : 4 ≤ n) (h4 : n % 4 ≠ 0) (i : Fin n) :
    (lightCone n (n / 2) i = false ∧
     lightCone n (n / 2) ⟨(i.val + 4) % n, Nat.mod_lt _ (by omega)⟩ = true) ↔
    i.val = defectIdx n := by
  have hi := i.isLt
  have hn5 : 5 ≤ n := by omega
  constructor
  · -- (→) Any witness must equal `defectIdx n`
    rintro ⟨hfalse, htrue⟩
    rw [lightCone_half_val n hn] at hfalse htrue
    by_cases hle : i.val ≤ n / 2
    · simp only [hle, ite_true, bne_eq_false_iff_eq] at hfalse
      by_cases hle4 : i.val + 4 ≤ n / 2
      · have hmod : (i.val + 4) % n = i.val + 4 := Nat.mod_eq_of_lt (by omega)
        simp only [hmod, hle4, ite_true, bne_iff_ne, ne_eq] at htrue
        omega
      · unfold defectIdx; omega
    · simp only [hle, ite_false, bne_eq_false_iff_eq] at hfalse
      by_cases hlt4 : i.val + 4 < n
      · have hmod : (i.val + 4) % n = i.val + 4 := Nat.mod_eq_of_lt hlt4
        have hgt4 : ¬ (i.val + 4 ≤ n / 2) := by omega
        simp only [hmod, hgt4, ite_false, bne_iff_ne, ne_eq] at htrue
        omega
      · have hmod : (i.val + 4) % n = i.val + 4 - n :=
          calc (i.val + 4) % n
            _ = ((i.val + 4 - n) + n) % n := by congr 1; omega
            _ = (i.val + 4 - n) % n := Nat.add_mod_right _ _
            _ = i.val + 4 - n := Nat.mod_eq_of_lt (by omega)
        have hle4 : i.val + 4 - n ≤ n / 2 := by omega
        simp only [hmod, hle4, ite_true, bne_iff_ne, ne_eq] at htrue
        omega
  · -- (←) `defectIdx n` satisfies the defect predicate
    intro hEq
    constructor
    · rw [lightCone_half_val n hn, hEq]
      unfold defectIdx
      have hle : n / 2 - (2 * (n / 2) + 1) % 4 ≤ n / 2 := by omega
      simp only [hle, ite_true, bne_eq_false_iff_eq]
      omega
    · rw [lightCone_half_val n hn]
      simp only [hEq]
      unfold defectIdx
      by_cases hn5eq : n = 5
      · subst hn5eq
        have hmod : (5 / 2 - (2 * (5 / 2) + 1) % 4 + 4) % 5 = 0 := by decide
        simp [hmod]
      · have hlt : n / 2 - (2 * (n / 2) + 1) % 4 + 4 < n := by omega
        have hmod : (n / 2 - (2 * (n / 2) + 1) % 4 + 4) % n =
            n / 2 - (2 * (n / 2) + 1) % 4 + 4 := Nat.mod_eq_of_lt hlt
        have hgt : ¬ (n / 2 - (2 * (n / 2) + 1) % 4 + 4 ≤ n / 2) := by omega
        simp only [hmod, hgt, ite_false, bne_iff_ne, ne_eq]
        omega

/-- When `4 ∤ n`, any cyclic shift leaving the attractor invariant must be a multiple of `n`. -/
theorem n_dvd_of_shiftLeft_eq (n q : Nat) (hn : 4 ≤ n) (h4 : n % 4 ≠ 0)
    (hq : shiftLeft q (lightCone n (n / 2)) = lightCone n (n / 2)) :
    n ∣ q := by
  let z : Fin n := ⟨defectIdx n, defectIdx_lt n hn h4⟩
  have hz : lightCone n (n / 2) z = false ∧
      lightCone n (n / 2) ⟨(z.val + 4) % n, Nat.mod_lt _ (by omega)⟩ = true :=
    (unique_defect_witness n hn h4 z).mpr rfl
  let zq : Fin n := ⟨(z.val + q) % n, Nat.mod_lt _ (by omega)⟩
  have hz1 : lightCone n (n / 2) zq = false := by
    have h := congrFun hq z
    simpa [shiftLeft, zq] using h.trans hz.1
  have hz2 : lightCone n (n / 2) ⟨(zq.val + 4) % n, Nat.mod_lt _ (by omega)⟩ = true := by
    let z4 : Fin n := ⟨(z.val + 4) % n, Nat.mod_lt _ (by omega)⟩
    have h := congrFun hq z4
    have hidx : ((z.val + 4) % n + q) % n = ((z.val + q) % n + 4) % n := by
      have h1 : ((z.val + 4) % n + q) % n = (z.val + 4 + q) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h2 : ((z.val + q) % n + 4) % n = (z.val + q + 4) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1, h2, Nat.add_right_comm]
    have hfin : (⟨(zq.val + 4) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) =
        ⟨(z4.val + q) % n, Nat.mod_lt _ (by omega)⟩ := Fin.ext hidx.symm
    rw [hfin]
    exact h.trans hz.2
  have huniq : zq.val = defectIdx n := (unique_defect_witness n hn h4 zq).mp ⟨hz1, hz2⟩
  -- From `(z.val + q) % n = z.val` with `z.val < n`, deduce `q % n = 0`
  have hq0 : q % n = 0 := by
    have hlt : defectIdx n < n := defectIdx_lt n hn h4
    have hmod_eq : (defectIdx n + q) % n = defectIdx n := huniq
    have h1 : (defectIdx n + q % n) % n = defectIdx n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact hmod_eq
    have hqlt : q % n < n := Nat.mod_lt q (by omega)
    by_cases hsum : defectIdx n + q % n < n
    · rw [Nat.mod_eq_of_lt hsum] at h1; omega
    · have h2 : defectIdx n + q % n = (defectIdx n + q % n - n) + n := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1
      omega
  exact Nat.dvd_of_mod_eq_zero hq0

/-! ### Part 5: Main Theorems — Global and Single-Cell Eventual Periods -/

/--
Helper: if a single cell `i` is eventually periodic with period `q` on a shift orbit
`k ↦ shiftLeft k S`, then `shiftLeft q S = S`.
-/
theorem shiftLeft_eq_of_cell_periodic {n : Nat} (S : Config n) (i : Fin n) (q : Nat)
    (hper : ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k → shiftLeft (k + q) S i = shiftLeft k S i) :
    shiftLeft q S = S := by
  obtain ⟨k₀, hk₀⟩ := hper
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  funext j
  let r := (i.val + k₀) % n
  let d := (j.val + n - r) % n
  let k := k₀ + d
  have hk_ge : k₀ ≤ k := Nat.le_add_right k₀ d
  have hspec := hk₀ k hk_ge
  simp only [shiftLeft] at hspec ⊢
  have hjk : (i.val + k) % n = j.val := by
    have hjlt := j.isLt
    have hrlt : r < n := Nat.mod_lt _ hn
    calc (i.val + (k₀ + d)) % n
      _ = ((i.val + k₀) + d) % n := by rw [Nat.add_assoc]
      _ = ((i.val + k₀) % n + d % n) % n := Nat.add_mod _ _ _
      _ = (r % n + (j.val + n - r) % n) % n := by simp only [r, d, Nat.mod_mod]
      _ = (r + (j.val + n - r)) % n := (Nat.add_mod _ _ _).symm
      _ = (j.val + n) % n := by congr 1; omega
      _ = j.val % n := Nat.add_mod_right _ _
      _ = j.val := Nat.mod_eq_of_lt hjlt
  have hjkq : (i.val + (k + q)) % n = (j.val + q) % n :=
    calc (i.val + (k + q)) % n
      _ = ((i.val + k) + q) % n := by congr 1; omega
      _ = ((i.val + k) % n + q % n) % n := Nat.add_mod _ _ _
      _ = (j.val % n + q % n) % n := by rw [hjk, Nat.mod_eq_of_lt j.isLt]
      _ = (j.val + q) % n := (Nat.add_mod _ _ _).symm
  have hfin1 : (⟨(i.val + (k + q)) % n, Nat.mod_lt _ hn⟩ : Fin n) =
      ⟨(j.val + q) % n, Nat.mod_lt _ hn⟩ := Fin.ext hjkq
  have hfin2 : (⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext hjk
  rw [hfin1, hfin2] at hspec
  exact hspec

/-- For every `n ≥ 1`, `a334501 n` divides every eventual period of any cell `i : Fin n`. -/
theorem a334501_dvd_of_cell_periodic (n : Nat) (_hn : 1 ≤ n) (i : Fin n) (q : Nat)
    (hq : IsEventuallyPeriodic (fun t => evolve n t i) q) :
    a334501 n ∣ q := by
  unfold a334501
  split
  · exact Nat.one_dvd q
  · next hgt3 =>
    have hn4 : 4 ≤ n := by omega
    obtain ⟨_, t₀, ht₀⟩ := hq
    have hshift : shiftLeft q (lightCone n (n / 2)) = lightCone n (n / 2) := by
      apply shiftLeft_eq_of_cell_periodic (lightCone n (n / 2)) i q
      refine ⟨t₀, fun k hk => ?_⟩
      have h1 := ht₀ (n / 2 + k) (by omega)
      dsimp only at h1
      rw [Nat.add_assoc] at h1
      rw [evolve_after_half n (k + q) hn4, evolve_after_half n k hn4] at h1
      exact h1
    split
    · next h4 => exact four_dvd_of_shiftLeft_eq n q hn4 h4 hshift
    · next h4 => exact n_dvd_of_shiftLeft_eq n q hn4 h4 hshift

/-- For every `n ≥ 1`, `evolve n` is eventually periodic with period `a334501 n`. -/
theorem evolve_isEventuallyPeriodic (n : Nat) (hn : 1 ≤ n) :
    IsEventuallyPeriodic (evolve n) (a334501 n) := by
  unfold a334501
  split
  · next hle3 =>
    refine ⟨by omega, 1, fun t ht => ?_⟩
    rw [evolve_small n hn hle3 (t + 1) (by omega), evolve_small n hn hle3 t ht]
  · next hgt3 =>
    have hn4 : 4 ≤ n := by omega
    split
    · next h4 =>
      refine ⟨by omega, n / 2, fun t ht => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, t = n / 2 + k := ⟨t - n / 2, by omega⟩
      rw [Nat.add_assoc, evolve_after_half n (k + 4) hn4, evolve_after_half n k hn4]
      rw [← shiftLeft_add, shiftLeft_four_of_mod4_zero n hn4 h4]
    · next h4 =>
      refine ⟨by omega, n / 2, fun t ht => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, t = n / 2 + k := ⟨t - n / 2, by omega⟩
      rw [Nat.add_assoc, evolve_after_half n (k + n) hn4, evolve_after_half n k hn4]
      rw [← shiftLeft_add, shiftLeft_n]

/--
**Main Theorem 1 (Global Configuration Eventual Period, OEIS A334501)**:
For every ring width `n ≥ 1`, the exact (minimal) eventual period of the Rule 190
cellular automaton started from a single live cell is `a334501 n`.
-/
theorem eventualPeriod_global (n : Nat) (hn : 1 ≤ n) :
    HasEventualPeriod (evolve n) (a334501 n) := by
  refine ⟨evolve_isEventuallyPeriodic n hn, fun q hq => ?_⟩
  have hcell : IsEventuallyPeriodic (fun t => evolve n t ⟨0, by omega⟩) q := by
    obtain ⟨hqpos, t₀, ht₀⟩ := hq
    exact ⟨hqpos, t₀, fun t ht => congrFun (ht₀ t ht) ⟨0, by omega⟩⟩
  have hdvd : a334501 n ∣ q := a334501_dvd_of_cell_periodic n hn ⟨0, by omega⟩ q hcell
  exact Nat.le_of_dvd hq.1 hdvd

/--
**Main Theorem 2 (Single-Cell Eventual Period, OEIS A334501)**:
For every ring width `n ≥ 1` and every cell `i : Fin n`, the exact (minimal) eventual period
of the bit sequence observed at cell `i` is also `a334501 n`.
-/
theorem eventualPeriod_cell (n : Nat) (hn : 1 ≤ n) (i : Fin n) :
    HasEventualPeriod (fun t => evolve n t i) (a334501 n) := by
  refine ⟨?_, fun q hq => ?_⟩
  · obtain ⟨hp, t₀, ht₀⟩ := evolve_isEventuallyPeriodic n hn
    exact ⟨hp, t₀, fun t ht => congrFun (ht₀ t ht) i⟩
  · exact Nat.le_of_dvd hq.1 (a334501_dvd_of_cell_periodic n hn i q hq)

/-! ### Part 6: Resolution of Colin Barker's 2020 OEIS A334501 Conjectures -/

/--
Colin Barker's conjectured linear recurrence `a(n) = 2*a(n-4) - a(n-8)` holds for all `n ≥ 12`.
-/
theorem colin_barker_recurrence (n : Nat) (hn : 12 ≤ n) :
    a334501 n = 2 * a334501 (n - 4) - a334501 (n - 8) := by
  unfold a334501
  split <;> try omega
  split <;> try omega
  · next h4 =>
    have h4a : (n - 4) % 4 = 0 := by omega
    have h4b : (n - 8) % 4 = 0 := by omega
    have hgt1 : ¬ (n - 4 ≤ 3) := by omega
    have hgt2 : ¬ (n - 8 ≤ 3) := by omega
    simp [hgt1, hgt2, h4a, h4b]
  · next h4 =>
    have h4a : (n - 4) % 4 ≠ 0 := by omega
    have h4b : (n - 8) % 4 ≠ 0 := by omega
    have hgt1 : ¬ (n - 4 ≤ 3) := by omega
    have hgt2 : ¬ (n - 8 ≤ 3) := by omega
    simp [hgt1, hgt2, h4a, h4b]
    omega

/--
Explicit counterexamples showing that Colin Barker's stated threshold `n > 8` on OEIS A334501
is off by 3: `n = 10` (`10 ≠ 2*6 - 1 = 11`) and `n = 11` (`11 ≠ 2*7 - 1 = 13`) fail,
matching the `- x^9 - 2*x^10` terms in his own generating function!
-/
theorem colin_barker_n_gt_8_counterexamples :
    a334501 10 ≠ 2 * a334501 6 - a334501 2 ∧
    a334501 11 ≠ 2 * a334501 7 - a334501 3 := by
  decide

/--
The numerator polynomial of Colin Barker's conjectured generating function:
`P(x) = x*(1 + x + x^2 + 4*x^3 + 3*x^4 + 4*x^5 + 5*x^6 - 4*x^7 - x^9 - 2*x^10)`.
-/
def colinBarkerNumCoeff : Nat → Int
  | 1  => 1
  | 2  => 1
  | 3  => 1
  | 4  => 4
  | 5  => 3
  | 6  => 4
  | 7  => 5
  | 8  => -4
  | 10 => -1
  | 11 => -2
  | _  => 0

/-- Sequence `a(n)` extended with `a(0) = 0` for the formal power series `∑_{n ≥ 1} a(n) x^n`. -/
def a334501Z (n : Nat) : Int :=
  if n = 0 then 0 else (a334501 n : Int)

/--
**Colin Barker's Generating Function Conjecture (Proved)**:
Since `(1 - x)^2 * (1 + x)^2 * (1 + x^2)^2 = (1 - x^4)^2 = 1 - 2x^4 + x^8`,
multiplying `A(x) = ∑_{n ≥ 1} a334501(n) x^n` by `(1 - 2x^4 + x^8)` produces exact
coefficient `colinBarkerNumCoeff n` at every degree `n : Nat`.
-/
theorem colin_barker_gf_identity (n : Nat) :
    (a334501Z n - (if 4 ≤ n then 2 * a334501Z (n - 4) else 0) +
      (if 8 ≤ n then a334501Z (n - 8) else 0)) = colinBarkerNumCoeff n := by
  by_cases h12 : n < 12
  · match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
    | n + 12 => omega
  · have hn12 : 12 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h8 : 8 ≤ n := by omega
    have hrec := colin_barker_recurrence n hn12
    have hnum : colinBarkerNumCoeff n = 0 := by
      match n with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
      | _ + 12 => rfl
    have hge : a334501 (n - 8) ≤ 2 * a334501 (n - 4) := by
      have hgt1 : ¬ (n - 4 ≤ 3) := by omega
      have hgt2 : ¬ (n - 8 ≤ 3) := by omega
      simp only [a334501, hgt1, hgt2, ite_false]
      split <;> split <;> omega
    have hz0 : a334501Z n = (a334501 n : Int) := by unfold a334501Z; split <;> omega
    have hz4 : a334501Z (n - 4) = (a334501 (n - 4) : Int) := by unfold a334501Z; split <;> omega
    have hz8 : a334501Z (n - 8) = (a334501 (n - 8) : Int) := by unfold a334501Z; split <;> omega
    simp only [h4, h8, ite_true, hz0, hz4, hz8, hnum]
    omega

end Rule190
