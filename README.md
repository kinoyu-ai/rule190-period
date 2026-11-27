# Rule 190 Cyclic Ring Eventual Period (OEIS A334501)

[![Lean 4 Verify](https://github.com/kinoyu-ai/rule190-period/actions/workflows/lean.yml/badge.svg)](https://github.com/kinoyu-ai/rule190-period/actions/workflows/lean.yml)

A self-contained, zero-dependency **Lean 4** proof resolving the open conjectures on
[OEIS A334501](https://oeis.org/A334501) (*Eventual period of a single cell in rule 190
cellular automaton in a cyclic universe of width $n$*, N. J. A. Sloane, May 2020; conjectures
by Colin Barker, May 9, 2020).

---

## Main Theorem

Let $\text{evolve}(n, t) : \mathrm{Fin}\ n \to \mathrm{Bool}$ be the state at step $t$ of
Elementary Cellular Automaton **Rule 190** ($190_{10} = 10111110_2$, equivalently
$(l, c, r) \mapsto r \lor (l \neq c)$) on a cyclic ring of width $n \ge 1$, started from a
single live cell at index $0$. Define:

$$a(n) = \begin{cases} 1 & (1 \le n \le 3), \\ 4 & (n \ge 4,\ 4 \mid n), \\ n & (n \ge 4,\ 4 \nmid n). \end{cases}$$

We formally prove in [`Rule190.lean`](Rule190.lean) (using **pure Lean 4** with no Mathlib,
no `sorry`, and only standard Lean axioms `[propext, Classical.choice, Quot.sound]`):

1. **`Rule190.eventualPeriod_global`**: For every $n \ge 1$, $a(n)$ is the exact (minimal)
   eventual period of the global configuration orbit $t \mapsto \text{evolve}(n, t)$.
2. **`Rule190.eventualPeriod_cell`**: For every $n \ge 1$ and every cell $i : \mathrm{Fin}\ n$,
   $a(n)$ is also the exact (minimal) eventual period of the individual cell trajectory
   $t \mapsto \text{evolve}(n, t)(i)$.
3. **`Rule190.colin_barker_gf_identity`**: Proves Colin Barker's 2020 generating function
   conjecture for all degrees $n \ge 0$:
   $$(1 - x)^2 (1 + x)^2 (1 + x^2)^2 \sum_{k \ge 1} a(k)\, x^k = x(1 + x + x^2 + 4x^3 + 3x^4 + 4x^5 + 5x^6 - 4x^7 - x^9 - 2x^{10}).$$
4. **`Rule190.colin_barker_recurrence` & `Rule190.colin_barker_n_gt_8_counterexamples`**:
   Proves the linear recurrence $a(n) = 2a(n-4) - a(n-8)$ for all $n \ge 12$, and formally
   shows that $n = 10$ ($10 \neq 2 \cdot 6 - 1 = 11$) and $n = 11$ ($11 \neq 2 \cdot 7 - 1 = 13$)
   are counterexamples to the `for n > 8` threshold written in the OEIS comment (which matches
   the degree-11 numerator of Barker's own generating function).

---

## Proof Overview

```text
n = 12 (4 ∣ n):                n = 13 (4 ∤ n):
t=0: #...........              t=0: #............
t=1: ##.........#              t=1: ##..........#
t=2: #.#.......##              t=2: #.#........##
t=3: .###.....###              t=3: .###......###
t=4: ###.#...###.              t=4: ###.#....###.
t=5: ##.###.###.#              t=5: ##.###..###.#
t=6: #.###.###.##  (period 4)  t=6: #.###.####.##  (unique defect "####" → period 13)
```

1. **Small widths ($1 \le n \le 3$)**: After 1 step every cell becomes `1`, which is a fixed point (period $1$).
2. **Exact light-cone formula ($n \ge 4,\ 0 \le t \le \lfloor n/2 \rfloor$)**: By induction on $t$
   (`evolve_eq_lightCone`), up to and including the collision step $t = \lfloor n/2 \rfloor$,
   the configuration equals `lightCone n t` (inside $[-t, t]$, cell $x$ is `0` iff
   $(x + t) \equiv 3 \pmod 4$).
3. **`110`-safety & pure cyclic left shift ($t \ge \lfloor n/2 \rfloor$)**: At $t = \lfloor n/2 \rfloor$,
   every `0` is preceded by `11` (`lightCone_half_safe`). On any `110`-safe configuration,
   Rule 190 acts as a pure cyclic left shift by $1$ cell per step (`step_eq_shiftLeft_one`),
   preserving `110`-safety forever (`evolve_after_half`).
4. **Minimal spatial period via unique topological defect**:
   - If $4 \mid n$, the two wavefronts meet in phase, forming a uniform `1110` crystal whose
     minimal shift period is $4$.
   - If $4 \nmid n$, the wavefronts meet out of phase, trapping a single longer block of `1`s.
     Its starting `0` at `defectIdx n = n / 2 - (2 * (n / 2) + 1) % 4` is the **unique** index
     $i \in \mathrm{Fin}\ n$ satisfying $S(i) = \mathrm{false} \land S((i+4)\bmod n) = \mathrm{true}$
     (`unique_defect_witness`), forcing minimal shift period $n$.

---

## Build & Verify Locally

Requires Lean 4 (`v4.36.0`, specified in [`lean-toolchain`](lean-toolchain)). No external packages are needed.

```bash
lake build
lake env lean AxiomCheck.lean
```

---

## 概要（日本語）

[OEIS A334501](https://oeis.org/A334501)（幅 $n$ の円環上で 1 セルだけ `1` にして初等セルオートマトン Rule 190 を走らせたときの最終周期）について、2020 年から未証明だった Colin Barker の予想を完全に解決し、外部依存ゼロの純粋な Lean 4 で機械検証しました。

- **主定理**：すべての $n \ge 1$ で最小周期は $n \le 3$ なら $1$、$n \ge 4$ かつ $4 \mid n$ なら $4$、$n \ge 4$ かつ $4 \nmid n$ なら $n$（全体状態・任意の単一セルの双方で成立）。
- **Colin Barker 予想の決着**：母関数予想は全次数で**肯定的（真）**。漸化式 $a(n)=2a(n-4)-a(n-8)$ は $n \ge 12$ で**真**であり、OEIS に書かれていた `n > 8` については $n=10, 11$ が反例であることも形式的に証明しています。
