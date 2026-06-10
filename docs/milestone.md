# Leray–Hopf 弱解存在定理 Lean 形式化ロードマップ

主線は周期領域 $\mathbb T^3$ 上の Leray–Hopf 弱解存在定理。詳細な MVP 設計は
[`leray_hopf_lean_mvp_plan.md`](./leray_hopf_lean_mvp_plan.md) を参照。

## Phase 0：スコープ

対象を三段階に分け、$\mathbb R^3$ 版は最初から狙わない。

$$
\mathbb T^3\ \text{conditional}
\;\to\;
\mathbb T^3\ \text{full}
\;\to\;
\mathbb R^3\ \text{Leray original}
$$

周期境界条件 $\Omega = \mathbb T^3$ から始めることで、境界・無限遠・tightness の処理を避ける。

## Milestone 1：Leray–Hopf solution の定義

- **目標**：存在定理の前に、解概念を Lean で型として定義する。
- **内容**：数学的には
  $u \in L^\infty_{\mathrm{loc}}([0,\infty); L^2) \cap L^2_{\mathrm{loc}}([0,\infty); H^1)$
  であって、弱形式 Navier–Stokes 方程式・初期値条件・エネルギー不等式を満たすもの。
  この段階では各条件を `Prop` placeholder として持たせ、後で順次展開する。

```lean
structure LerayHopfSolution
  (Ω : Type*) (u₀ : SpatialField Ω) where
  u : Time → SpatialField Ω
  weak_eq : Prop
  divergence_free : Prop
  energy_class : Prop
  initial_trace : Prop
  energy_inequality : Prop
```

- **成果物**：`LerayHopf/Basic.lean`

## Milestone 2：弱解存在定理の statement 化

- **目標**：存在定理そのものを Lean で述べ、「何を証明するのか」を固定する。
- **内容**：$u_0 \in L^2_\sigma(\mathbb T^3) \Rightarrow \exists u,\ u\ \text{is a Leray–Hopf solution}$。
  proof はこの時点では `sorry` でよい。

```lean
theorem exists_lerayHopf_torus3_statement
  (u₀ : L2Sigma Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True := by
  sorry
```

- **成果物**：`LerayHopf/Statement.lean`

## Milestone 3：Galerkin compactness package

- **目標**：存在証明を一気に行わず、次の抽象的含意に分解する。
  「Galerkin 近似列が標準評価と compactness を満たす $\Rightarrow$ Leray–Hopf 解が存在する」。
- **内容**：compactness と極限移行の結論をフィールドとして格納したパッケージを定義し、
  そこから存在を導く。これが最初の中心定理。

```lean
structure GalerkinCompactnessPackage where
  approx : ℕ → Time → SpatialField Torus3
  uniform_energy_bound : Prop
  uniform_dissipation_bound : Prop
  time_derivative_bound : Prop
  compactness : Prop
  nonlinear_term_converges : Prop
  initial_trace_converges : Prop
  energy_ineq_passes_to_limit : Prop

theorem exists_lerayHopf_from_galerkin_package
  (pkg : GalerkinCompactnessPackage u₀) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

- **成果物**：`LerayHopf/GalerkinPackage.lean`

## Milestone 4：Galerkin 近似のエネルギー評価

- **目標**：有限次元 Galerkin 近似 $u_n$ に対するエネルギー不等式を証明する。

$$
\tfrac12 \lVert u_n(t)\rVert_2^2
+ \nu \int_0^t \lVert \nabla u_n(s)\rVert_2^2\,ds
\le \tfrac12 \lVert P_n u_0\rVert_2^2
$$

- **内容**：核となるのは非線形項の消去
  $\langle (u_n\cdot\nabla)u_n,\ u_n\rangle = 0$。
  Lean 上でも比較的きれいに切り出せる部分。
- **成果物**：`LerayHopf/EnergyEstimate.lean`

## Milestone 5：周期領域 $\mathbb T^3$ の Fourier–Galerkin 基盤

- **目標**：$\mathbb T^3$ 上で divergence-free Fourier modes、射影 $P_n$、Leray projection を整備する。
- **内容**：必要な構造は
  $L^2_\sigma(\mathbb T^3)$, $H^1_\sigma(\mathbb T^3)$, $P_n$, $\Pi_{\mathrm{div}=0}$。
  mathlib には分布・Sobolev・Fourier の入口はあるが Navier–Stokes 向けの完成 API は無く、
  設計の比重が大きい。
- **成果物**：`LerayHopf/TorusFourier.lean`

## Milestone 6：Aubin–Lions / compactness の axiom 化

- **目標**：最難所の compactness を一旦 axiom とし、先に骨格を完成させる。
- **内容**：「energy estimate + compactness theorem $\Rightarrow$ weak solution exists」の構造を
  先に閉じる。実証明は Milestone 8 で置き換える。

```lean
axiom aubin_lions_for_navier_stokes_torus3 : ...
```

- **成果物**：`LerayHopf/CompactnessAxioms.lean`

## Milestone 7：$\mathbb T^3$ conditional existence theorem

- **目標**：最初の大きな到達点。Aubin–Lions 型 compactness を仮定すれば
  $\mathbb T^3$ 上に Leray–Hopf 弱解が存在することを示す。
- **内容**：弱解存在定理の conditional formalization。ここでプロジェクトの背骨が立つ。

```lean
theorem exists_lerayHopf_torus3_conditional
  (u₀ : L2Sigma Torus3)
  (hcompact : NSCompactnessTheorem Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

- **成果物**：`LerayHopf/ExistenceTorusConditional.lean`

## Milestone 8：compactness を axiom から theorem へ

- **目標**：axiom を一つずつ消す本格段階。
- **内容**：必要となる要素は weak convergence、Bochner 空間 $L^p_t X_x$、Aubin–Lions、
  非線形項の極限移行、lower semicontinuity、initial trace。
- **成果物**：`LerayHopf/AubinLions.lean`, `LerayHopf/LimitPassage.lean`

## Milestone 9：$\mathbb T^3$ full existence theorem

- **目標**：周期領域版の無条件存在定理を完成させる。

$$
u_0 \in L^2_\sigma(\mathbb T^3)
\;\Rightarrow\;
\exists u,\ u\ \text{is a Leray–Hopf solution on}\ \mathbb T^3.
$$

```lean
theorem exists_lerayHopf_torus3
  (u₀ : L2Sigma Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

- **成果物**：`LerayHopf/ExistenceTorus.lean`

## Milestone 10：$\mathbb R^3$ 版への拡張

- **目標**：Leray original に近い形へ移行する。

$$
u_0 \in L^2_\sigma(\mathbb R^3)
\;\Rightarrow\;
\exists u,\ u\ \text{is a Leray–Hopf solution on}\ \mathbb R^3.
$$

- **内容**：追加で必要となる困難は、無限遠の処理、局所 compactness、pressure recovery、
  cutoff argument、initial trace、局所エネルギー評価との接続。
- **成果物**：`LerayHopf/ExistenceR3.lean`

## 横枝

### Branch A：Leray blow-up lower bound

主線とは独立な不等式スキーマとして小さく形式化できる。

$$
\text{local lifespan estimate}
\;\Rightarrow\;
\lVert u(t)\rVert_{L^p}
\gtrsim
(T-t)^{-\frac12\left(1-\frac3p\right)}.
$$

- **成果物**：`Leray/BlowupLowerBound.lean`

### Branch B：Hou–Wang–Yang 非一意性

Leray–Hopf 解クラスにおける非一意性の主張であり、`LerayHopfSolution` の定義が固まった後に置く。
まずは statement と certificate interface のみ。

```lean
def LerayHopfNonunique : Prop :=
  ∃ u₀, ∃ u v : LerayHopfSolution R3 u₀, u ≠ v
```

- **成果物**：`LerayHopf/NonuniquenessStatement.lean`

## 全体タイムライン

```text
0. Scope fixed
1. LerayHopfSolution definition
2. Existence theorem statement
3. Galerkin compactness package
4. Galerkin energy estimate
5. Torus Fourier / divergence-free API
6. Compactness axioms
7. T³ conditional existence
8. Aubin–Lions / limit passage
9. T³ full existence
10. R³ Leray existence

Side A. Blow-up lower bound
Side B. Hou–Wang–Yang nonuniqueness statement
```

## MVP

最初の現実的な MVP は **Milestone 1–3**：Leray–Hopf 解の定義と、Galerkin package から
存在を導く conditional theorem。ここまでで NS の全解析を Lean 化せずに、プロジェクトの
主張・構造・依存関係を確定できる。
