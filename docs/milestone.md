# Leray–Hopf 弱解存在定理 Lean 形式化ロードマップ

## Phase 0：スコープ固定

対象を三段階に分ける。

[
\boxed{
\mathbb T^3 \text{ conditional}
\to
\mathbb T^3 \text{ full}
\to
\mathbb R^3 \text{ Leray original}
}
]

最初から (\mathbb R^3) 版を狙わない。まず周期境界条件の

[
\Omega=\mathbb T^3
]

で始める。境界・無限遠・tightness を避けるためです。

---

## Milestone 1：Leray–Hopf solution の定義

まず存在定理ではなく，解概念を Lean で定義する。

目標：

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

数学的には，

[
u\in L^\infty_{\mathrm{loc}}([0,\infty);L^2)
\cap L^2_{\mathrm{loc}}([0,\infty);H^1),
]

弱形式の Navier–Stokes 方程式，初期値条件，エネルギー不等式を持つ，という定義。

この段階では，`Prop` placeholder を許してよいです。後で少しずつ展開します。

**成果物**：
`LerayHopf/Basic.lean`

---

## Milestone 2：弱解存在定理の statement 化

次に，存在定理そのものを Lean で述べる。

[
u_0\in L^2_\sigma(\mathbb T^3)
\Rightarrow
\exists u,\ u \text{ is a Leray--Hopf solution}.
]

Lean では例えば：

```lean
theorem exists_lerayHopf_torus3_statement
  (u₀ : L2Sigma Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True := by
  ...
```

この時点では proof は `sorry` でよい。
目的は「何を証明するのか」を固定すること。

**成果物**：
`LerayHopf/Statement.lean`

---

## Milestone 3：Galerkin compactness package

存在証明を一気にやらず，次の抽象定理に分解する。

[
\text{Galerkin 近似列が標準評価と compactness を満たす}
\Rightarrow
\text{Leray--Hopf 解が存在する}.
]

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
```

そして：

```lean
theorem exists_lerayHopf_from_galerkin_package
  (pkg : GalerkinCompactnessPackage u₀) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

ここが最初の中心定理です。

**成果物**：
`LerayHopf/GalerkinPackage.lean`

---

## Milestone 4：Galerkin 近似のエネルギー評価

次に，有限次元 Galerkin 近似 (u_n) に対して

[
\frac12|u_n(t)|_2^2
+\nu\int_0^t|\nabla u_n(s)|_2^2,ds
\le
\frac12|P_nu_0|_2^2
]

を証明する。

核は

[
\langle (u_n\cdot\nabla)u_n,u_n\rangle=0
]

です。
ここは Lean 的にも比較的きれいに切れるはずです。

**成果物**：
`LerayHopf/EnergyEstimate.lean`

---

## Milestone 5：周期領域 (\mathbb T^3) の Fourier–Galerkin 基盤

(\mathbb T^3) 上で divergence-free Fourier modes，射影 (P_n)，Leray projection を整える。

必要な構造：

[
L^2_\sigma(\mathbb T^3),\quad
H^1_\sigma(\mathbb T^3),\quad
P_n,\quad
\Pi_{\mathrm{div}=0}.
]

mathlib には分布・Sobolev・Fourier 周辺の入口はありますが，Navier–Stokes 用の完成 API があるわけではないので，ここはかなり設計が必要です。mathlib docs には `Analysis.Distribution.Sobolev` などの分布/Sobolev 系モジュールがあり，Gagliardo–Nirenberg–Sobolev inequality のファイルもあります。([Leanコミュニティ][1])

**成果物**：
`LerayHopf/TorusFourier.lean`

---

## Milestone 6：Aubin–Lions / compactness を一旦 axiom 化

最難所です。最初は

```lean
axiom aubin_lions_for_navier_stokes_torus3 :
  ...
```

としてよいです。

これにより，先に

[
\text{energy estimate}
+
\text{compactness theorem}
\Rightarrow
\text{weak solution exists}
]

の骨格を完成させる。

PDE の大規模形式化は実例が出始めており，Armstrong–Kempe の De Giorgi–Nash–Moser theory formalization は，弱解・Sobolev・正則性評価を含む本格的 PDE formalization として重要な先例です。([arXiv][2])

**成果物**：
`LerayHopf/CompactnessAxioms.lean`

---

## Milestone 7：(\mathbb T^3) conditional existence theorem

ここで最初の大きな到達点：

[
\boxed{
\text{Aubin--Lions 型 compactness を仮定すれば，
(\mathbb T^3) 上に Leray--Hopf 弱解が存在する}
}
]

Lean statement：

```lean
theorem exists_lerayHopf_torus3_conditional
  (u₀ : L2Sigma Torus3)
  (hcompact : NSCompactnessTheorem Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

これは「弱解存在定理の conditional formalization」です。
ここまで来れば，プロジェクトの背骨は完成です。

**成果物**：
`LerayHopf/ExistenceTorusConditional.lean`

---

## Milestone 8：compactness を axiom から theorem へ

ここからが本格戦です。

必要：

* weak convergence
* Bochner (L^p_t X_x)
* Aubin–Lions
* nonlinear term の極限移行
* lower semicontinuity
* initial trace

この段階で axiom を一つずつ消していく。

**成果物**：
`LerayHopf/AubinLions.lean`
`LerayHopf/LimitPassage.lean`

---

## Milestone 9：(\mathbb T^3) full existence theorem

目標：

[
\boxed{
u_0\in L^2_\sigma(\mathbb T^3)
\Rightarrow
\exists u,\ u \text{ is a Leray--Hopf solution on } \mathbb T^3.
}
]

Lean statement：

```lean
theorem exists_lerayHopf_torus3
  (u₀ : L2Sigma Torus3) :
  ∃ u : LerayHopfSolution Torus3 u₀, True
```

この段階で，周期領域版の弱解存在定理が完成。

**成果物**：
`LerayHopf/ExistenceTorus.lean`

---

## Milestone 10：(\mathbb R^3) 版への拡張

最後に Leray original に近い形へ移る。

[
u_0\in L^2_\sigma(\mathbb R^3)
\Rightarrow
\exists u,\ u \text{ is a Leray--Hopf solution on } \mathbb R^3.
]

ここで追加される困難：

* 無限遠の処理
* 局所 compactness
* pressure recovery
* cutoff argument
* initial trace
* 局所エネルギー評価との接続

**成果物**：
`LerayHopf/ExistenceR3.lean`

---

# 横枝

## Branch A：Leray blow-up lower bound

これは主線の後でも前でもよい。
独立した不等式スキーマとして小さく形式化できる。

[
\text{local lifespan estimate}
\Rightarrow
|u(t)|*{L^p}
\gtrsim
(T**-t)^{-\frac12(1-3/p)}.
]

**成果物**：
`Leray/BlowupLowerBound.lean`

---

## Branch B：Hou–Wang–Yang 非一意性

後回しでよいです。

最初は statement と certificate interface のみ：

```lean
def LerayHopfNonunique : Prop :=
  ∃ u₀, ∃ u v : LerayHopfSolution R3 u₀, u ≠ v
```

Hou–Wang–Yang の結果は，Leray–Hopf 解クラスにおける非一意性の主張なので，この branch は **LerayHopfSolution の定義が固まった後**に置くのが自然です。

**成果物**：
`LerayHopf/NonuniquenessStatement.lean`

---

# 全体タイムライン

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

最初の現実的な MVP は：

[
\boxed{
\text{Milestone 1--3：
Leray--Hopf 解の定義と，
Galerkin package から存在を出す conditional theorem}
}
]

です。
ここまでなら，NS の全解析をまだ Lean 化せずに，プロジェクトの主張・構造・依存関係を明確にできます。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib.html?utm_source=chatgpt.com "Mathlib"
[2]: https://arxiv.org/html/2604.05984v1?utm_source=chatgpt.com "Formalization of De Giorgi–Nash–Moser Theory in Lean - arXiv"

