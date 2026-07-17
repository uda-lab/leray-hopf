# Leray–Hopf 弱解存在定理の Lean 形式化 — 要所・難所・レビュー

本書は、本リポジトリで形式化した **Leray–Hopf 弱解存在定理**（T³ 版 `exists_lerayHopf_torus3`、
ℝ³ 版 `exists_lerayHopf_r3`）について、

- 要所となる**定義・補題**とその役割、
- **証明の自然言語訳**と Lean ソース（ファイル・補題名）との**対応関係**、
- 形式化で**非自明に効いたタクティク**、
- **自然言語証明と Lean のギャップが大きかった箇所**のレビュー（健全性監査が捕捉した穴を含む）、

を一つにまとめたものである。各節の見出し末尾に対応ソースを `［ファイル:補題］` で付す。

---

## 0. 全体像

到達した主定理は次の二つ（いずれも `#print axioms` がプロジェクト公理＋`propext/Classical.choice/Quot.sound`
のみ、`sorryAx` なし）。

```lean
-- LerayHopf/Torus/GalerkinODECapstone.lean
exists_lerayHopf_torus3 (u₀ : L2Sigma)    (ν>0) (T>0) : ∃ F,   Nonempty (LerayHopfSolutionFull    F ν T u₀)
-- LerayHopf/R3/GalerkinODECapstone.lean
exists_lerayHopf_r3      (u₀ : L2Sigma_R3) (ν>0) (T>0) : ∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

`LerayHopfSolution(_R3)Full` は **証明保持型 (proof-carrying)** の構造体で、
弱 NS 方程式 (`WeakFormNS`、分離変数 test `ψ(t)w(x)`)、`[0,T]` 上のエネルギー不等式、
`t→0⁺` の片側初期トレース、エネルギー類（`[0,T]` 上 a.e. の H¹ 所属＋粘性散逸の区間可積分性）
の四つを**実際の証明として**フィールドに持つ。エネルギー類は a.e.-in-time の H¹ 所属＋
可積分性であって、文字通りの Bochner 空間所属 `u∈L²(0,T;H¹_σ)` ではない（`u_aestronglyMeasurable`
は H¹ 値ではなく周囲の L² 値写像としての強可測性）。また `C_w([0,T];L²_σ)` 型の弱連続性は
本構造体のフィールドではない。対応表は `README.md` の claims table を参照。

設計の核心は **抽象層と空間層の分離**：

| 層 | 内容 | T³/ℝ³ |
|---|---|---|
| 抽象層 | `DissipativeEvolution`（H + 正則性汎関数 reg + 粘性形式 + 移流形式）, `WeakFormNS`, `AbstractEnergyLaw` | 共通（ℝ³ で**無修正再利用**） |
| 空間線形層 | `L²_σ`, Leray 射影, 正則性汎関数, 粘性形式 — **公理ゼロで構築** | 各々 |
| 解析フロンティア | 移流形式・Galerkin ODE・Aubin–Lions・極限移行 — かつて公理化、現在は**全て証明済み（公理ゼロ）** | 各々 |

T³・ℝ³ とも現在は **0 公理**（kernel-only）で閉じる。かつては T³ が 4 公理、ℝ³ が 6 公理で閉じており、
ℝ³ の**差の 2 公理**（Galerkin 近似射影族の存在 `r3GalerkinScheme_exists` と空間コンパクト性
`spatial_compactness_R3`）は、T³ 側の対応物（`velocityProjection_n` と `rellich_L2Sigma`）が最初から
証明済みだった一方、ℝ³ では非有界領域ゆえ未証明という、非有界領域固有の追加コストだった。その後
`r3GalerkinScheme_exists`（issue #21）・`spatial_compactness_R3`（issue #2、局所 Rellich への再定式化）
がいずれも証明され、残る全公理（移流形式存在・Galerkin ODE 解・Aubin–Lions・極限移行、T³/ℝ³ 双方）も
issue #22–25 / #44–56 で順次除去された。除去履歴の一次情報は §5 と `HANDOFF.md` §4「The axioms」。

---

## 1. 要所の定義

### 1.1 抽象散逸発展 `DissipativeEvolution` ／ 弱形式 `WeakFormNS` ［EvolutionTriple.lean］

H¹ ヒルベルト空間を**作らない**という方針（"道具づくりで消耗しない"）のもとで、
ゲルファント三つ組 `V↪H↪V'` の代わりに、**ピボット・ヒルベルト空間 `H` + 正則性汎関数 `reg : H→ℝ`**
を抽象化した。`reg` のレベル集合のコンパクト性（＝Rellich）は外から与える。

```lean
structure DissipativeEvolution where
  H : Type*
  instNACG : NormedAddCommGroup H ; instIPS : InnerProductSpace ℝ H ; instCS : CompleteSpace H
  reg : H → ℝ ; reg_nonneg : ∀ u, 0 ≤ reg u
  viscousForm : H → H → ℝ
  convForm : H → H → H → ℝ ; convForm_antisymm : ∀ u v w, convForm u v w = - convForm u w v
  isTest : H → Prop                          -- 弱形式のテスト関数クラス
```

`WeakFormNS ν T E u`：時間テスト関数 `ψ : ℝ→ℝ` が C¹ かつ **開区間 (0,T) にコンパクト台**
（`tsupport ψ ⊆ Set.Ioo 0 T` ⇒ 端点項が自動消滅）、空間テスト `w` が `E.isTest w` を満たすとき、
```
∫ t in 0..T, (-(⟪u t, w⟫) · ψ'(t) + ψ(t) · (ν · viscousForm(u t, w) + convForm(u t, u t, w))) = 0
```
**注**：`b(u,u,u)=0`（散逸構造の鍵）は公理ではなく、反対称性からの補題
`DissipativeEvolution.convForm_self_zero`（`have := convForm_antisymm u u u; linarith`）。

### 1.2 散逸下のエネルギー法則 `AbstractEnergyLaw` ［EnergyEstimate.lean］

任意の実内積空間 `H` 上の曲線 `u:ℝ→H` に対し、内積形式の ODE 法則
`⟪u'(t),u(t)⟫ + D(u(t)) + B(u(t),u(t),u(t)) = 0`（`B w w w = 0`, `D ≥ 0`）から
エネルギー非増加 `½‖u(t)‖² ≤ ½‖u(s)‖²` を導く（後述 2.3）。これも抽象で、ℝ³ にそのまま効く。

### 1.3 T³ の発散ゼロ空間 `L2Sigma` ［Torus/DivergenceFree.lean, Torus/Leray.lean］

`L2VF := Lp (EuclideanSpace ℝ (Fin 3)) 2 haarTorus3`（＝`L²(𝕋³;ℝ³)`）。Fourier 係数による発散記号
```lean
divSymbol k : L2VF →L[ℝ] ℂ,  u ↦ ∑ j, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k
L2Sigma : Submodule ℝ L2VF := ⨅ k, (divSymbol k).ker          -- 連続汎関数の核の可算交叉 ⇒ 閉
```
**設計上の要点**：M2 計画では「div-free モードの張る空間の閉包＝Fourier 対角」を**公理**に予定したが、
`⨅ k, ker` と直接定義することで**構成から**メンバーシップが `DivFreeL2` と一致し、公理を消去した
（閉部分空間＝ヒルベルト構造＋Leray 射影が無料）。

### 1.4 ℝ³ の発散ゼロ空間 `L2Sigma_R3` — 弱発散×Schwartz テスト ［R3/DivergenceFree.lean］

ℝ³ では Fourier 級数の離散添字がない。L²-Fourier 変換 `𝓕 u` の**点ごとの値** `ξ·û(ξ)=0` は
同値類の代表元問題（後述 4.2 と同種の罠）に触れるため**採らない**。代わりに**超関数的弱発散**：

```lean
-- 各 Schwartz φ に対する連続線形汎関数  divTestFunctional φ u = ∑ j, ∫ u_j (∂_j φ)
divTestFunctional (φ : 𝓢(ℝ³,ℝ)) : L2VF_R3 →L[ℝ] ℝ :=
  ∑ j, (innerSL ℝ ((lineDerivOpCLM ℝ _ (EuclideanSpace.single j 1) φ).toLp 2 volume)).comp
        (L2VF_projComponent_R3 j)
L2Sigma_R3 : Submodule ℝ L2VF_R3 := ⨅ φ : 𝓢(ℝ³,ℝ), (divTestFunctional φ).ker
```
**数学的正しさ**：`div u = 0`（弱）⇔ `∀φ, ∫ div u · φ = -∑_j ∫ u_j ∂_j φ = 0` ⇔ `∀φ, divTestFunctional φ u = 0`。
符号は `=0` 条件に効かない。**ここが ℝ³ で最も非自明に "上手くいった" 構成**：T³ の `⨅ ker` パターンを
そのまま流用でき（`isClosed_iInter` + `ContinuousLinearMap.isClosed_ker`）、Leray 射影も無料で出る。
実際に効いた mathlib API：`lineDerivOpCLM`（偏微分、`pderivCLM` は 2025-11 非推奨）、`SchwartzMap.toLp`
（`volume` が `IsAddHaarMeasure` ⇒ `HasTemperateGrowth` が自動発火）、`innerSL ℝ`。

### 1.5 正則性・粘性汎関数

- T³：`h1EnergySq u = ∑_j ∑'_k (1+∑_i k_i²)‖û_j(k)‖²`、`viscousFormSq ν u = ν∑_j∑'_k (2π)²(∑_i k_i²)‖û_j(k)‖²`
  ［Torus/H1Sigma.lean］。`(2π)²` は荷重項（`∂_xᵢ e^{2πi k·x}` の係数 `(2π kᵢ)`）。
- ℝ³：`memH1VF_R3` は `TemperedDistribution.MemSobolev 1 2`（Bessel ポテンシャル）で**厳密構築**、
  `stokesTestPairing_R3`/`viscousFormSq_R3` は L²-Fourier 変換 `Lp.fourierTransformₗᵢ` を用いた
  **スペクトル積分** `∫ ξ, (2π)²‖ξ‖²·…`（`smulLeftCLM` 装置は不要）［R3/Regularity.lean］。

---

## 2. 要所の補題：自然言語訳 + Lean 対応

### 2.1 ＜山場＞ Fourier-tail Rellich コンパクト埋め込み ［Torus/RellichEmbedding.lean: `rellich_seq_compact`, `H1_ball_totallyBounded`］

**主張**：H¹ ノルムが一様有界な `L²(𝕋³;ℂ)` 列は L² 収束部分列をもつ（`H¹↪L²` のコンパクト性）。
**これがプロジェクトで最も難度の高い "本物の解析" であり、公理ゼロで証明できたのが最大の成果。**

**自然言語証明**（L1→L5）：
1. **Parseval** `‖f‖² = ∑'_k ‖f̂(k)‖²`。Lean：`repr` が線形等長（`LinearIsometryEquiv.norm_map`）＋
   `lp.norm_rpow_eq_tsum`（`p=2`）。［`L2C_norm_sq_eq_tsum_coeff_sq`］
2. **截断残差＝高周波テイル** `‖f - P_N f‖² = ∑_{k∉box} ‖f̂(k)‖²`。`P_N` の係数公式
   `fourierProjection_n_mFourierCoeff`（箱の内は恒等・外はゼロ）＋ `tsum_subtype_eq_of_support_subset`。
3. **テイル評価** `∑_{k∉box_N} ‖f̂‖² ≤ M²/(1+N²)`。`k∉box_N ⇒ ∃i,|k_i|>N ⇒ 1+|k|² ≥ 1+N²`、
   `Summable.tsum_le_tsum` で単調性、最後に正の量で割る（`le_div_iff₀`）。［`H1_tail_bound`］
4. **H¹ 球上の一様 L² 近似**：`ε>0` に対し `N` を `M/√(1+N²)≤ε` ととる（`exists_nat_gt`）。［`H1_ball_uniform_L2_approx`］
5. **全有界性**：`Metric.totallyBounded_iff`。各 `ε` で、`P_N`（有限次元ゆえ**コンパクト作用素**）の像が
   有限次元（＝固有）部分空間の有界閉球＝コンパクトなので有限 ε/2-網をとり、三角不等式で `‖f-y‖≤ε`。
   ［`H1_ball_totallyBounded`］
6. **列コンパクト形**：閉包が全有界＋完備 ⇒ コンパクト（`TotallyBounded.isCompact_of_isComplete`）、
   `IsCompact.tendsto_subseq` で収束部分列。［`rellich_seq_compact`］

**効いた非自明タクティク**：有限次元 ⇒ 固有 ⇒ 局所コンパクトの連鎖
（`RCLike.properSpace_submodule`, `isCompactOperator_of_locallyCompactSpace_dom`,
`isCompact_closedBall` の像）。テイル和の subtype 化（`Summable.subtype`, `tsum_subtype_le`）。

### 2.2 発散ゼロ列への Rellich ＋対角列 ［Torus/H1Sigma.lean: `rellich_L2Sigma`］

**主張**：`u n ∈ L2Sigma`、`memH1VF (u n)`、`h1EnergySq (u n) ≤ M²` ⇒ `L2VF` 収束部分列＋極限も `L2Sigma`。

**自然言語証明**（成分分解＋対角化）：
- **Step A**：`h1EnergySq` は成分ごとの非負和。`Finset.single_le_sum` で各成分の H¹ 和 ≤ `h1EnergySq ≤ M²`。
- **Step B**：`rellich_seq_compact` を **j=0,1,2 と三段入れ子**で適用（`φ₀` の上で `φ₁`、その上で `φ₂`）。
  対角列 `φ = φ₀∘φ₁∘φ₂`（`StrictMono.comp`）上で三成分が同時に L² 収束。極限は `![g₀,g₁,g₂]`（`fin_cases j`）。
  収束部分列は `ht₀.comp ((hφ₁.comp hφ₂).tendsto_atTop)` で前段の収束を引き継ぐ。
- **Step C–D**：複素埋め込みの**実部**で実成分へ（`re_compLpL_projComponentC`）、
  `L2VF_injectComponent` の連続性＋`tendsto_finsetSum`＋成分分解恒等式 `sum_inject_projComponent` で再合成。
- **Step E**：極限の発散ゼロ性は**閉性から**：`isClosed_L2Sigma.mem_of_tendsto`（各 `u(φn)∈L2Sigma`、
  `Filter.Eventually.of_forall`）。極限を**明示再構成せず**、`L2Sigma` が閉集合であることだけで結論する点が綺麗。

**レビュー**：Step A の `hH1`（成分の summable）が**本質的に必要**。`h1EnergySq ≤ M²` だけからは
summable は出ない（tsum 規約、後述 4.1）ので、`rellich_seq_compact` の仮説に渡すために `memH1VF` を別途仮定する。

### 2.3 抽象 Galerkin エネルギー恒等式 ［EnergyEstimate.lean: `abstract_galerkin_energy_identity`］

**主張**：内積形 ODE 法則＋`B w w w = 0` ⇒ `d/dt(½‖u(t)‖²) = -D(u(t))`。
**自然言語**：`d/dt‖u‖² = 2⟪u,u'⟫`、ODE から `⟪u',u⟫ = -D(u)-B(u,u,u)`、`B(u,u,u)=0`、内積対称性で結論。
**Lean 対応と "詰まり"**：`HasDerivAt.norm_sq` で `d/dt‖u‖² = 2⟪u,u'⟫` は出るが、**1/2 倍**が曲者。
`HasDerivAt.const_mul` が当該ファイルの import 閉包外だったため、
`(hasDerivAt_const t (1/2)).inner h1`（定数 1/2 との内積として微分）で代用し `simp`＋`ring`。
→ **これは数学的ギャップではなく Lean 人間工学のギャップ**（4.9）。FTC-2
`intervalIntegral.integral_eq_sub_of_hasDerivAt` で積分してエネルギー不等式、`EnergySkeleton` へ橋渡し。

### 2.4 Galerkin 射影の実数値性 ［Torus/VelocityGalerkin.lean: `velocityProjection_n_component_comm`, `conjL2C_fourierProjection`］

**主張**：実ベクトル場の成分は複素埋め込みされるが、対称箱上の Fourier 截断は実数値性を保つ
（`Re(P_n(û_j)) = P_n(実成分)`）。
**自然言語**：実関数の Fourier 係数は共役対称 `f̂(-k)=conj f̂(k)`、箱 `k↦-k` 対称、ゆえに `P_n` も共役対称性を保つ。
**Lean 対応**：共役作用素 `conjL2C`（`Complex.conjCLE` の `compLpL` 持ち上げ）の**不動点**として実数値性を表現。
`conjL2C_fourierProjection`：`conjL2C f = f ⇒ conjL2C(P_n f)=P_n f`（係数反射 `mFourierCoeff3_conjL2C` ＋
箱対称 `neg_mem_fourierBox`）。`ofRealLp_reLp_eq_self` で実部往復が恒等。
**レビュー**：自然言語では「実だから実」で一行だが、componentwise 複素化の選択ゆえ
**Lean では明示の共役-不動点議論が必要**になった（4.8）。`filter_upwards … with x hx`（Lp の a.e. 等式）が随所で効く。

### 2.5 閉部分空間・直交射影（T³/ℝ³ 共通パターン）

`⨅ (連続線形汎関数).ker` ⇒ `simp [Submodule.coe_iInf]; isClosed_iInter (ContinuousLinearMap.isClosed_ker _)`、
`IsClosed.completeSpace_coe` ⇒ `CompleteSpace` ⇒ `HasOrthogonalProjection`（優先度 100 インスタンス自動発火）
⇒ `orthogonalProjectionOnto`。**T³ も ℝ³ もこの 4 行で空間が立つ**のが設計上の旨味。

---

## 3. 効いた非自明タクティク・イディオム（まとめ）

| イディオム | 用途 | 代表箇所 |
|---|---|---|
| `MeasureTheory.Lp.ext` + `filter_upwards [coeFn_compLpL …] with x h…` | Lp 等式を a.e. 等式に落として点ごとに計算 | VelocityGalerkin, H1Sigma, R3/* |
| `Submodule.coe_iInf` + `isClosed_iInter` + `ContinuousLinearMap.isClosed_ker` | 発散ゼロ空間の閉性 | Leray, R3/DivergenceFree |
| `lp.norm_rpow_eq_tsum` + `LinearIsometryEquiv.norm_map` | Parseval | RellichEmbedding |
| `TotallyBounded.isCompact_of_isComplete` + `IsCompact.tendsto_subseq` | 全有界 ⇒ 列コンパクト | RellichEmbedding |
| `isCompactOperator_of_locallyCompactSpace_dom` + `RCLike.properSpace_submodule` | 有限次元 ⇒ コンパクト作用素 | RellichEmbedding |
| `StrictMono.comp` + `.tendsto_atTop`、`fin_cases`、`![g₀,g₁,g₂]` | 三成分対角部分列 | H1Sigma |
| `IsClosed.mem_of_tendsto` + `Filter.Eventually.of_forall` | 閉集合中の極限 | H1Sigma |
| `(hasDerivAt_const _ c).inner h` | `const_mul` 不在を回避した 1/2 倍 | EnergyEstimate |
| `Submodule.inner_starProjection_left_eq_right`（自己随伴） | Fourier 乗数公式の導出 | GalerkinProjection |
| `lineDerivOpCLM` + `SchwartzMap.toLp` + `innerSL ℝ` | ℝ³ 弱発散汎関数 | R3/DivergenceFree |
| `𝓕 := Lp.fourierTransformₗᵢ` の `instFourierTransform` + `Lp.instCoeFun` 点値 + `integral_nonneg`/`positivity` | ℝ³ 粘性スペクトル積分 | R3/Regularity |
| `Exists.choose` / `choose_spec`（`obtain` 不可な Type 値ゴール） | A3 の存在子から構造体を組む | (R3/)GalerkinODECapstone |

---

## 4. ＜レビューの核心＞ 自然言語証明と Lean のギャップが大きかった箇所

健全性監査（Codex `--effort xhigh`、T³ で 8 ラウンド・ℝ³ で 2 ラウンド＋最終）が捕捉した穴の多くは、
**"自然言語では暗黙に処理される約束事" が Lean では明示を要求する**ことに由来する。重要度順に。

### 4.1 ＜最大＞ `tsum` 規約：非可算和は非可算和でなく "0"
mathlib では `∑' k, f k = 0`（`+∞` ではない）if `f` が非可算和。ゆえに `h1EnergySq`/`viscousFormSq` は
**H¹ の外でも有限値（実質 0）を返す**。自然言語では「H¹ の外では H¹ ノルム＝+∞」なので
「エネルギー不等式が成り立つ ⇒ 解は H¹」が自動だが、Lean では**エネルギー不等式が tsum 崩壊で
空虚に成立**しうる。
→ 対策：A3 の結論に **`energy_class` フィールドを証明保持**で追加
（`∀ᵐ t, memH1VF (u t)` ＋ `IntervalIntegrable (viscousFormSq ν ∘ u)`）。これにより a.e.-in-time
の H¹ 所属と粘性散逸の可積分性が強制される。ただしこれは文字通りの Bochner 空間所属
`u∈L²(0,T;H¹_σ)` の証明ではない — `u_aestronglyMeasurable` は H¹ を値域とする強可測性ではなく、
周囲の L² 空間を値域とする強可測性のフィールドだからである。
（Codex T³ v5 / ℝ³ にも継承。）

### 4.2 測度ゼロ代表元の不変性：弱解の "良い代表元"
自然言語の「弱解 `u(t)`」は a.e. 同値類で、点ごとの主張（各 `t` でのエネルギー不等式・初期トレース）は
暗黙に**良い代表元**（弱連続版）について語る。Lean の曲線 `u:ℝ→L2Sigma` は具体的代表元であり、
**任意の強 L² 代表元**に点ごとの性質を課す公理は、零集合スパイクで**偽**になる。
→ 対策：A3 を**存在型**にし（`∃ u, …`）、さらに `∀ᵐ t, u t = alPkg.u t`（Aubin–Lions 極限への a.e. リンク）を
第一連言子に置く。存在型ゆえ零集合の病理で偽化せず、かつ「良い代表元の存在」という正しい主張になる。
（Codex T³ v6/v7。）**最も微妙な測度論的健全性点。**

**注（issue #146）**：`Torus/TraceEnergy.lean` の限定的な構成では、この良い代表元が実際に
`[0,T]` 上で弱連続であることを内部補題として証明する経路もあるが、この弱連続性
`C_w([0,T];L²_σ)` は最終的な公開構造体 `LerayHopfSolution(_R3)Full` の**フィールドとして
公開されていない**——公開されているのは `t→0⁺` の片側初期トレースのみである。したがって
「良い代表元＝弱連続版」という自然言語の直感は、内部の構成手法としては真だが、公開 API の
型が保証する主張ではない。これは本 repo の定義選択であり、証明の欠落ではない。

### 4.3 `(2π)²` 正規化
自然言語では規約に吸収されて見えないが、`e^{2πi k·x}` 規約では `∂` が `2π k` を生むので
勾配エネルギーに `(2π)²` が要る。落とすと粘性形式が誤り。
→ `viscousFormSq` に明示し、`stokes_eq` 経由で荷重化（Codex T³ defect 8）。

### 4.4 Stokes 形式の定義域（∞ off H¹）
`∫∇u:∇u` は H¹ の外で `+∞`。ゆえに **L²_σ 全体上の実数値双線形形式としては存在しない**。
自然言語はこれを流すが、Lean では「対角＝`viscousFormSq 1` の総形式」を公理化すると**偽**（Codex T³ v4）。
→ 対策：粘性形式を**脱公理化**（Fourier 乗数 `stokesTestPairing` として具体的に定義）し、
散逸は別途 `viscousFormSq` ＋ `energy_class` で扱う。**A4 は移流形式のみに縮小**（信頼ベース最小化）。

### 4.5 大域 vs 局所コンパクト性（ℝ³ 固有）
自然言語の Leray は「コンパクト性」を緩く使うが、ℝ³ では Rellich が**大域では破綻**
（質量が無限遠へ逃げる）。大域強 L² 収束は tightness なしでは偽。
→ 対策：`spatial_compactness_R3` を**球上の局所**収束 `∀R, ∫_{B_R}‖z_ψn-g‖²→0`（局所 Rellich）に再定式化。
これは tightness なしで**真**であり、Schwartz テストの減衰が裾を一様制御するので極限移行が回る
（Codex ℝ³ v1）。**ℝ³ の本質的追加困難。**

### 4.6 弱形式のテスト関数クラス（Galerkin vs Schwartz）
「弱解」は**滑らかな発散ゼロ関数**でテストする。`isTest` を Galerkin 不動点クラス
`IsGalerkinTest_R3`（スキーム依存・潜在的に小さい）にすると、定理名が主張する**標準的弱形式**より狭く、
過大主張になる。
→ 対策：`r3Evolution.isTest := IsSchwartzDivFree_R3`（標準 Schwartz 発散ゼロ）に修正。
（Codex ℝ³ 最終チェックが捕捉。`IsGalerkinTest_R3` は Galerkin 近似の有限次元テスト空間としてのみ残す。）

### 4.7 非退化（`b≠0`）：抽象移流形式は 0 で充足されうる
自然言語の「移流形式」は当然 `∫(u·∇)v·w` だが、Lean で `b` を反対称・三線形だけで抽象化すると
**`b:=0` が全条件を充足** ⇒ 定理が密かに **Stokes/熱方程式**を証明（過大主張）。
さらに ℝ³ では素朴な Fourier 二重積分は非可算和規約で 0 に潰れる恐れ（再び 4.1）。
→ 対策：`b_galerkin` で `b` を**具体的移流積分にピン留め**。
T³ は `galerkinConvection`（有限 Fourier 和）、ℝ³ は `convIntegralSchwartz = ∑_{i,a}∫ u_a(∂_a v_i)w_i`
（Schwartz 場上の真の積分、`lineDerivOpCLM`＋点積＋積分）。これで `b=0` を排除し、真の移流形式を証人にできる。
（Codex T³ defect 4 / ℝ³ で再点検。）

### 4.8 実数値性の明示議論（T³）
4.2.4 の通り、「実だから実」が componentwise 複素化では**共役-不動点議論**に化ける。
自然言語の一行が Lean では一節（`conjL2C` ＋係数反射＋対称箱）。

### 4.9 微分の定数倍など人間工学的ギャップ
`d/dt(½‖u‖²)` の 1/2 倍（`HasDerivAt.const_mul` 不在）、ベクトル値 `toLp` の煩雑さ（成分版で回避）、
`Exists` の Type 値ゴールへの消去不可（`choose`/`choose_spec` で対処）など。**数学ではなく Lean/ライブラリ事情**。

### 4.10 多線形性の欠落が生む "隠れ非整合"（ℝ³ で顕在化した別系統）
`stokes`/`b` を対角だけ拘束し多線形性を課さないと、`∀F` 量化の Galerkin ODE が `w=0` で
`ν·stokes(u,0)=0` を要求 ⇒ 病的 `F` で**偽**（`False` 導出可能）。
→ 多線形フィールド（`b_add_i`/`b_smul_i`、`stokes` の双線形・対称）を追加して排除（Codex T³ v1/v3）。
**自然言語では "形式は当然線形" で済むが、抽象公理では明示が必須。**

---

## 5. 何が証明され、何が公理か（信頼ベースの所在・現状は公理ゼロ）

**現在、両定理とも 0 プロジェクト公理**（`#print axioms` は `propext`/`Classical.choice`/`Quot.sound`
の kernel 公理のみ）。以下は**最初から公理ゼロで構築されたもの**と、**かつて公理化され、後に
定理として除去されたもの**の内訳。

**最初から公理ゼロで証明したもの**（"道具"はここまで本物）：
- 抽象層全体（`DissipativeEvolution`/`WeakFormNS`/`AbstractEnergyLaw` と諸補題）。
- T³ 空間線形層：`L2Sigma`（閉発散ゼロ空間）、Leray・Galerkin 射影、Fourier 乗数公式、
  **エネルギー恒等式・不等式**、そして**山場の Fourier-tail Rellich** `rellich_seq_compact`/`rellich_L2Sigma`。
- ℝ³ 空間線形層：`L2Sigma_R3`（弱発散×Schwartz、閉）、Leray 射影、`memH1VF_R3`（MemSobolev）、
  粘性形式（Fourier 積分）、移流積分 `convIntegralSchwartz`。

**かつて公理化され、後に定理として除去されたもの**（mathlib 不在の解析フロンティアを埋めた順）：

| | T³（かつて 4 公理） | ℝ³（かつて 6 公理） | 数学的内容 | 除去 |
|---|---|---|---|---|
| 移流形式存在 | `torus3_NSForms_exist` → `torusConvectionGap_exists` | `r3_NSForms_exist` → `r3ConvectionGapOp_exists` | `(u·∇)v` の L² 化（具体ピン留めで非退化） | T³: issue #22, #53/PR #62。ℝ³: issue #56/PR #60 |
| Galerkin ODE | `galerkin_ode_solution` | `galerkin_ode_solution_R3` | 有限次元 Picard–Lindelöf＋一様評価 | issue #24 / #10 |
| Aubin–Lions | `aubin_lions` | `aubin_lions_R3` | 時間コンパクト性（空間半は最初から証明済み） | T³: issue #23（mode-wise spectral route）。ℝ³: issue #15/#44 + #46 PR-4（spacetime precompactness） |
| 極限移行 | `galerkin_limit_passage` | `galerkin_limit_passage_R3` | 非線形項の極限（強 L² が誤差を消す） | T³: issue #25/PR #75。ℝ³: issue #4/PR-6 |
| Galerkin 射影族 | （最初から証明済み `velocityProjection_n`） | `r3GalerkinScheme_exists` | ℝ³ は周波数截断が無限次元／Lp 乗数不在 | issue #21 |
| 空間コンパクト性 | （最初から証明済み `rellich_L2Sigma`） | `spatial_compactness_R3` | ℝ³ は大域 Rellich 破綻 ⇒ 局所版 | issue #2 |

T³ が最初から**空間半を証明済 `rellich_L2Sigma` で割り当て**ていた一方、ℝ³ の差の 2 公理
（Galerkin 射影族・空間コンパクト性）が**まさに「T³ で最初から証明できた二つ」に対応していた**の
が非有界領域固有の追加コストだった——という構図は issue #21・#2 で解消されている。現在の公理台帳・
除去履歴の一次情報は `HANDOFF.md` §4「The axioms」および `docs/STATUS.md`。

---

## 6. プロセス上の所見

- **Codex 敵対的監査が設計を駆動**：上記 4 節の穴の多くは監査で初めて顕在化した。
  T³ は 8 ラウンドかけて健全化（隠れ非整合・偽の 3 次元評価・Stokes 定義域・代表元不変性…）、
  その教訓を ℝ³ に**先回り適用**したため 2 ラウンドで approve に収束。
- **役割分担**：定義・公理・構造体は `lean-coder`、証明本体は `fable`（prover）、
  オーケストレータ（私）は逐次化と Codex 実行と docs のみ（Lean は直接編集しない）。
- **抽象化の配当**：ℝ³ ピボットで抽象層を**無修正再利用**でき、mathlib の ℝ³ 調和解析
  （`Lp.fourierTransformₗᵢ`・`MemSobolev`）が想定以上に充実していたため、空間層も公理ゼロで構築できた。

---

### 付録：主要ファイル対応表

| ファイル | 主な内容 |
|---|---|
| `LerayHopf/EvolutionTriple.lean` | 抽象 `DissipativeEvolution`, `WeakFormNS`, `convForm_self_zero` |
| `LerayHopf/EnergyEstimate.lean` | `AbstractEnergyLaw`, エネルギー恒等式・不等式・非増加 |
| `LerayHopf/Torus/Leray.lean`, `Torus/DivergenceFree.lean` | T³ `L2Sigma`, `divSymbol`, Leray 射影 |
| `LerayHopf/Torus/GalerkinProjection.lean`, `Torus/VelocityGalerkin.lean` | Fourier 截断・速度 Galerkin 射影・実数値性 |
| `LerayHopf/Torus/RellichEmbedding.lean` | **Fourier-tail Rellich**（L1–L5, `rellich_seq_compact`） |
| `LerayHopf/Torus/H1Sigma.lean` | `h1EnergySq`, `viscousFormSq`, **`rellich_L2Sigma`**（成分＋対角） |
| `LerayHopf/Torus/SolutionInterfaces.lean` | T³ 支援層（組立ヘルパ）；主定理本体は `Torus/GalerkinODECapstone.lean` の `exists_lerayHopf_torus3`（0 公理） |
| `LerayHopf/R3/Domain.lean` | ℝ³ L² 空間・成分射影 |
| `LerayHopf/R3/DivergenceFree.lean` | **弱発散×Schwartz** `L2Sigma_R3`・Leray 射影 |
| `LerayHopf/R3/Regularity.lean` | `memH1VF_R3`(MemSobolev), Fourier 積分粘性形式 |
| `LerayHopf/R3/SolutionInterfaces.lean` | ℝ³ 支援層（組立ヘルパ）；主定理本体は `R3/GalerkinODECapstone.lean` の `exists_lerayHopf_r3`（0 公理） |
| `docs/STATUS.md` | 公理台帳・Codex 監査ログ |
