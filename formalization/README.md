# Carlet 猜想持续核验与 Lean 形式化

`Carlet/MainTheorem.lean` 已证明 `oddCarletConjecture_main : OddCarletConjecture`，并用单独定理展开核对原始量词；`Carlet/EvenDegree.lean` 的 `evenDegreeCarlet_unconditional` 无条件证明偶数次数范围。奇偶两个结论都适用于任意相应基数的有限域。包含两项结论的完整默认构建、独立验证和最终定理公理审计均已通过。

## 精确目标

`Carlet/Statement.lean` 中的原始目标是：任意奇数 n、3≤k、k+3≤n，以及任意基数为 2^n 的有限域 K，存在 k 维 F₂ 子空间，其非零元素逆元和为零。

## 已证明的内容

- 实际子空间的逆元和/多项式系数判据、扩维乘积与维数、线性求解条件。
- 子空间多项式、Artin–Schreier 映射、迹对偶、次高系数、同维零和对应及互补维数对称性。
- 缩放轨道、系数纤维、关联双计数、相邻含 1 子空间比值及非空性。
- 实际含 1 系数概率分布的计数递推及 b=1 边界递推。
- 二次坐标模型的正反构造、自然点函子、显式商环及两侧实际仿射 Spec 同构。尚未识别 reciprocal Proj 的完整几何接口，也未证明后续 IC/权重/迹公式链。
- 实际有限域转移的一、二阶特征矩、一步精确平方范数公式、中心 delta 异常方向映射及单坐标能量界。
- **实际两步能量收缩和高维存在性**：令 E(f)=∑f(x)²，f 为零总和；若 s≥2 且 q≥32s²，则 `E(T_(2s)(T_s f))≤(4s²/q)E(f)`。另证明 s²≤q 时的一步能量非扩张。源码为 `TransferContraction.lean`、`TransferEnergy.lean`、`TwoStepEnergy.lean`、`ProbabilityEnergy.lean`。实际含 1 的系数分布已接入迭代；奇数 k≥11、偶数 k≥10 且 n≥2k+1 时，严格能量界推出零值概率正，再由系数纤维和同维对偶得到零和子空间存在。全量构建审计通过。
- **加法封闭与精确约化**：`AdditiveClosure.lean` 从实际有限域子空间证明，k、l 维零和子空间及 k*l<n 蕴含 k+l 维零和子空间；`LowDimensionReduction.lean` 证明原始奇数次数猜想等价于满足 n≥2k+1 的 k=3、4、5 三个基例。该等价不证明右侧基例。
- **低维基例**：`KloostermanThree.lean` 给出 k=3；`K4AllOddDegreesProbe.lean` 给出所有适用奇数次数的 k=4；`K5NormOneConstructionProbe.lean` 给出所有适用奇数次数的 k=5。k=5 的大次数构造复用已形式化的椭圆曲线 Hasse 界和三维迹空间范数曲线计数，小次数由已有有限域构造覆盖。
- **原始主定理**：`K5NormOneConstructionProbe.lean` 的 `oddCarletConjecture_normOne` 接入既有低维约化；`MainTheorem.lean` 的两个定理分别给出原始命题和显式展开的同一陈述。它们的定向公理输出仅含 `propext`、`Classical.choice`、`Quot.sound`。

## 论文本身与单独桥接的状态

候选论文 v1.1 的几何接口尚未整体认证；当前范数曲线证明是另一条路线，不能据此声称原稿的全部论证正确。用户特别提出的 Θ₅ 四维张成桥接及其 12 个模块已通过隔离式独立重建和公理审计，回执为 `theta5_bridge_audit.json`。证明路线见 `research_notes/carlet-audit-2026-11-02/NORM_ONE_K5_PROOF_ROUTE_2026-11-06.md`。

**数学文献更新（2026-11-05）**：Cheng 的预印本 arXiv:2610.06445 声称完整数学证明；Hou–Zhao arXiv:2502.04545 Corollary 5.5 包含 k=4、k=5 的数学结论。外部文献结论本身不等于 Lean 证明；本项目当前主定理采用形式化的范数曲线、椭圆曲线 Hasse 界与既有高维约化路线。

不得将外部预印本的完整结论或低维定理作为未经证明的关键假设引入。采用替代证明时，须区分其对猜想的证明与对原稿几何论证的认证，并明确来源。

## 当前验证和构建

2026-11-07 完整默认构建和独立验证通过：327 个项目模块、188 个 Hasse 依赖模块、1,188 项打印声明，零编译警告，源码与 OLean 哈希匹配。独立最终审计重新检查原始奇数命题和偶数定理的量词；两项主结果的公理集合均仅为 `propext`、`Classical.choice`、`Quot.sound`。结果见 `build_receipt.json`、`verified_build_summary.json` 和 `final_theorem_audit.json`；此审计不声称重新构建了全部 mathlib 缓存。

工具链为本机 Lean 4.33.0，mathlib 固定源码基线 `db584cd6d46c92f209a44c0f1c829460d327499d`，现阶段复用兼容本地缓存，最终交付仍需可移植打包。

Hasse 依赖为 `vendor/aintlib` 内固定并修补的 Apache-2.0 源码，原快照、完整差异和重建方法见 `research_notes/carlet-audit-2026-11-02/ROUND_42_KLOOSTERMAN_THREE.md`。依赖源码含有未被 Hasse 定理使用的其他 `sorry`；目标定理的 `#print axioms` 不包含 `sorryAx`。

```powershell
python -I build.py
python -I verify_build.py
python -I audit_final_theorem.py
python -I audit_theta5_bridge.py
```

`verify_build.py` 拒绝定向构建回执，只为完整默认模块构建更新摘要。`python -I build.py Carlet/TwoStepEnergy.lean` 等定向命令用于开发调试，之后不能把旧的完整摘要当作修改后的证明证据。

本轮新增的 `check_two_step_energy.py` 独立精确检查了 45 个有限域零和向量；这核对定义和坐标，不替代 Lean 的通用证明。持续目标、历史记录及最终验收条件在研究笔记的 `ONGOING_GOAL.md`。
