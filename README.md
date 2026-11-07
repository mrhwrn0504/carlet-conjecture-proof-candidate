# Carlet 零和子空间猜想：完整 Lean 证明

本仓库只收录本文采用的奇偶次数证明路线：中英文数学论文、完整 Lean 4 证明源码、完整默认构建记录、独立验证脚本和主定理公理审计。

## 定理范围

设 $K$ 是含 $2^n$ 个元素的特征 2 有限域。

- 奇数 $n$：对 $3\le k$ 且 $k+3\le n$，存在 $k$ 维 $\mathbb F_2$ 线性子空间 $E\subseteq K$，使 $\sum_{x\in E\setminus\{0\}}x^{-1}=0$。原始命题定义为 `OddCarletConjecture`，定理为 `Carlet.oddCarletConjecture_main`。
- 偶数 $n$：对 $2\le k$ 且 $k+2\le n$，同样存在这样的子空间；Lean 定理为 `Carlet.evenDegreeCarlet_unconditional`。

上述陈述对每个满足基数条件的有限域统一成立。论文说明了低维构造、Hasse 界、能量迭代、偶数维数递推及它们与 Lean 定理的对应。

## 内容

- `paper/lean-formalization/`：论文中英文 PDF 和可编辑 TeX 源码。
- `formalization/Carlet/`：主定理及证明依赖闭包中的 Lean 源码。
- `formalization/build.py`：完整默认构建入口。
- `formalization/verify_build.py`：检查默认构建清单、源码/OLean 哈希、打印声明和主定理公理。
- `formalization/audit_final_theorem.py`：独立重新核验奇数原命题与偶数定理。
- `formalization/build_receipt.json`、`verified_build_summary.json`、`final_theorem_audit.json`：本仓库快照对应的构建与审计记录。

## 验证

在配置了 Lean 4.33.0、回执记录中的 mathlib 源码基线及 AINTLIB Hasse 依赖的环境中运行：

```powershell
cd formalization
python -I build.py
python -I verify_build.py
python -I audit_final_theorem.py
```

脚本可通过 `CARLET_LEAN_BIN` 指定 Lean 可执行文件，并通过 `CARLET_MATHLIB_LIBRARIES` 指定包含 mathlib 等已编译依赖的目录；未设置时会尝试本机 `lean` 命令和记录中的兼容缓存路径。

完整默认构建与独立审计通过时，奇数主定理及偶数定理的公理集合仅为 `propext`、`Classical.choice` 和 `Quot.sound`；不含 `sorryAx` 或自建未证明公理。回执会记录构建模块、警告数与源码/OLean 哈希。该记录验证的是回执所列的本机 Lean/mathlib/AINTLIB 环境；不将其表述为已在全新机器完成的干净室复现。

## 许可与引用

仓库原创 Lean 源码适用根目录 MIT 许可。论文适用 `paper/LICENSE.md` 中的 CC BY 4.0。AINTLIB 文件保留其 Apache-2.0 许可与上游声明。引用信息见 `CITATION.cff`。
