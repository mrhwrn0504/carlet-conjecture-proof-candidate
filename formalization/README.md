# Lean 形式化

本目录包含 Carlet 零和子空间猜想奇数与偶数适用范围的完整 Lean 证明及其必要依赖。主声明为：

- `Carlet.oddCarletConjecture_main : Carlet.OddCarletConjecture`，保留 `Statement.lean` 的原始奇数次数量词；
- `Carlet.evenDegreeCarlet_unconditional`，证明偶数次数的完整适用范围。

完整默认构建只包含这两项主定理所需的 Lean 依赖闭包。`build.py`、`verify_build.py` 和 `audit_final_theorem.py` 分别负责全量编译、哈希/声明核验和独立主定理公理审计。构建验收回执和摘要位于本目录。

```powershell
python -I build.py
python -I verify_build.py
python -I audit_final_theorem.py
```

通过环境变量 `CARLET_LEAN_BIN` 指定 Lean 4.33.0 可执行文件，通过 `CARLET_MATHLIB_LIBRARIES` 指定包含 mathlib 等已编译依赖的目录。

工具链为 Lean 4.33.0；依赖版本与此次实际验收记录在 `build_receipt.json`。当前脚本复用回执中配置的本机 Lean、mathlib 和兼容缓存路径，因此回执证明的是记录环境上的完整构建与独立核验，尚不表示已验证全新机器上的干净室构建。
