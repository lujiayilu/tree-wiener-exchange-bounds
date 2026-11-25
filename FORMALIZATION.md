# Lean 4 验证范围

使用项目根目录的 `lean-toolchain` 和 `lakefile.toml` 固定 Lean 与 mathlib 的版本。安装 elan 后，在仓库根目录运行：

```sh
lake update
lake exe cache get
lake build
```

| Lean 声明 | 对应论文中的数学步骤 |
| --- | --- |
| `TreeWiener.chord`、`chord_sum` | 给定投影坐标和离路径的高度，证明单顶点弦差不等式，再用非负质量作有限求和。 |
| `TreeWiener.transfer` | 将涉及两个交换点的贡献写成 `pairCost` 后，展开任意实数质量转移引起的目标函数变化。 |
| `TreeWiener.exchange` | 从势函数的弦差下界推出式 (1) 的最大值下界。 |
| `TreeWiener.threshold` | 从正边长下界、载荷差下界和分子下界导出定理 2 共用的数值阈值。 |
| `TreeWiener.sharp` | 对任意实参数验证三顶点路径上两种交换的增益恒等式。 |

文件以实数坐标表述路径几何。把抽象有限加权树转换成这些坐标、从原始无序点对和构造两点分解、从水平集不连通抽取严格谷或峰，以及命题 3 的算法与复杂度证明，仍由论文中的数学论证承担。证明依赖审计在 GitHub Actions 中通过 `#print axioms` 检查上述结果是否依赖 `sorryAx`。
