# Scratch CAS 内核设计

目标不是做一个完整的 CAS，这是不可能的；而是在 Scratch 的执行模型里做到可扩展的符号计算。

## 1. 运行约束

Scratch/goboscript 的关键约束：

- 没有指针/对象，列表是唯一的动态容器。
- 自定义积木的局部变量在递归时行为未定义。
- 没有 `break`/`continue`/`for`，只有 `repeat`/`until`/`forever`。
- 字符串只能逐字符处理；列表下标从 1 开始。
- TurboWarp 的 `nowarp` 积木没有 500ms 限制；原生 Scratch 的 warp 线程每次最多跑 500ms。

因此：

1. **不使用递归**。解析、树遍历、打印全部用显式栈/工作列表。
2. **每个节点用整数 ID 表示**，ID 是列表下标，`0` 表示 null/错误。
3. **每个命令开始时重置 arena**，避免跨命令的垃圾和碎片；所有工作列表在每次算法开始前 `delete` 或用栈指针覆盖。
4. **所有 `local` 只出现在 proc/func 内**，这是 gobo 的 bug 。

## 2. 节点 arena

`lib/arena.gs` 用一个 struct list：

```goboscript
struct Node {
    kind, a, b, num, den, txt, sig, deg
}
list Node nodes;
```

- `nodes[0]` 不存在；列表第 1 项是 dummy，真实节点从 ID 2 开始。`node_count` 指向最后一个真实节点。
- `new_node(...)` 追加一个节点并返回 ID；达到 `MAX_NODES` 时设置 `err` 并返回 0。
- 节点字段：
  - `kind`：`K.Num`、`K.Var`、`K.Add`、`K.Mul`、`K.Pow`、`K.PowE`、`K.Sin` … `K.E`、`K.Float`。
  - `K.Float` 只由嵌套的 `eval`/`approx` 产生：`num` 存浮点值，`txt` 存格式化小数；它参与普通算术，但不再保持精确有理数。
  - `a`/`b`：子节点 ID；一元函数只用 `a`。
  - `num`/`den`：有理数字面量；对 `Pow` 表示整数指数；`PowE` 用 `b` 指向指数表达式。
  - `txt`：变量名（`K.Var`）。
  - `sig`：规范签名，用于结构相等、排序、同类项合并。
  - `deg`：总次数，用于加法项排序。
- 不存 Sub/Div/Neg：
  - `a - b` → `Add(a, Neg(b))`
  - `a / b` → `Mul(a, Pow(b, -1))`
  - `Neg(x)` → `Mul(-1, x)`（数字直接取反）
- 整数指数用 `Pow`（`num` 存指数）；有理数或含变量的指数用 `PowE`（`a` 底数，`b` 指数节点）。这样整数幂仍可精确合并/展开，同时支持 `5^x`、`x^x`、`x^2.5`。

### sig 是什么

`sig` 是节点的规范字符串：

- 数字：`N:num/den`（实际是 `"N" & 分子 & "/" & 分母`）
- 变量：`V:name`
- 加法：`A[term1;term2;...]`，项已排序
- 乘法：`M[factor1;factor2;...]`，因子已排序
- 幂：`P(base,exp)`
- 函数：`F<kind>(child)`
- 常量：`PI`、`E`

这样 `sig` 相等就可以用来判断两个规范化子表达式是否相同。注意：**只有 `mk_add`/`mk_mul` 返回的根节点 sig 是完整的扁平签名**；二叉链内部的中间节点 sig 为空，绝不被外部当作表达式使用（构造器在扁平化时会穿过链）。

## 3. 规范形式与智能构造器

所有表达式在解析时就直接经过 `mk_add`/`mk_mul`/`mk_pow` 构造，因此树里不存在未化简的 `0+x`、`1*x`、`x^1` 等。

### mk_num

- 调用 `rat_norm`：约分、分母为正、检查 `2^53` 安全范围。
- 数字 0 统一成 `0/1`。
- 溢出时设置 `err`，不静默转 float。

### sqrt 的数字化简

`mk_func` 对 `K.Sqrt` 的数字参数做平方因子提取：

- `sqrt(0) → 0`；`sqrt(1) → 1`。
- 分子、分母分别提取最大平方因子：`k² | n`、`m² | d`，得到
  `sqrt(n/d) = (k/m) * sqrt((n/k²)/(d/m²))`。
- 剩余根式为 1 时直接返回有理数；否则用 `new_func_raw` 建根式节点（不重复化简），再与系数相乘。
- 数字超过 `MAX_SQRT = 1,000,000` 时跳过化简，保留 `sqrt(...)`。
- `sqrt(u)^2 -> u` 等幂规则由 `lib/rules.gs` 的规则引擎处理，因此 `sqrt(8)*sqrt(2) -> 4`。
- `build_product` 会把 `pow_node` 返回的数字因子折回系数，避免出现 `2*2`。

### mk_add

1. 扁平化两侧的 `Add`（显式栈），得到项列表。
2. 对每个项拆成 `系数 × 基`：
   - `Num`：系数是数字，基为 0。
   - `Mul`：扁平化因子，数字因子乘进系数，非数字因子用 `mk_mul` 重建基。
   - 其他：系数 1，基是节点本身。
3. 按基的 `sig` 合并同类项，系数用精确有理数相加；系数为 0 的项丢弃。
4. **Pythagorean pass**：扫描 `sin(u)^2` 与 `cos(u)^2`，若参数 sig 相同且系数相同，删除两项并把系数加到常数项。这是 `sin(x+y)^2 + cos(y+x)^2 -> 1` 的实现。
5. 为每个剩余项构造节点（`系数 * 基`），按“次数降序 → 项类型 rank → sig”排序。
6. 用二叉 `Add` 链重建，根节点写扁平 `A[...]` sig，`deg` 取最大次数。

`term_order_rank` 让变量/变量幂排在乘积项前面，常数排最后，因此常见输出更像 `x - 2*y + 1` 而不是 `-2*y + x + 1`。

### mk_mul

1. 扁平化两侧的 `Mul`（显式栈）。
2. 数字因子乘进系数；`Pow` 因子拆成 `底数^指数`；`PowE` 作为不透明因子保留；其他因子指数为 1。
3. 用底数的 `sig` 合并同底数，指数相加；指数为 0 的因子丢弃。
4. 按底数 `sig` 排序。
5. 重建：系数（若不是 1）在前，然后各因子 `pow_node(base, exp)`，用二叉 `Mul` 链连接；根节点写扁平 `M[...]` sig。
6. 不自动做分配律；`(x+1)*(x-1)` 保持乘积，只有 `expand` 才展开。

### mk_pow

- 指数 0 → 1；指数 1 → 底数。
- 数字底数：精确有理数幂。
- `Pow` 底数：循环合并指数。
- `mk_pow_expr`：指数是整数 `Num` 时转 `mk_pow`；否则建 `PowE`，用于一般幂。
- `Mul` 底数：分配为各因子幂的乘积（例如 `(2*x)^2 -> 4*x^2`）。
- `Add`/函数/变量底数：建 `Pow` 节点。
- 指数绝对值超过 `MAX_EXP` 报错。

## 4. 解析

`lib/lex.gs`：

- 逐字符扫描；数字精确转成有理数（整数部分 + 小数部分 / 10^k）。
- 标识符用 `norm_ident` 转小写；`is_alpha_char` 只接受字母，支持大小写。
- token 列表：`tk_type`、`tk_text`、`tk_pos`、`tk_num`、`tk_den`；类型枚举 `T.End/Num/Ident/Op/LP/RP/Comma`。

`lib/parse.gs`：

- shunting-yard，运算符栈 + 输出栈，全部显式。
- 优先级：`+ -` 2，`* /` 3，一元负号 4，`^` 5，函数标记 6。
- `^` 右结合；一元负号低于 `^`，所以 `-x^2 = -(x^2)`。
- 函数调用：标识符后跟 `(` 时压入函数标记；`)` 时先弹到 `(`，再把函数标记应用到唯一参数。
- 逗号参数、未知函数、缺少括号等设置 `err` 并停止；`^` 的指数是整数时走 `mk_pow`，否则走 `mk_pow_expr` 建 `PowE`。
- 解析过程中直接调用智能构造器，所以得到的已经是规范树。

## 5. 打印

`lib/print.gs` 用任务栈（节点任务/文本任务）做迭代打印：

- 优先级：Add 1，Mul 2，Pow/PowE 3，原子 4；父优先级更高时加括号。
- 加法先扁平化，判断每项符号；负项打印成 ` - ` 并取绝对值，所以输出 `x - 2*y` 而不是 `x + -2*y`。
- 乘法同样扁平化；负系数打印成 `-`；系数 1 省略。
- 负指数打印成分数：`x^-1 -> 1/x`，`x^-2 -> 1/x^2`，底数是复合表达式时加括号。
- 函数打印 `sin(...)`；常量打印 `pi`/`e`。
- 输出先写入 `pr_parts` 列表，最后 join 一次；超过 `MAX_OUTPUT` 截断。

## 6. 求导

`lib/diff.gs`：

- 后序显式栈；`df_done`/`df_val` 按节点 ID 缓存导数，避免共享子树重复计算。
- 规则：
  - 数字/常量 → 0；变量匹配求导变量 → 1，否则 0。
  - Add → 两边相加。
  - Mul → 乘积法则。
  - Pow(base,n) → `n * base^(n-1) * base'`。
  - PowE(base,exp)：
    - 指数是数字常量 `e`：`e * base^(e-1) * base'`（例如 `x^2.5 -> 5/2*x^(3/2)`）。
    - 指数含变量：`base^exp * (exp' * ln(base) + exp * base'/base)`（例如 `5^x -> ln(5)*5^x`、`x^x -> (ln(x)+1)*x^x`）。
  - 函数 → 链式法则：
    - `sin' = cos`，`cos' = -sin`，`tan' = 1/cos^2`
    - `exp' = exp`，`ln' = 1/u`
    - `log' = 1/(u*ln(10))`
    - `sqrt' = 1/(2*sqrt(u))`
    - `abs' = u/abs(u)`
    - `asin' = 1/sqrt(1-u^2)`，`acos'` 取负，`atan' = 1/(1+u^2)`
- 所有结果都经过 `mk_*`，所以会自动合并同类项和分数幂。

## 7. 展开

`lib/expand.gs`：

- 后序显式栈；`ex_done`/`ex_val` 缓存。
- `Add` → `mk_add`；`Func` → 保留函数、展开参数。
- `Mul` → 把两侧的 `Add` 项收集成列表，做双重循环分配，再用 `mk_add` 合并。
- `Pow(Add,n)`：
  - 如果 `Add` 恰好有两项，优先用二项式定理：`Σ C(n,k) a^(n-k) b^k`，系数用安全整数递推；系数溢出或项数超限时回退。
  - 否则重复 `expand_mul` n 次；项数超过 `MAX_TERMS` 报错。
- 非 `Add` 底数的幂直接 `mk_pow`。

## 8. 求值

`lib/eval.gs`：

- 后序栈 + `ev_done`/`ev_val`。
- 环境表 `env_name`/`env_val`；`eval ... at x=2, y=3` 逐个解析赋值并求值。
- 整数幂用循环；负指数取倒数；`0^0 = 1`，`0^-1` 报错。
- `PowE` 用 `pow_real_value`：整数指数复用循环；非整数指数且底数 >0 时用 `exp(e*ln(base))`；底数为 0 时按指数正负处理；负底数 + 非整数指数报“需要复数”。
- 三角函数按**弧度**：内部把参数乘 `180/pi` 再调用 Scratch 的 `sin/cos/tan`；反三角结果再除回。
- 定义域检查：`ln/log` 参数 >0，`sqrt` 参数 ≥0，`asin/acos` 在 [-1,1]。
- 输出 `fmt_dec`：整数直接输出，否则保留约 10 位小数并去尾零。

## 9. 符号代入

`lib/subst.gs`：

- 变量映射表 `sub_name` / `sub_node`；`subst_add` 对同名变量覆盖旧映射。
- 后序显式栈；`sb_done`/`sb_val` 按节点 ID 缓存结果。
- 对 `Var` 节点查映射，命中就替换成映射里的表达式节点；其余节点用 `mk_add`/`mk_mul`/`mk_pow`/`mk_func` 重建。
- 替换是**同时**发生的：`subst(x+y, x=y, y=x)` 得到 `x + y`，不会先换 `x` 再换 `y` 形成链式替换。
- 替换表达式本身不会被再次遍历，所以 `subst(x, x=(x+1))` 得到 `x + 1`，不会无限展开。
- `eval(expr, x=3, ...)` 的实现就是先 `subst`，再对结果做 `eval_expr`；`eval` 是同一行为的别名。

## 10. 命令与 UI

`lib/api.gs`：

- `run_command` 重置 arena/环境/错误，先尝试函数式语法：
  - 找到命令名后的第一个 `(`，用 `find_close` 做括号配对；
  - 如果配对括号在输入末尾，按 `split_args` 拆参数（只在最外层逗号处拆）；
  - 参数列表支持 `simplify(x+2*x)`、`diff(x^2, x)`、`subst(x^2, x=(a+1))`、`eval(x^2, x=3)`。
- 函数式命令：
  - `simplify(expr)`、`expand(expr)`
  - `diff(expr[, var])`，默认 `x`
  - `subst(expr, var=expr, ...)`
  - `eval(expr, var=value, ...)` / `eval(...)`
  - `help`
- 旧版冒号语法仍然保留：`simplify: ...`、`diff: ... wrt ...`、`eval: ... at ...`、`subst: ...`。
- 每个命令的结果写入全局字符串 `cas_result`；错误统一加 `错误：` 前缀。
- `MAX_INPUT` 在命令入口检查。

`main.gs`：

- 两个角色：`main` 是可见的角色，负责计算和 `say`；`asker` 是隐藏角色，只负责 `ask` 和广播 `compute`。
- 绿旗 → `main` 显示并显示 `history` 监视器 → 隐藏的 `asker` 立即弹出输入框 → 输入后广播 `compute` → `main` 计算、`say` 结果、把记录插入 `history` 顶部。
- 因为 ask 来自隐藏角色，Scratch 只弹输入框、不会用 ask 问题气泡覆盖 `main` 的 say 结果。
- `history` 显示在舞台上，最新结果在最上面；`results` 仍保存最近结果但默认隐藏。按 `c` 清空，按 `h` 让角色说出帮助。
- 所有计算仍由 `nowarp` 过程完成；UI 只负责输入/显示。

## 11. 模式规则引擎

`lib/rules.gs` 把“根节点局部”的恒等式从智能构造器里抽出来，做成结构规则表：

| ID | 模式 | 替换 |
|---|---|---|
| 1 | `Pow(Sqrt(u), n)`，n 偶数 | `u^(n/2)` |
| 2 | `Pow(Sqrt(u), n)`，n 奇数且 n>1 | `u^((n-1)/2) * Sqrt(u)` |
| 3 | `Sqrt(Pow(u, 2))` | `Abs(u)` |
| 4 | `Ln(Exp(u))` | `u` |
| 5 | `Exp(Ln(u))` | `u` |
| 6 | `Abs(Abs(u))` | `Abs(u)` |

规则执行：

1. `rules_apply(node)` 按优先级依次尝试规则，返回第一个成功匹配的替换节点；没有匹配返回 0。
2. `rules_pass(root)` 用显式后序栈自底向上重建整棵树：先用 `mk_add/mk_mul/mk_pow/mk_pow_expr/mk_func` 重建子节点，再在重建节点上调用 `rules_apply`。
3. `rules_simplify(root)` 重复 `rules_pass`，直到没有规则触发或达到 8 轮；`rs_changed` 只在新旧 `sig` 不同（或子节点变化）时置位。
4. 负奇次 `sqrt(u)^-1`、`sqrt(u)^-3` 不套规则，避免和倒数规则循环；负偶数次正常化成 `u^(n/2)`。
5. 规则在 `simplify`/`expand`/`diff`/`subst` 以及嵌套命令返回前运行，所以 `diff(sqrt(x)^4)`、`expand(sqrt(x)^4)`、`subst(sqrt(x)^4, x=y)` 都能得到化简结果。

`sqrt(x)^4` 不再需要特判：规则 1 把 4 折成 2，得到 `x^2`；`sqrt(x)^6 -> x^3`、`sqrt(x)^3 -> x*sqrt(x)` 同理。

`sin(u)^2 + cos(u)^2 -> 1` 是**多项模式**，需要在一个加法项列表里匹配两项，仍由 `mk_add` 的 Pythagorean 扫描完成；单节点规则引擎不处理它。

## 12. 嵌套命令调用

嵌套调用不能在解析器里直接递归求值，否则会破坏外层的 token/运算符栈。实现采用由内向外求值 + 占位符绑定：

1. 顶层 `run_command` 先确定外层命令及其参数。
2. 对每个参数调用 `expand_nested_text`：
   - `find_innermost_call` 扫描参数文本，找到第一个“参数里不再包含命令调用”的命令调用；
   - `nested_command_node` 直接求出该调用的 AST 节点（不打印）；
   - `bind_add` 把节点绑定到占位符 `__cN`；
   - 用 `__cN` 替换原调用文本，重复直到没有命令调用。
3. 外层命令重新解析参数文本。解析器遇到标识符时先查 `bind_lookup`：如果它是 `__cN`，直接把绑定节点压入输出栈，而不是创建变量。
4. 外层命令继续走正常流程（打印、求值等）。

这样：

- `simplify(subst(x^2, x=(a+1)))` 会把内层 `subst` 求成 `(a+1)^2` 的 AST，再让 `simplify` 打印。
- `eval(expand((x+1)^3), x=2)` 会把内层 `expand` 求成多项式 AST，再代入求值。
- 内层 `eval`/`approx` 返回 `K.Float` 节点，因此 `simplify(1+approx(sqrt(2)))` 输出 `2.4142135624`，而不是分数。
- 嵌套深度上限 64；`help` 不允许嵌套。
- 占位符名 `__cN` 是保留的；用户变量不要使用这个前缀。

## 13. 三角函数特殊值

`lib/trig.gs` 在 `rules_simplify` 后运行：

- 识别参数为 `r*pi` 的有理倍数，归一到 `[0,2)`；
- 对 `0, pi/6, pi/4, pi/3, pi/2` 等给出精确值；
- 处理负角、`x+pi`、`pi-x`、`x+2*pi` 等诱导；
- `tan(pi/2)` 报无定义；
- 反三角特殊值：`asin(1/2)=pi/6`、`acos(1/2)=pi/3`、`atan(1)=pi/4`。

## 14. 三角变形

`lib/trigtrans.gs` 提供结构重写：

- `texpand`：`sin/cos/tan` 的和角与 `2*x` 倍角；
- `tlinear`：`sin^2/cos^2` 降幂，`sin*sin/cos*cos/sin*cos` 积化和差；
- `tcollect`：`2*sin(u)*cos(u) -> sin(2u)`，以及 `A*sin(u)+B*cos(u)` 的辅助角合并；
- `sgn`：数值/无穷/符号处理；`exp(0)=1`、`exp(1)=e`；
- `sin2cos`：`sin(u) -> cos(pi/2-u)`；
- `cos2sin`：`cos(u) -> sin(pi/2+u)`；
- `halftan`：`u -> t=tan(u/2)` 的万能代换；
- `trigcos`/`trigsin`/`trigtan`：同角 `sin²/cos²/tan²` 之间改写。

它们都在 AST 上做后序重写，不依赖浮点。

## 15. 级数与极限

- `series(expr, x=a, n)`：对 `expr` 反复求导，在 `a` 处数值求值，除以阶乘，构造 `(x-a)^k` 项；支持 0..16 阶。
- `limit(expr, x, a)`：先直接代入；若为商且分母为 0，尝试洛必达；仍失败时用逐阶导数比较最低非零阶（级数回退）；全程使用 `exact_fold` 做精确有理/符号求值，不经过浮点过程。
- 无穷点 `oo`：识别 `(1+a/x)^x`，返回 `e^a`；其他无穷形式目前报错。

## 16. n 元 modular GCD

`lib/bipoly.gs` 提供二元 base，`lib/ngcd.gs` 扩展到 n 元：

- 输入先展开为二元稠密系数矩阵（每个节点最多两个变量）。
- 固定 `y=a`，在 `F_p[x]` 上做一元欧几里得 GCD；次数下降的采样点丢弃。
- 对每个 `x^k` 的系数按 `y` 插值，得到候选 `G(x,y) mod p`。
- 两个素数分别计算，CRT 还原整数系数；再做精确 Q 除法验证。
- 公共单项式因子单独恢复，避免 `gcd(x^2*y,x*y^2) -> x` 这类丢因子。
- 不使用 Kronecker 替换，因此不需要伪因子消除或随机平移。
- `lcm = p*q/g`，结果首一。
- 分式约分在 `do_simplify` 中调用；分子/分母同除 GCD。

n 元做法：额外 `n-2` 个变量在网格点上求值，每个点调用二元 modular GCD，再对每个 `x^i y^j` 系数做张量插值；网格点上限 256。CRT 使用两个约 1,000,000 的素数；只做整数系数 GCD。

## 14. 上限与错误

| 名称 | 值 | 行为 |
|---|---|---|
| `MAX_NODES` | 8192 | 超限报“表达式过大” |
| `MAX_TERMS` | 128 | 展开超限报“展开项过多” |
| `MAX_EXP` | 64 | 超限报“指数过大” |
| `MAX_INPUT` | 512 | 超限报“输入过长” |
| `MAX_OUTPUT` | 8192 | 截断并加 `...` |
| `MAX_SQRT` | 1,000,000 | 超过则不拆根式平方因子 |
| 嵌套深度 | 64 | 超限报“嵌套过深” |
| `MAX_SAFE` | 2^53-1 | 精确算术溢出报错 |

`err` 是第一个错误的字符串；`set_err` 不覆盖已有错误，避免丢失根因。

## 17. 测试

`tests/` 是独立 goboscript 工程：

- `tests/project/cases.txt` 是命令列表；`tests/build.sh` 生成 `data/cases.gs`（`list cases = [...]`），复制 `lib`，编译测试工程。
- `tests/run_vm.js` 用 `scratch-vm` 加载 `.sb3`、点绿旗、轮询 `tests` 角色的 `finished` 列表，读取 `results`，与 `tests/expected.txt` 逐行比较。
- `tests/ui_smoke.js` 监听 `QUESTION` 并发送 `ANSWER`，验证绿旗输入框、计算、角色 `say` 和 `history` 最新记录。
- 当前 421 条用例覆盖解析、优先级、有理数、同类项、幂、Pythagorean、展开、求导、一般幂（`5^x`/`x^x`/`x^2.5`）、根式化简（`sqrt(8)`/`sqrt(8/9)`）、规则化简（`sqrt(x)^4`/`ln(exp(x))`）、代入、求值、定义域、裸表达式、嵌套命令和错误路径；同时覆盖函数式命令与旧版冒号语法。

## 18. 优化

当前实现优先正确性和可读性。若继续提速，按收益排序：

1. **SoA**：把 `list Node` 拆成并行列表，去掉字段索引乘法。
2. **Hash-consing**：用 sig 做驻留表，共享重复子表达式，结构相等变 ID 相等。
3. **N-ary Add/Mul**：项链表代替二叉链，减少 flatten/rebuild。
4. **多项式后端**：`expand`/未来的 `solve` 用“指数 → 系数”数组，避免通用树重写。
5. **规则表**：把 Pythagorean 等恒等式抽成带元变量的规则匹配器；核心热路径仍保持硬编码。
