# 三能级精确反例否定纯化 Krylov 复杂度的普适下界

研究日期：2026-09-22  
状态：**PROVISIONAL CENTRAL CLOSURE（暂定中心闭合）**  
性质：本轮推导的精确否定性结果；已进行内部精确计算及异实现复核；未进行外部独立审核；未确认发表优先权。

## 1. 中心目标与边界

本轮选定 Das 与 Mori 的 *Krylov Complexity of Purification*，Phys. Rev. Lett. **136**, 030201 (2026)，arXiv:2408.00826v4 中式 (4) 的下界部分 [1,2]：

\[
\mathcal C_S\bigl(|\Psi^{U^*}_\rho(t)\rangle\bigr)
\stackrel{?}{\leq}\mathcal C_K(\rho(t)). \tag{T}
\]

固定的目标契约为：对任意有限维、满秩、迹为一的密度矩阵 \(\rho\)，任意时间无关 Hermitian Hamiltonian \(H\)，以及任意实时间 \(t\)，在论文规定的 Hilbert–Schmidt 归一化与时间依赖规范纯化下，证明或者精确否定 (T)。

该文的公开记录显示：PRL 发表日期为 2026-01-20，arXiv v4 更新日期为 2026-01-21。本轮核查的是这个版本，不是仅根据早期摘要重新命名目标。式 (T) 在来源中属于猜想；其定义和量词范围是本轮外部依赖，猜想的正确性不是证明前提。

结果否定的是这个普适下界。它不自动否定式 (4) 的上界，也不否定纯态算符复杂度与态复杂度的因子二关系，更不解决一般量子引力或所有复杂度猜想。

**前沿后果链：**

\[
\text{纯化复杂度能否普适地下界混合态算符复杂度}
\longrightarrow
\text{两种动力学诊断量之间的比较原则是否成立}
\longrightarrow
\text{使用纯化替代混合态算符传播诊断时所需的附加条件}.
\]

选题判断：该普适比较机制在混合态 Krylov 复杂度框架中具有中心性；这不是对整个理论物理领域影响力的认证。预期受众为相关专业群体，辨识度评为 MODERATE、8/15，选择档位为 Tier B，而非夸称 Tier A。

## 2. 约定与精确对象

取 \(\hbar=1\)，\(U_t=e^{-iHt}\)，\(\rho(t)=U_t\rho U_t^\dagger\)。算符内积为

\[
(A|B)=\operatorname{Tr}(A^\dagger B),\qquad
\mathcal L A=[H,A].
\]

混合态算符 Krylov 链的初始向量为

\[
A_K=\frac{\rho}{\sqrt{P}},\qquad P=\operatorname{Tr}\rho^2.
\]

时间依赖规范纯化为

\[
|\Psi^{U^*}_\rho(t)\rangle
=(U_t\otimes U_t^*)\operatorname{vec}(\sqrt\rho)
=\operatorname{vec}(U_t\sqrt\rho U_t^\dagger).
\]

因此其态 Krylov 链等价于：使用相同的交换子生成元，初始算符取 \(A_S=\sqrt\rho\)。它已经归一化，因为 \(\operatorname{Tr}[(\sqrt\rho)^2]=1\)。这正是两条链不能混用归一化的地方。论文附录的归一化步骤见 [1] 的 (S.7)–(S.11)。

两种复杂度均使用其自身 Krylov 基，并定义为

\[
C(t)=\sum_{n\geq0}n\,|\varphi_n(t)|^2.
\]

以下证明不依赖来源中的数值代码或任何未公开的证明。

## 3. 主反例

取

\[
H=\begin{pmatrix}2&0&0\\0&0&0\\0&0&1\end{pmatrix},\qquad
\rho=\frac1{42}
\begin{pmatrix}32&0&0\\0&5&3\\0&3&5\end{pmatrix}. \tag{1}
\]

其谱为

\[
\operatorname{spec}(\rho)=\left\{\frac{16}{21},\frac4{21},\frac1{21}\right\}.
\]

所以 \(\rho\) 严格正定且迹为一；\(H\) 有三个不同的有限实本征值。正平方根和纯度分别为

\[
\sqrt\rho=\frac1{2\sqrt{21}}
\begin{pmatrix}8&0&0\\0&3&1\\0&1&3\end{pmatrix},\qquad
P=\frac{13}{21}. \tag{2}
\]

直接平方即验证 (2)。这里既没有非物理状态，也没有无限维截断或者秩亏极限。

### 3.1 从三点谱精确求解 Krylov 链

对归一化 Hermitian 初始算符 \(A\)，设其全部非零相干性只有第 2、3 能级之间、且能隙为 1。其归一化谱测度是

\[
\nu_\mu=(1-\mu)\delta_0+\frac\mu2\delta_{1}+\frac\mu2\delta_{-1},
\qquad \mu=2|A_{23}|^2.
\]

因而返回振幅为 \(1-\mu+\mu\cos t\)。矩 \(m_2=m_4=\mu\) 给出

\[
b_1^2=\mu,\qquad b_2^2=1-\mu,\qquad b_3=0,\qquad a_n=0.
\]

也可直接从 \(A,[H,A],[H,[H,A]]\) 正交化，得到相同链；第三步精确终止，不是人为截断。链上的生成矩阵为

\[
J_\mu=
\begin{pmatrix}
0&\sqrt\mu&0\\
\sqrt\mu&0&\sqrt{1-\mu}\\
0&\sqrt{1-\mu}&0
\end{pmatrix}.
\]

由于 \(J_\mu^3=J_\mu\)，指数算符严格等于

\[
e^{-itJ_\mu}=I-i\sin t\,J_\mu+(\cos t-1)J_\mu^2.
\]

从第零节点出发的三个振幅为

\[
\varphi_0=1-\mu+\mu\cos t,\quad
\varphi_1=-i\sqrt\mu\sin t,\quad
\varphi_2=\sqrt{\mu(1-\mu)}(\cos t-1).
\]

直接相加三个模方得到 1；复杂度的精确表达式为

\[
F(\mu,t)=\mu\sin^2t+8\mu(1-\mu)\sin^4(t/2). \tag{3}
\]

### 3.2 两种初始向量对应不同的谱权重

由 (2)，

\[
\mu_K=\frac{2|\rho_{23}|^2}{P}=\frac3{182},\qquad
\mu_S=2|(\sqrt\rho)_{23}|^2=\frac1{42}.
\]

所以

\[
\mathcal C_K(t)=F\left(\frac3{182},t\right),\qquad
\mathcal C_S(t)=F\left(\frac1{42},t\right). \tag{4}
\]

在 \(t=\pi\) 时，演化算符是精确有理矩阵 \(U_\pi=\operatorname{diag}(1,1,-1)\)，且

\[
\boxed{\mathcal C_S(\pi)=\frac{82}{441}>\frac{1074}{8281}=\mathcal C_K(\pi)}.
\]

精确差值是

\[
\boxed{\mathcal C_S(\pi)-\mathcal C_K(\pi)=\frac{4192}{74529}>0}. \tag{5}
\]

相应的概率分布也全部是有理数：

| 链 | 第零节点 | 第一节点 | 第二节点 |
|---|---:|---:|---:|
| 混合态算符 | \(7744/8281\) | \(0\) | \(537/8281\) |
| 时间依赖纯化态 | \(400/441\) | \(0\) | \(41/441\) |

(5) 已经是对目标 (T) 的完整否定证书。

## 4. 同轮推进：不是孤立时间点，也不是偶然参数

### 4.1 三能级满秩反例族与任意常数修复的不可能性

固定同一 \(H\)，令实数 \(m\geq4\)，取

\[
\rho_m=\frac1{m^2+5}
\begin{pmatrix}
m^2&0&0\\0&5/2&3/2\\0&3/2&5/2
\end{pmatrix}.
\]

谱为 \((m^2,4,1)/(m^2+5)\)，每个有限 \(m\) 对应严格满秩态。它满足

\[
P_m=\frac{m^4+17}{(m^2+5)^2},\quad
\mu_S(m)=\frac1{2(m^2+5)},\quad
\mu_K(m)=\frac9{2(m^4+17)}.
\]

而

\[
\mu_S-\mu_K=
\frac{m^4-9m^2-28}{2(m^2+5)(m^4+17)}>0.
\]

证明最后的符号不需要数值：令 \(x=m^2\geq16\)，则 \(x^2-9x-28\) 在该区间严格递增，在 16 处为 84。

由恒等式

\[
F(a,t)-F(b,t)=(a-b)\bigl[\sin^2t+8(1-a-b)\sin^4(t/2)\bigr], \tag{6}
\]

以及这里 \(a+b<1\)，可知

\[
\mathcal C_S(t)>\mathcal C_K(t)
\quad\text{对所有 }t\notin2\pi\mathbb Z.
\]

在完整复现时间，两者同时为零，没有把 \(0/0\) 当作证书。固定 \(t=\pi\) 时，

\[
\frac{\mathcal C_S(\pi)}{\mathcal C_K(\pi)}\sim\frac{m^2}{9}
\longrightarrow\infty.
\]

因此即使把下界前的系数 1 改成任意固定正数 \(c\)，也不能在全部满秩三能级状态上保持 \(c\mathcal C_S\leq\mathcal C_K\)。这个陈述由每个有限参数的实际反例实现，不依赖把极限态当作许可输入。

### 4.2 固定维数和固定纯度也不能提供正的统一修正系数

进一步固定 \(d=4\)、\(P=1/2\)，取 \(0<\varepsilon<5/18\)。令

\[
s_\pm=\frac{1-\varepsilon\pm\sqrt{2\varepsilon-59\varepsilon^2/25}}2,
\]

并定义

\[
\rho_\varepsilon=
\operatorname{diag}(s_+,s_-)\oplus
\begin{pmatrix}\varepsilon/2&3\varepsilon/10\\3\varepsilon/10&\varepsilon/2\end{pmatrix},
\qquad H_4=\operatorname{diag}(2,3,0,1).
\]

它的本征值是 \(s_+,s_-,4\varepsilon/5,\varepsilon/5\)，总和为 1。平方和严格等于 \(1/2\)。正定性来自

\[
(1-\varepsilon)^2-\left(2\varepsilon-\frac{59}{25}\varepsilon^2\right)
=\left(1-\frac{14}{5}\varepsilon\right)
 \left(1-\frac65\varepsilon\right)>0.
\]

此时

\[
\mu_S=\frac\varepsilon{10},\qquad
\mu_K=\frac9{25}\varepsilon^2,
\]

故

\[
\frac{\mathcal C_K(\pi)}{\mathcal C_S(\pi)}
=\frac{18\varepsilon}{5}
\frac{1-9\varepsilon^2/25}{1-\varepsilon/10}
\longrightarrow0.
\]

**结论：即使维数固定为 4、纯度固定为 1/2，也不存在严格为正的统一系数 \(c\) 使 \(c\mathcal C_S\leq\mathcal C_K\) 对全部这些状态成立。** 因而仅依赖维数和纯度、并要求处处为正的全局修正不能恢复该下界。

一个全部有理的有限参数示例为 \(\varepsilon=1/10\)：

\[
\rho_4=\frac1{100}
\begin{pmatrix}66&0&0&0\\0&24&0&0\\0&0&5&3\\0&0&3&5\end{pmatrix},
\]

其纯度恰为 \(1/2\)，且

\[
\mathcal C_S(\pi)=\frac{99}{1250},\qquad
\mathcal C_K(\pi)=\frac{22419}{781250}.
\]

## 5. 机制、最小维数与一般谱障碍

### 5.1 短时曲率直接暴露机制

对任意满秩 \(\rho\)，直接展开两条 Krylov 链可得

\[
\mathcal C_K(t)=\frac{\|[H,\rho]\|_{\rm HS}^2}{P}t^2+O(t^4),
\qquad
\mathcal C_S(t)=\|[H,\sqrt\rho]\|_{\rm HS}^2t^2+O(t^4).
\]

在 \(\rho\) 的本征基中，系数之差为

\[
a_K-a_S=
\sum_{i,j}|H_{ij}|^2(\sqrt{\lambda_i}-\sqrt{\lambda_j})^2
\left[\frac{(\sqrt{\lambda_i}+\sqrt{\lambda_j})^2}{P}-1\right]. \tag{7}
\]

因此，对给定的 \(\rho\)，要求所有 \(H\) 的二阶曲率都满足下界，当且仅当

\[
P\leq(\sqrt{\lambda_i}+\sqrt{\lambda_j})^2
\quad\text{对所有 }\lambda_i\ne\lambda_j\text{ 的能级对成立}. \tag{8}
\]

相等本征值的能级对不给约束，因为其权重为零；完全混合态的情况是平凡静止情形。式 (8) 是曲率级别的充要条件，**不是**一般多频谱全时间下界的充分条件；本报告不作这种越界推断。

物理上，少量布居的动态子空间在 \(\sqrt\rho\) 的频谱权重中按布居的一次幂出现，在 \(\rho/\sqrt P\) 中按二次幂出现。高布居的静态部分因而可以把混合态算符复杂度稀释得更快。固定纯度构造进一步说明，这不是只靠整体纯度就能控制的效应。

### 5.2 独立重建二能级情形：三能级是最小反例维数

无需把文献中的二能级证明作为黑箱，直接利用 Cayley–Hamilton 恒等式。设二能级 \(\rho\) 的本征值为 \(\lambda_1,\lambda_2\)，则

\[
\rho=(\sqrt{\lambda_1}+\sqrt{\lambda_2})\sqrt\rho
-\sqrt{\lambda_1\lambda_2}\,I.
\]

在任意能量基中，非对角元满足相同的比例关系。因此，在有动力学的情形，

\[
\frac{\mu_K}{\mu_S}
=\frac{(\sqrt{\lambda_1}+\sqrt{\lambda_2})^2}{P}\geq1.
\]

任意正半定二阶矩阵 \(A=\left(\begin{smallmatrix}a&z\\z^*&b\end{smallmatrix}\right)\) 满足 \(a^2+b^2\geq2ab\geq2|z|^2\)，所以 \(2|z|^2/\|A\|_{\rm HS}^2\leq1/2\)。两条链的 \(\mu\) 都不超过 \(1/2\)。结合 (6)，得到全部二能级状态、全部时间的 \(\mathcal C_K\geq\mathcal C_S\)。无相干或退化 \(H\) 的情形两者均为零。

一维情况亦平凡。故 (1) 在本报告的定义范围内给出了最小 Hilbert 空间维数的反例。

## 6. 对反例的破坏性检查：解除精确分块

为排除反例只能在完全解耦的精细对称性上成立的疑问，保持 (1) 的 \(\rho\)，改用

\[
H_\delta=
\begin{pmatrix}2&\delta&2\delta\\\delta&0&3\delta\\2\delta&3\delta&1\end{pmatrix}.
\]

直接交换子计算给出

\[
a_S-a_K=\frac{2(1-468\delta^2)}{273}.
\]

因此 \(|\delta|<1/\sqrt{468}\) 时仍存在严格的小时间违例。取明确的 \(\delta=1/100\)，二阶差为

\[
a_S-a_K=\frac{2383}{341250}>0.
\]

这里还能给出不依赖浮点数的有限时间证书。每种复杂度都能写为

\[
C(t)=\langle v|e^{itG}Ne^{-itG}|v\rangle,
\]

其中 \(Nv=0\)，\(\|N\|\leq8\)。对这个 \(H_\delta\)，\(\|H_\delta\|\leq3\)，因而 \(\|G\|\leq6\)。三阶 Taylor 余项有界为

\[
|R_C(t)|\leq\frac{(2\|G\|)^3\|N\|}{6}|t|^3\leq2304|t|^3.
\]

对两个复杂度之差，余项不超过 \(4608|t|^3\)。故在 \(t=10^{-6}\) 处，

\[
\boxed{
\mathcal C_S(t)-\mathcal C_K(t)
\geq\frac{20263}{8531250000000000000}>0.
}
\]

因此，具有非零跨块耦合的具体 Hamiltonian 也有严格有限时间反例。原来 \(t=\pi\) 的大间隔证书仍是主证书；这里的小时间界只用于额外的对称性破坏审查。

## 7. 实际执行的验证

| 验证通道 | 实际执行内容 | 结果 |
|---|---|---|
| 精确密度矩阵计算 | 正平方根、谱、迹、纯度；3×3 交换子 Lanczos；正交性及精确终止 | 全部通过 |
| 独立谱表示 | 三点测度、矩、三节点生成矩阵、全时间表达式 | 精确一致 |
| 高精度直接向量演化 | 9×9 生成元，90 位精度，独立正交化及矩阵指数 | 与有理证书差小于 \(10^{-75}\) |
| 独立双精度实现 | 密度矩阵独立本征分解求平方根；原 Hilbert 空间直接酉演化 | 129 个时间点、258 个比较，最大误差 \(2.23\times10^{-16}\) 以下 |
| 坐标不变性 | 24 个随机整体酉基变换，两种复杂度分别比较 | 最大误差 \(8.61\times10^{-16}\) 以下 |
| 对称性破坏 | 非零 \(H_\delta\) 耦合的精确曲率与 Taylor 有界余项 | 严格有限时间反例成立 |
| 同轮结构推进 | 满秩三能级族；固定维数且固定纯度的四能级族；二能级重建 | 精确证明完成 |

主证书的数值读数是

\[
\mathcal C_K(\pi)=0.1296944813428329911846395362878879\ldots,
\]
\[
\mathcal C_S(\pi)=0.1859410430839002267573696145124717\ldots.
\]

这些小数只是复核。证明依靠前面的有理差值、有限维链的精确终止和解析恒等式。不同实现仍属于同一轮内部审查，不能写成外部研究者的独立复现。

## 8. 攻击树和停止理由

| ID | 路线 | 表示与硬检验 | 结果、障碍及后继 | 状态 |
|---|---|---|---|---|
| R1 | 从证明方向推导必要条件 | 交换子范数、\(\rho\) 的本征基 | 得到 (7)–(8)；普适证明被小本征值对阻断，产生 R2 | MUTATED |
| R2 | 静态大布居与动态小布居子空间的反例 | 满秩 3×3 矩阵、三点谱 | 得到精确有理违例 (5) | CLOSED |
| R3 | 不使用已猜出的复杂度公式重建 | 直接交换子正交化、9×9 向量化 | 独立重建同一反例；归一化和终止均通过 | CLOSED |
| R4 | 尝试推翻反例的物理许可性及对称性依赖 | 正定谱、非零跨块耦合、Taylor 余项 | 满秩、Hermiticity、标准纯化均满足；非分块版本亦有精确证书 | CLOSED |
| R5 | 把单例推进到中心机制 no-go | 参数谱、全时间符号分解 | 三能级比值无界，固定正系数不能修复 | CLOSED |
| R6 | 检验仅用整体纯度修复的可能性 | 固定 \(d=4,P=1/2\) 的谱约束 | 固定纯度下比值仍趋零 | CLOSED |
| R7 | 原下界的全域证明 | 保持原量词的证明任务 | 已被 R2 精确反例逻辑否定；不是算力耗尽 | DEAD |

主目标已由 R2 完整否定。没有剩余的必要中心证明步骤。没有宣称穷尽全部数学方法；穷尽失败协议不适用于已经闭合的反例目标。其他不同的上界、纯态或大规模随机系综问题不被静默加入目标，也不被冒充为已经解决。

## 9. 来源台账、新颖性与校准

### 9.1 外部来源台账

| 外部内容 | 来源与状态 | 是否承重 | 本轮处理 |
|---|---|---|---|
| 目标 (T)、时间依赖纯化、归一化约定 | [1] PRL 对应 arXiv v4；目标在原文中是猜想 | 是，仅作为问题定义 | 对照式 (2)、式 (4)、附录 (S.7)–(S.11) |
| 发表日期及版本 | [2] APS；[1] arXiv 摘要和提交历史 | 来源真实性 | 核对期刊记录和 v4 日期 |
| 纯态/张量积超可加性相关结果 | [3] 2026 预印本 | 否 | 用于区分目标与新颖性排查，未作为反例证明前提 |
| 选题阶段的 spin-alignment 强版本反例 | [4] 2026 预印本 | 否 | 排除把已否定的强版本当作新目标；未迁移其结论到熵版本 |
| 二能级下界 | [1] 已有专门计算 | 否 | 本轮用 Cayley–Hamilton 独立重建，消除依赖 |

### 9.2 新颖性边界

选题前和候选闭合后，检索了论文标题、arXiv 编号、DOI、counterexample、lower bound、qutrit、spectator、Wigner 等相关组合。返回结果中未定位到本报告的三能级反例或固定纯度 no-go 的直接先例。但部分组合出现大量同名词干的无关命中，检索召回率不能保证；没有进行覆盖全部引用文献的人工审核。因此：

**NOVELTY STATUS = PARTIALLY CLEARED；没有声称首次发现或确立优先权。**

数学正确性依赖可检查的证明，而不依赖检索没有命中。没有联系原作者、没有提交论文，也没有取得第三方审核意见。

### 9.3 三轴校准

科学价值：实际闭合的是一个完整普适下界的真假，并额外排除了正的常数修复和固定纯度修复。没有把局部特殊解当成全域证明。

AI 可控性：短时导数、有限矩阵、谱表示和精确运算形成了有效闭环。最有价值的信号不是更多随机样本，而是归一化前后的布居幂次差异。按本轮选题记录仍保留 Tier B，不因得到反例而事后抬高为 Tier A。

辨识度：MODERATE，8/15；预期为 SPECIALIST / PROGRAM-WIDE 边界上的关注，保守记录为 SPECIALIST。实际学界反应尚无数据，不能用预测代替已实现影响。

## 10. 复现

本目录包括：

- `verify.py`：精确与异实现验证脚本。
- `verification_results.json`：机器可读的全部证书和测试输出。
- `verification_log.txt`：实际执行记录。
- `contract.md`：固定的主目标及边界。
- `environment.json`：实际软件版本。
- `SHA256SUMS.txt`：交付文件摘要。

安装依赖 `numpy scipy sympy mpmath` 后，在本目录执行 `python verify.py`。脚本不访问网络、不需要作者的数值代码，不把数值精度当作证明本身。

## 参考来源

[1] R. N. Das and T. Mori, *Krylov Complexity of Purification*, arXiv:2408.00826v4. 原始目标见式 (4)，时间依赖纯化见式 (2)，Hilbert–Schmidt 归一化见补充材料 (S.7)–(S.11)。
https://arxiv.org/html/2408.00826v4  
版本记录：https://arxiv.org/abs/2408.00826

[2] R. N. Das and T. Mori, *Krylov Complexity of Purification*, Phys. Rev. Lett. **136**, 030201 (2026), published 20 January 2026, DOI: 10.1103/qgcx-wxpd.
https://journals.aps.org/prl/abstract/10.1103/qgcx-wxpd

[3] J. Murugan and H. J. R. van Zyl, *Superadditivity of Krylov Complexity for Tensor Products*, arXiv:2601.08723 (2026). 非承重来源，不把其已有结论作为本轮新结果。
https://arxiv.org/abs/2601.08723

[4] Z. Song and L. Chen, *A counterexample to the strong spin alignment conjecture*, arXiv:2603.25410 (2026). 仅用于选题真实性排查。
https://arxiv.org/abs/2603.25410

[5] 用户提供的 *One-Shot Theoretical Physics Research Selection P2-3*，尤其第 5.2 节（暂定中心闭合）、第 64–65 节（认识状态与新颖性）、第 67 节（状态字段）。这是工作协议，不是数学证明的外部前提。

## P2-3 完整状态块

```text
THEORETICAL-PHYSICS P2-3 STATUS:
PROVISIONAL CENTRAL CLOSURE

SELECTED BOTTLENECK:
时间依赖规范纯化的态 Krylov 复杂度是否普适地下界混合态算符 Krylov 复杂度。

CENTRAL TARGET CONTRACT:
对所有有限维满秩 rho、时间无关 Hermitian H 和实 t，
采用 normalized Hilbert-Schmidt operator Krylov complexity 及 U⊗U* 纯化，
证明或否定 CS(Psi_rho^{U*}(t)) <= CK(rho(t))。
已由满秩三能级精确反例否定。

FRONTIER CENTRALITY BEFORE RUN:
CENTRAL（混合态 Krylov 比较机制内的选题判断；非整个理论物理领域的影响认证）

FRONTIER CENTRALITY AFTER RUN:
CENTRAL（同一限定；实际闭合了普适下界）

RECOGNITION / HEADLINE RESONANCE BEFORE RUN:
MODERATE

RECOGNITION / HEADLINE RESONANCE AFTER RUN:
MODERATE（预测；没有实际学界反馈数据）

RESONANCE SCORE:
8/15 = canonicality 1/4 + headline 2/3 + audience 2/3 + surprise 2/3 + AI-story 1/2

ONE-LINE HYPOTHETICAL / ACTUAL HEADLINE:
三能级精确反例否定纯化 Krylov 复杂度的普适下界，且固定纯度也不能提供正的统一修正。

COUNTERFACTUAL HUMAN-SOLVER ATTENTION:
MODERATE

EXPECTED REACTION SCOPE:
SPECIALIST

AI-HYPE DEPENDENCE:
LOW

FRONTIER CONSEQUENCE MAP:
普适下界真假 -> 混合态与纯化传播诊断的比较原则 -> 附加谱约束或替代界的必要性

NATURAL PHYSICAL SCOPE:
全部有限维满秩混合态、时间无关酉动力学、论文规定的规范纯化与归一化。

DOWNSTREAM UNLOCKS:
排除该下界作为普适诊断原则；给出曲率级别的准确谱障碍；
排除正的常数修复及在 d=4,P=1/2 的正统一系数。

BOTTLENECK AUTHENTICITY:
ESTABLISHED（核对公开的 PRL/v4 猜想）；新颖性另行保留。

PREDICTED AI-FIT TIER:
B

REALIZED AI-FIT TIER:
B

CLOSED-LOOP CONTROLLABILITY:
STRONG

ONTOLOGY BURDEN:
LOW

GLOBAL-CONSISTENCY BURDEN:
LOW

PROVENANCE BURDEN:
LOW（主证明自包含；只有目标定义依赖来源）

PRIMARY ATTACK MODE:
MIXED（解析结构、反例、精确运算、独立数值重建）

DECISIVE CENTRAL-BOTTLENECK CERTIFICATE FOUND:
YES

RESULT TYPE:
EXACT ANALYTIC

FASTEST USEFUL ORACLE:
归一化交换子范数给出的短时 t^2 系数。

INDEPENDENT VERIFICATION CHANNELS USED:
精确 3×3 交换子链；三点谱矩与三节点解析指数；
9×9 向量化的 90 位运算；独立密度矩阵本征分解和酉演化；坐标不变性。
全部属于内部验证，不是外部研究者复现。

PHYSICAL CONSISTENCY CHECKS PASSED:
正定性、迹一、满秩、Hermiticity、酉性、规范纯化、HS 归一化、概率守恒、
维数闭合、无截断、复现端点、符号与基变换一致性。

COUNTEREXAMPLE / KILL ATTACKS ACTUALLY PERFORMED:
主反例；满秩审查；归一化审查；时刻与符号审查；
24 次酉基变换；非零跨块耦合；固定纯度对近纯态机制的反向检验。

MEANINGFUL REPRESENTATION SWITCHES:
交换子范数 -> rho 本征值对 -> 能量基单频块 -> 谱测度 -> Lanczos 链 -> 向量化。

EXACTIFICATION STATUS:
SUCCEEDED

BYPRODUCTS:
最小反例维数为三；满秩无界比值族；固定 d=4,P=1/2 的 no-go；
曲率级别的谱充要条件；非分块 Hamiltonian 的有限时间严格证书。

DID ANY LOCAL BYPRODUCT BECOME A SUBSTITUTE TERMINAL OBJECTIVE:
NO

SAME-RUN CENTRAL-BOTTLENECK BOOTSTRAPS ACTUALLY PERFORMED:
单例 -> 全时间参数族 -> 排除固定常数修复 -> 排除固定维数/纯度修复。

BRIDGE ATTEMPTS ACTUALLY PERFORMED:
短时信号 -> 单频谱 -> 精确链 -> 严格有理违例；
对称性破坏 -> 精确曲率 -> 有界 Taylor 余项。

BRIDGE RESULT:
TRACTION

SOURCE-PROVENANCE / DE-SOURCE ACTIONS:
核对 v4 目标、规范纯化与归一化；独立重建二能级结论；
不依赖作者数值代码或未公开随机矩阵结果；区分已知纯态超可加性。

OBSTRUCTION TYPES ENCOUNTERED:
F4（原普适证明路线与精确谱条件/反例不相容；不是物理许可性失败）

WALL TYPES ENCOUNTERED:
NONE

ATTACK ROUTES EXECUTED:
R1 必要条件；R2 精确反例；R3 独立重建；R4 破坏性检查；
R5 参数无界比值；R6 固定纯度 no-go；R7 原普适证明路线被精确反例终结。

DEAD ROUTES:
R7：原普适下界的全域证明已被物理许可的精确反例否定。

MUTATED ROUTES:
R1：证明必要条件转化为低布居能级对反例。

LIVE ROUTES REMAINING:
NONE（就已固定且已否定的中心目标而言；不是宣称所有相关研究问题均已解决）

STRONGER-PARENT ATTACKS:
任意正统一系数；固定维数且固定纯度的正统一系数。

WEAKER-SUFFICIENT-BRIDGE ATTACKS:
一个满足全部许可条件的有限维精确反例已足够否定原全称命题。

COMPUTE-WALL COMPRESSION ATTEMPTS:
没有实际算力墙；使用单频谱把完整有限维问题精确压缩成三节点链。

GLOBAL-WALL LOCALIZATION ATTEMPTS:
没有实际全局墙；将全称命题的反例搜索定位到满秩谱与一个动态能级对。

CROSS-ROUTE SYNTHESIS ATTEMPTS:
谱条件、精确矩阵、三点测度和 Taylor 余项互相验证并完成一般机制推进。

CLEAN-SLATE SECOND/LATER SHOTS:
不使用闭式复杂度的直接交换子重建与 9×9 演化；
固定纯度构造独立检验是否仅为整体纯度效应。

FRESH RECONSTRUCTION PERFORMED:
YES（定义 -> 初始向量 -> 独立 Krylov 构造 -> 相同证书）

METHOD-FAMILY SWEEP PERFORMED:
NO（不是穷尽失败；主目标已由完整精确反例闭合）

EXHAUSTION PROTOCOL:
NOT APPLICABLE

UNTRIED ACTIONABLE CENTRAL-BOTTLENECK STEP:
NONE（完成原命题的精确否定不再需要其他数学步骤）

IF A SPECIFIC STEP IS LISTED ABOVE, WHY WAS IT NOT EXECUTED:
NOT APPLICABLE

EXHAUSTION CERTIFICATE:
NOT APPLICABLE

POST-RUN FRONTIER-VALUE CALIBRATION:
实际结果是普适比较机制的否定与谱障碍；未宣称一般复杂度或量子引力闭合。

POST-RUN RESONANCE CALIBRATION:
保留 MODERATE；尚无外部反应，不能记录为已实现的影响。

POST-RUN AI-CAPABILITY CALIBRATION:
闭环强；结构化边界搜索与精确运算有效；不以数值样本代替证明。

SELECTION FAILURE:
NO（中心性限于明示的方法框架，预测为 Tier B）

NOVELTY STATUS:
PARTIALLY CLEARED（未确认首次发现或优先权）

INDEPENDENT EXTERNAL AUDIT:
NOT PERFORMED
```
