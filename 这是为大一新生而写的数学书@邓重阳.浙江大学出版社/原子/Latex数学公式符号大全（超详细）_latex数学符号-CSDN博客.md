[Latex数学公式符号大全（超详细）_latex数学符号-CSDN博客](https://blog.csdn.net/Yushan_Ji/article/details/134322574)
## 基本符号

### 小写希腊字母

**注：部分希腊字母在数学公式中常以变量形式出现，例如 ϵ \epsilon ϵ在数学中一般写法为 ε \varepsilon ε， ϕ \phi ϕ在数学中通常写作 φ \varphi φ**

| 符号  | 语法     | 符号  | 语法          | 符号  | 语法     |
| --- | ------ | --- | ----------- | --- | ------ |
| α   | \alpha | β   | \beta       | γ   | \gamma |
| θ   | \theta | ε   | \varepsilon | δ   | \delta |
| μ   | \mu    | ν   | \nu         | η   | \eta   |
| ζ   | \zeta  | λ   | \lambda     | ψ   | \psi   |
| σ   | \sigma | ξ   | \xi         | τ   | \tau   |
| ϕ   | \phi   | φ   | \varphi     | ρ   | \rho   |
| χ   | \chi   | ω   | \omega      | π   | \pi    |

### 大写希腊字母

大写希腊字母通常是小写希腊字母的LATEX语法第一个字母改为大写，见下表

| 符号  | 语法      | 符号  | 语法     | 符号  | 语法     |
| --- | ------- | --- | ------ | --- | ------ |
| Σ   | \Sigma  | Π   | \Pi    | Δ   | \Delta |
| Γ   | \Gamma  | Ψ   | \Psi   | Θ   | \Theta |
| Λ   | \Lambda | Ω   | \Omega | Φ   | \Phi   |
| Ξ   | \Xi     |     |        |     |        |

### 常用字体

默认的字体为 A B C d e f ABCdef ABCdef，也就是\mathnormal{ABCdef}（当然，打公式的时候不需要加上这个\mathnormal，直接打字母就是这个效果）

|字体|语法|字体|语法|
|---|---|---|---|
|A B C d e f \mathrm{ABCdef} ABCdef|\mathrm{ABCdef}|A B C d e f \mathbf{ABCdef} ABCdef|\mathbf{ABCdef}|
|A B C d e f \mathit{ABCdef} ABCdef|\mathit{ABCdef}|A B C d e f \pmb{ABCdef} ABCdef|\pmb{ABCdef}|
|A B C d e f \mathscr{ABCdef} ABCdef|\mathscr{ABCdef}|A B C d e f \mathcal{ABCdef} ABCdef|\mathcal{ABCdef}|
|A B C d e f \mathfrak{ABCdef} ABCdef|\mathfrak{ABCdef}|A B C d e f \mathbb{ABCdef} ABCdef|\mathbb{ABCdef}|

### 常见运算符

|运算符|语法|运算符|语法|运算符|语法|
|---|---|---|---|---|---|
|+ + +|+|− - −|-|× \times ×|\times|
|± \pm ±|\pm|⋅ \cdot ⋅|\cdot|∗ \ast ∗|\ast|
|∪ \cup ∪|\cup|∩ \cap ∩|\cap|∘ \circ ∘|\circ|
|∨ \lor ∨|\lor或\vee|∧ \land ∧|\land或\wedge|¬ \lnot ¬|\lnot|
|⊕ \oplus ⊕|\oplus|⊖ \ominus ⊖|\ominus|⊗ \otimes ⊗|\otimes|
|⊙ \odot ⊙|\odot|⊘ \oslash ⊘|\oslash|∙ \bullet ∙|\bullet|
|x \sqrt{x} x ​|\sqrt{x}|x n \sqrt[n]{x} nx ​|\sqrt[n]{x}|||

### 大尺寸运算符

|运算符|语法|运算符|语法|运算符|语法|
|---|---|---|---|---|---|
|∑ \sum ∑|\sum|∏ \prod ∏|\prod|∫ \int ∫|\int|
|⋃ \bigcup ⋃|\bigcup|⋂ \bigcap ⋂|\bigcap|∮ \oint ∮|\oint|
|⋁ \bigvee ⋁|\bigvee|⋀ \bigwedge ⋀|\bigwedge|∬ \iint ∬|\iint|
|∐ \coprod ∐|\coprod|⨆ \bigsqcup ⨆|\bigsqcup|∯ \oiint ∬ ​|\oiint|

### 常见关系符号

|符号|语法|符号|语法|符号|语法|
|---|---|---|---|---|---|
|< < <|<|> > >|>|= = =|=|
|≤ \leq ≤|\leq|≥ \geq ≥|\geq|≠ \neq =|\neq|
|≪ \ll ≪|\ll|≫ \gg ≫|\gg|≡ \equiv ≡|\equiv|
|⊂ \subset ⊂|\subset|⊃ \supset ⊃|\supset|≈ \approx ≈|\approx|
|⊆ \subseteq ⊆|\subseteq|⊇ \supseteq ⊇|\supseteq|∼ \sim ∼|\sim|
|∈ \in ∈|\in|∋ \ni ∋|\ni|∝ \propto ∝|\propto|
|⊢ \vdash ⊢|\vdash|⊣ \dashv ⊣|\dashv|⊨ \models ⊨|\models|
|∣ \mid ∣|\mid|∥ \parallel ∥|\parallel|⊥ \perp ⊥|\perp|
|∉ \notin ∈/|\notin|⋈ \Join ⋈|\Join|≁ \nsim ≁|\nsim|
|⊊ \subsetneq ⊊|\subsetneq|⊋ \supsetneq ⊋|\supsetneq|||

### 数学模式重音符

|符号|语法|符号|语法|符号|语法|
|---|---|---|---|---|---|
|a ^ \hat{a} a^|\hat{a}|a ˉ \bar{a} aˉ|\bar{a}|a ~ \tilde{a} a~|\tilde{a}|
|a ⃗ \vec{a} a|\vec{a}|a ˙ \dot{a} a˙|\dot{a}|a ¨ \ddot{a} a¨|\ddot{a}|
|a b c ^ \widehat{abc} abc|\widehat{abc}|a b c ~ \widetilde{abc} abc|\widetilde{abc}|a b c ‾ \overline{abc} abc|\overline{abc}|

### 箭头

如果需要长箭头，只需要在语法前面加上\long，例如\longleftarrow即为 ⟵ \longleftarrow ⟵，如果加上\Long则变为双线长箭头，例如\Longleftarrow即为 ⟸ \Longleftarrow ⟸

|符号|语法|符号|语法|符号|语法|
|---|---|---|---|---|---|
|← \leftarrow ←|\leftarrow|→ \rightarrow →|\rightarrow|↔ \leftrightarrow ↔|\leftrightarrow|
|⇐ \Leftarrow ⇐|\Leftarrow|⇒ \Rightarrow ⇒|\Rightarrow|⇔ \Leftrightarrow ⇔|\Leftrightarrow|
|↑ \uparrow ↑|\uparrow|↓ \downarrow ↓|\downarrow|↕ \updownarrow ↕|\updownarrow|
|⇑ \Uparrow ⇑|\Uparrow|⇓ \Downarrow ⇓|\Downarrow|⇕ \Updownarrow ⇕|\Updownarrow|
|↼ \leftharpoonup ↼|\leftharpoonup|↽ \leftharpoondown ↽|\leftharpoondown|⇀ \rightharpoonup ⇀|\rightharpoonup|
|⇁ \rightharpoondown ⇁|\rightharpoondown|⇌ \rightleftharpoons ⇌|\rightleftharpoons|⇋ \leftrightharpoons ⇋|\leftrightharpoons|
|⟺    \iff ⟺|\iff|↦ \mapsto ↦|\mapsto|||

### 括号

|括号|语法|括号|语法|括号|语法|
|---|---|---|---|---|---|
|( ) () ()|()|[ ] [] []|[]|{ } \{\} {}|\{\}|
|⌊ ⌋ \lfloor\rfloor ⌊⌋|\lfloor\rfloor|⌈ ⌉ \lceil\rceil ⌈⌉|\lceil\rceil|⟨ ⟩ \langle\rangle ⟨⟩|\langle\rangle|

### 大尺寸括号

|括号|语法|括号|语法|
|---|---|---|---|
|( ) \left(\right) ()|\left( \right)|[ ] \left[ \right] []|\left[ \right]|
|x 1 x 2 … x n ⏞ n \overbrace{x_1x_2\ldots x_n}^{n} x1​x2​…xn​ ​n​|\overbrace{x_1x_2\ldots x_n}^{n}|x 1 x 2 … x n ⏟ n \underbrace{x_1x_2\ldots x_n}_{n} n x1​x2​…xn​​​|\underbrace{x_1x_2\ldots x_n}_{n}|

**注：大尺寸的()和[]是可以根据公式的高度自动调节的，例如**

```
\arg\min_{\theta}
\left[
    -\sum_{i=1}^{n}
    \left[
        \mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) +
        (1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
    \right]
\right]
```

arg ⁡ min ⁡ θ [ − ∑ i = 1 n [ y ( i ) ln ⁡ ( h θ ( x ( i ) ) ) + ( 1 − y ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) ] ] \arg\min_{\theta} \left[ -\sum_{i=1}^{n} \left[ \mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) + (1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)})) \right] \right] argθmin​[−i=1∑n​[y(i)ln(hθ​(x(i)))+(1−y(i))ln(1−hθ​(x(i)))]]

可以看出，括号高度可以框住整个公式

因此在这种大型的公式中，使用大尺寸括号视觉效果更美观

### 其他常见符号

|符号|语法|符号|语法|符号|语法|
|---|---|---|---|---|---|
|∀ \forall ∀|\forall|∃ \exist ∃|\exist|∠ \angle ∠|\angle|
|∅ \emptyset ∅|\emptyset|∂ \partial ∂|\partial|∞ \infty ∞|\infty|
|… \ldots …|\ldots|⋯ \cdots ⋯|\cdots|… \dots …|\dots|
|⋮ \vdots ⋮|\vdots|⋱ \ddots ⋱|\ddots|′ \prime ′|\prime|
|∵ \because ∵|\because|∴ \therefore ∴|\therefore|□ \Box □|\Box|
|△ \triangle △|\triangle|§ \S §|\S|||

## 数学公式写法

### 上下标

- `^`：上标
- `_`：下标

例如:

- `\sum_{i=1}^{n}X_n`表示 ∑ i = 1 n X n \sum_{i=1}^{n}X_n ∑i=1n​Xn​
- `\int_{0}^{\infty}x^2dx`表示 ∫ 0 ∞ x 2 d x \int_{0}^{\infty}x^2dx ∫0∞​x2dx
- `\prod_{i=1}^{n}X_n`表示 ∏ i = 1 n X n \prod_{i=1}^{n}X_n ∏i=1n​Xn​

### 分数

使用`\frac{}{}`即可，例如`\frac{a}{b}`表示 a b \frac{a}{b} ba​

### 插入文字

使用`\text`，例如`\text{hello,world!}`表示 hello,world! \text{hello,world!} hello,world!

### 常见函数

|函数|语法|函数|语法|函数|语法|
|---|---|---|---|---|---|
|log ⁡ ( ) \log() log()|\log()|ln ⁡ ( ) \ln() ln()|\ln()|lg ⁡ ( ) \lg() lg()|\lg()|
|max ⁡ \max max|\max|min ⁡ \min min|\min|lim ⁡ x → ∞ \lim_{x \to \infty} limx→∞​|\lim_{x \to \infty}|
|arg ⁡ max ⁡ c ∈ C \arg\max_{c \in C} argmaxc∈C​|\arg\max_{c \in C}|arg ⁡ min ⁡ c ∈ C \arg\min_{c \in C} argminc∈C​|\arg\min_{c \in C}|exp ⁡ \exp exp|\exp|

### 矩阵、行列式

`&`表示分隔元素，`\\`表示换行

```
A=
\begin{pmatrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{pmatrix}
```

A = ( a 11 a 12 a 21 a 22 ) A=

(a11a12a21a22)

A=(a11​a21​​a12​a22​​)

```
A=
\begin{bmatrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{bmatrix}
```

A = [ a 11 a 12 a 21 a 22 ] A=

[a11a12a21a22]

A=[a11​a21​​a12​a22​​]

```
A=
\begin{Bmatrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{Bmatrix}
```

A = { a 11 a 12 a 21 a 22 } A=

{a11a12a21a22}

A={a11​a21​​a12​a22​​}

```
A=
\begin{vmatrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{vmatrix}
```

A = ∣ a 11 a 12 a 21 a 22 ∣ A=

|a11a12a21a22|

A= ​a11​a21​​a12​a22​​ ​

```
A=
\begin{Vmatrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{Vmatrix}
```

A = ∥ a 11 a 12 a 21 a 22 ∥ A=

‖a11a12a21a22‖

A= ​a11​a21​​a12​a22​​ ​

```
A=
\begin{matrix}
a_{11} & a_{12} \\
a_{21} & a_{22}
\end{matrix}
```

A = a 11 a 12 a 21 a 22 A=

a11a12a21a22

A=a11​a21​​a12​a22​​

### 多行公式对齐

使用`\begin{split} \end{split}`，在需要对齐的地方添加`&`符号，注意需要用`\\`来换行。

例如：

```
\begin{split}
L(\theta)
&=	\arg\max_{\theta}\ln(P_{All})\\
&=	\arg\max_{\theta}\ln\prod_{i=1}^{n}
    \left[
        (h_{\theta}(\mathbf{x}^{(i)}))^{\mathbf{y}^{(i)}}\cdot
        (1-h_{\theta}(\mathbf{x}^{(i)}))^{1-\mathbf{y}^{(i)}}
    \right]\\
&=	\arg\max_{\theta}\sum_{i=1}^{n}
	\left[
		\mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) +
		(1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
	\right]\\
&=	\arg\min_{\theta}
	\left[
        -\sum_{i=1}^{n}
        \left[
            \mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) +
            (1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
        \right]
	\right]\\
&=	\arg\min_{\theta}\mathscr{l}(\theta)
\end{split}
```

L ( θ ) = arg ⁡ max ⁡ θ ln ⁡ ( P A l l ) = arg ⁡ max ⁡ θ ln ⁡ ∏ i = 1 n [ ( h θ ( x ( i ) ) ) y ( i ) ⋅ ( 1 − h θ ( x ( i ) ) ) 1 − y ( i ) ] = arg ⁡ max ⁡ θ ∑ i = 1 n [ y ( i ) ln ⁡ ( h θ ( x ( i ) ) ) + ( 1 − y ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) ] = arg ⁡ min ⁡ θ [ − ∑ i = 1 n [ y ( i ) ln ⁡ ( h θ ( x ( i ) ) ) + ( 1 − y ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) ] ] = arg ⁡ min ⁡ θ l ( θ )

L(θ)=arg⁡maxθln⁡(PAll)=arg⁡maxθln⁡∏i=1n[(hθ(x(i)))y(i)⋅(1−hθ(x(i)))1−y(i)]=arg⁡maxθ∑i=1n[y(i)ln⁡(hθ(x(i)))+(1−y(i))ln⁡(1−hθ(x(i)))]=arg⁡minθ[−∑i=1n[y(i)ln⁡(hθ(x(i)))+(1−y(i))ln⁡(1−hθ(x(i)))]]=arg⁡minθl(θ)

L(θ)​=argθmax​ln(PAll​)=argθmax​lni=1∏n​[(hθ​(x(i)))y(i)⋅(1−hθ​(x(i)))1−y(i)]=argθmax​i=1∑n​[y(i)ln(hθ​(x(i)))+(1−y(i))ln(1−hθ​(x(i)))]=argθmin​[−i=1∑n​[y(i)ln(hθ​(x(i)))+(1−y(i))ln(1−hθ​(x(i)))]]=argθmin​l(θ)​

上例中，在`=`前添加了`&`，因此实现**等号对齐**；

`\begin{split} \end{split}`语法**默认为右对齐**，也就是说如果不在任何地方添加`&`符号，则公式默认右侧对齐，例如：

```
\begin{split}
L(\theta)
=	\arg\max_{\theta}\ln(P_{All})\\
=	\arg\max_{\theta}\ln\prod_{i=1}^{n}
    \left[
        (h_{\theta}(\mathbf{x}^{(i)}))^{\mathbf{y}^{(i)}}\cdot
        (1-h_{\theta}(\mathbf{x}^{(i)}))^{1-\mathbf{y}^{(i)}}
    \right]\\
=	\arg\max_{\theta}\sum_{i=1}^{n}
	\left[
		\mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) +
		(1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
	\right]\\
=	\arg\min_{\theta}
	\left[
        -\sum_{i=1}^{n}
        \left[
            \mathbf{y}^{(i)}\ln(h_{\theta}(\mathbf{x}^{(i)})) +
            (1-\mathbf{y}^{(i)})\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
        \right]
	\right]\\
=	\arg\min_{\theta}\mathscr{l}(\theta)
\end{split}
```

上述LATEX代码没有添加`&`符号，则公式[右对齐](https://so.csdn.net/so/search?q=%E5%8F%B3%E5%AF%B9%E9%BD%90&spm=1001.2101.3001.7020)：  
L ( θ ) = arg ⁡ max ⁡ θ ln ⁡ ( P A l l ) = arg ⁡ max ⁡ θ ln ⁡ ∏ i = 1 n [ ( h θ ( x ( i ) ) ) y ( i ) ⋅ ( 1 − h θ ( x ( i ) ) ) 1 − y ( i ) ] = arg ⁡ max ⁡ θ ∑ i = 1 n [ y ( i ) ln ⁡ ( h θ ( x ( i ) ) ) + ( 1 − y ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) ] = arg ⁡ min ⁡ θ [ − ∑ i = 1 n [ y ( i ) ln ⁡ ( h θ ( x ( i ) ) ) + ( 1 − y ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) ] ] = arg ⁡ min ⁡ θ l ( θ )

L(θ)=arg⁡maxθln⁡(PAll)=arg⁡maxθln⁡∏i=1n[(hθ(x(i)))y(i)⋅(1−hθ(x(i)))1−y(i)]=arg⁡maxθ∑i=1n[y(i)ln⁡(hθ(x(i)))+(1−y(i))ln⁡(1−hθ(x(i)))]=arg⁡minθ[−∑i=1n[y(i)ln⁡(hθ(x(i)))+(1−y(i))ln⁡(1−hθ(x(i)))]]=arg⁡minθl(θ)

L(θ)=argθmax​ln(PAll​)=argθmax​lni=1∏n​[(hθ​(x(i)))y(i)⋅(1−hθ​(x(i)))1−y(i)]=argθmax​i=1∑n​[y(i)ln(hθ​(x(i)))+(1−y(i))ln(1−hθ​(x(i)))]=argθmin​[−i=1∑n​[y(i)ln(hθ​(x(i)))+(1−y(i))ln(1−hθ​(x(i)))]]=argθmin​l(θ)​

如果希望**左对齐**，例如

```
\begin{split}
&\ln h_{\theta}(\mathbf{x}^{(i)})
=	\ln\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}}
= 	-\ln(1+e^{\theta^T \mathbf{x}^{(i)}})\\
&\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
=	\ln(1-\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}})
= 	-\theta^T \mathbf{x}^{(i)}-\ln(1+e^{\theta^T \mathbf{x}^{(i)}})
\end{split}
```

ln ⁡ h θ ( x ( i ) ) = ln ⁡ 1 1 + e − θ T x ( i ) = − ln ⁡ ( 1 + e θ T x ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) = ln ⁡ ( 1 − 1 1 + e − θ T x ( i ) ) = − θ T x ( i ) − ln ⁡ ( 1 + e θ T x ( i ) )

ln⁡hθ(x(i))=ln⁡11+e−θTx(i)=−ln⁡(1+eθTx(i))ln⁡(1−hθ(x(i)))=ln⁡(1−11+e−θTx(i))=−θTx(i)−ln⁡(1+eθTx(i))

​lnhθ​(x(i))=ln1+e−θTx(i)1​=−ln(1+eθTx(i))ln(1−hθ​(x(i)))=ln(1−1+e−θTx(i)1​)=−θTx(i)−ln(1+eθTx(i))​

除了`\begin{split} \end{split}`，也可以用`\begin{align} \end{align}`，用法与`split`相同，对齐方式也相同；

只有一点不同：**采用align环境会默认为每一条公式编号**（如下例），split则不会编号。

```
\begin{align}
&\ln h_{\theta}(\mathbf{x}^{(i)})
=	\ln\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}}
	= -\ln(1+e^{\theta^T \mathbf{x}^{(i)}})\\
&\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
=	\ln(1-\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}})
	= -\theta^T \mathbf{x}^{(i)}-\ln(1+e^{\theta^T \mathbf{x}^{(i)}})
\end{align}
```

ln ⁡ h θ ( x ( i ) ) = ln ⁡ 1 1 + e − θ T x ( i ) = − ln ⁡ ( 1 + e θ T x ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) = ln ⁡ ( 1 − 1 1 + e − θ T x ( i ) ) = − θ T x ( i ) − ln ⁡ ( 1 + e θ T x ( i ) )

ln⁡hθ(x(i))=ln⁡11+e−θTx(i)=−ln⁡(1+eθTx(i))ln⁡(1−hθ(x(i)))=ln⁡(1−11+e−θTx(i))=−θTx(i)−ln⁡(1+eθTx(i))

​lnhθ​(x(i))=ln1+e−θTx(i)1​=−ln(1+eθTx(i))ln(1−hθ​(x(i)))=ln(1−1+e−θTx(i)1​)=−θTx(i)−ln(1+eθTx(i))​​

但可以在align后加一个`*`号，则align环境也可以取消公式自动编号，如下：  
(也就是说`align*`和`split`的用法完全相同)

```
\begin{align*}
&\ln h_{\theta}(\mathbf{x}^{(i)})
=	\ln\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}}
	= -\ln(1+e^{\theta^T \mathbf{x}^{(i)}})\\
&\ln(1-h_{\theta}(\mathbf{x}^{(i)}))
=	\ln(1-\frac{1}{1+e^{-\theta^T \mathbf{x}^{(i)}}})
	= -\theta^T \mathbf{x}^{(i)}-\ln(1+e^{\theta^T \mathbf{x}^{(i)}})
\end{align*}
```

ln ⁡ h θ ( x ( i ) ) = ln ⁡ 1 1 + e − θ T x ( i ) = − ln ⁡ ( 1 + e θ T x ( i ) ) ln ⁡ ( 1 − h θ ( x ( i ) ) ) = ln ⁡ ( 1 − 1 1 + e − θ T x ( i ) ) = − θ T x ( i ) − ln ⁡ ( 1 + e θ T x ( i ) )

ln⁡hθ(x(i))=ln⁡11+e−θTx(i)=−ln⁡(1+eθTx(i))ln⁡(1−hθ(x(i)))=ln⁡(1−11+e−θTx(i))=−θTx(i)−ln⁡(1+eθTx(i))

​lnhθ​(x(i))=ln1+e−θTx(i)1​=−ln(1+eθTx(i))ln(1−hθ​(x(i)))=ln(1−1+e−θTx(i)1​)=−θTx(i)−ln(1+eθTx(i))​

### 方程组

使用`\begin{cases} \end{cases}`

例如：

```
\begin{cases}
    \begin{split}
        p &= P(y=1|\mathbf{x})=
        	\frac{1}{1+e^{-\theta^T\mathbf{X}}}\\
        1-p &= P(y=0|\mathbf{x})=1-P(y=1|\mathbf{x})=
        	\frac{1}{1+e^{\theta^T\mathbf{X}}}
    \end{split}
\end{cases}
```

{ p = P ( y = 1 ∣ x ) = 1 1 + e − θ T X 1 − p = P ( y = 0 ∣ x ) = 1 − P ( y = 1 ∣ x ) = 1 1 + e θ T X

{p=P(y=1|x)=11+e−θTX1−p=P(y=0|x)=1−P(y=1|x)=11+eθTX

⎩ ⎨ ⎧​p1−p​=P(y=1∣x)=1+e−θTX1​=P(y=0∣x)=1−P(y=1∣x)=1+eθTX1​​​

注意[LATEX语法](https://so.csdn.net/so/search?q=LATEX%E8%AF%AD%E6%B3%95&spm=1001.2101.3001.7020)可以嵌套使用，上例即为`\begin{cases} \end{cases}`下嵌套了`begin{split} \end{split}`。

也可以将公式和文字结合起来，例如：

```
\text{Decision Boundary}=
\begin{cases}
    1\quad \text{if }\ \hat{y}>0.5\\
    0\quad \text{otherwise}
\end{cases}
```

Decision Boundary = { 1 if y ^ > 0.5 0 otherwise \text{Decision Boundary}=

{1ify^>0.50otherwise

Decision Boundary={1ify^​>0.50otherwise​  
注：`\quad`表示空格。