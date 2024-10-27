-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

.. _matrices_bases_dimension:

TEXT. -/
/- OMIT:
Matrices, bases and dimension
-----------------------------

OMIT. -/
/- TEXT:
行列・基底・次元
-----------------------------

.. _matrices:

TEXT. -/
/- OMIT:
Matrices
^^^^^^^^

OMIT. -/
/- TEXT:
行列
^^^^^^^^

.. index:: matrices

TEXT. -/
/- OMIT:
Before introducing bases for abstract vector spaces, we go back to the much more elementary setup
of linear algebra in :math:`K^n` for some field :math:`K`.
Here the main objects are vectors and matrices.
For concrete vectors, one can use the ``![…]`` notation, where components are separated by commas.
For concrete matrices we can use the ``!![…]`` notation, lines are separated by semi-colons
and components of lines are separated by colons.
When entries have a computable type such as ``ℕ`` or ``ℚ``, we can use
the ``eval`` command to play with basic operations.

OMIT. -/
/- TEXT:
抽象的なベクトル空間の基底を導入する前に，ある体 :math:`K` に対する :math:`K^n` における線形代数の最も初歩的な設定に戻ります．ここでの主な対象はベクトルと行列です．具体的なベクトルには ``![…]`` という表記を使うことができ，成分はカンマで区切られます．具体的な行列には ``!![…]`` という表記を使うことができ，行はセミコロンで，行の成分はカンマで区切ります．要素が ``ℕ`` や ``ℚ`` のような計算可能な型を持っている場合， ``eval`` コマンドを使って基本的な演算を行うことができます．
EXAMPLES: -/
-- QUOTE:

section matrices

-- OMIT: Adding vectors
-- ベクトルの加法
#eval !![1, 2] + !![3, 4]  -- !![4, 6]

-- OMIT: Adding matrices
-- 行列の加法
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- OMIT: Multiplying matrices
-- 行列の乗法
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- QUOTE.
/- OMIT:
It is important to understand that this use of ``#eval`` is interesting only for
exploration, it is not meant to replace a computer algebra system such as Sage.
The data representation used here for matrices is *not* computationally
efficient in any way. It uses functions instead of arrays and is optimized for
proving, not computing.
The virtual machine used by ``#eval`` is also not optimized for this use.


OMIT. -/
/- TEXT:
この `#eval` の使用は確認のためだけのものであり，Sageのようなコンピュータ代数システムを置き換えるものではないことを理解することが重要です．ここで使用されている行列のデータ表現は計算効率に優れているわけではありません．配列の代わりに関数を使っており，計算ではなく証明に最適化されています． ``#eval`` が使用する仮想マシンもこの用途に最適化されていません．

TEXT. -/
/- OMIT:
Beware the matrix notation list rows but the vector notation
is neither a row vector nor a column vector. Multiplication of a matrix with a vector
from the left (resp. right) interprets the vector as a row (resp. column) vector.
This corresponds to operations
``Matrix.vecMul``, with notation ``ᵥ*`` and ``Matrix.mulVec``, with notation ` `*ᵥ``.
Those notations are scoped in the ``Matrix`` namespace that we therefore need to open.
OMIT. -/
/- TEXT:
行列表記は行のリストですが，ベクトル表記は行ベクトルでも列ベクトルでもない点に注意してください．行列に左（または右）からのベクトルを掛ける場合，そのベクトルを行（または列）ベクトルとして解釈します．これはそれぞれ ``ᵥ*`` という表記の ``Matrix.vecMul`` と ``*ᵥ`` という表記の ``Matrix.mulVec`` に対応します．これらの記法は ``Matrix`` 名前空間にスコープされているため，使う場合は開く必要があります．
EXAMPLES: -/
-- QUOTE:
open Matrix

-- OMIT: matrices acting on vectors on the left
-- 行列をベクトルに左から作用させる
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- OMIT: matrices acting on vectors on the left, resulting in a size one matrix
-- 行列をベクトルに左から作用させ，結果はサイズが1の行列になる
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- OMIT: matrices acting on vectors on the right
-- 行列をベクトルに右から作用させる
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]
-- QUOTE.
/- OMIT:
In order to generate matrices with identical rows or columns specified by a vector, we
use ``Matrix.row`` and ``Matrix.column``, with arguments the type indexing the
rows or columns and the vector.
For instance one can get single row or single column matrixes (more precisely matrices whose rows
or columns are indexed by ``Fin 1``).
OMIT. -/
/- TEXT:
ベクトルで指定された内容と同一の行または列を持つ行列を生成するには ``Matrix.row`` と ``Matrix.column`` を使用します．引数には行または列のインデックスを指定する型とベクトルを指定します．例えば，単一行または単一列の行列（より正確には行または列のインデックスが ``Fin 1`` である行列）を得ることができます．
EXAMPLES: -/
-- QUOTE:
#eval row (Fin 1) ![1, 2] -- !![1, 2]

#eval col (Fin 1) ![1, 2] -- !![1; 2]
-- QUOTE.
/- OMIT:
Other familiar operations include the vector dot product, matrix transpose, and,
for square matrices, determinant and trace.
OMIT. -/
/- TEXT:
その他には，ベクトルのドット積，行列の転置，正方行列の行列式やトレースなどのおなじみの演算があります．
EXAMPLES: -/
-- QUOTE:

-- OMIT: vector dot product
-- ベクトルのドット積
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- OMIT: matrix transpose
-- 行列の転置
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- OMIT: determinant
-- 行列式
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- OMIT: trace
-- トレース
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`


-- QUOTE.
/- OMIT:
When entries do not have a computable type, for instance if they are real numbers, we cannot
hope that ``#eval`` can help. Also this kind of evaluation cannot be used in proofs without
considerably expanding the trusted code base (i.e. the part of Lean that you need to trust when
checking proofs).

OMIT. -/
/- TEXT:
例えば実数など，要素が計算可能な型を持っていない場合， ``#eval`` の助けを期待することはできません．また，このような評価は信頼できるコードベース（つまり証明をチェックする際に信頼する必要があるLeanの部分）を大幅に拡張しない限り，証明に使用することはできません．

TEXT. -/
/- OMIT:
So it is good to also use the ``simp`` and ``norm_num`` tactics in proofs, or
their command counter-part for quick exploration.
OMIT. -/
/- TEXT:
そのため ``simp`` や ``norm_num`` を証明の中で使ったり，これと対のコマンドを簡単な確認のために使ったりするのも良いでしょう．
EXAMPLES: -/
-- QUOTE:

#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

-- QUOTE.
/- OMIT:
The next important operation on square matrices is inversion.
In the same way as division of numbers is always defined and returns the artificial value
zero for division by zero, the inversion operation is defined on all matrices and returns
the zero matrix for non-invertible matrices.

OMIT. -/
/- TEXT:
正方行列に対する次の重要な操作は逆行列です．Leanにおいて数値の除法が常に定義され，0による除算では人為的に0を返すのと同じように，逆行列を求める演算はすべての行列に対して定義され，非可逆行列では零行列を返します．

TEXT. -/
/- OMIT:
More precisely, there is general function ``Ring.inverse`` that does this in any ring,
and, for any matrix ``A``, ``A⁻¹`` is defined as ``Ring.inverse A.det • A.adjugate``.
According to Cramer’s rule, this is indeed the inverse of ``A`` when the determinant of ``A`` is
not zero.
OMIT. -/
/- TEXT:
より正確には，任意の環においてこれを行う一般的な関数 ``Ring.inverse`` があり，任意の行列 ``A`` に対して， ``A⁻¹`` は ``Ring.inverse A.det • A.adjugate`` として定義されます．Cramerのルールによれば，これは ``A`` の行列式が0でない場合に ``A`` の逆行列となります．
EXAMPLES: -/
-- QUOTE:

#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

-- QUOTE.
/- OMIT:
Of course this definition is really useful only for invertible matrices.
There is a general type class ``Invertible`` that helps recording this.
For instance, the ``simp`` call in the next example will use the ``inv_mul_of_invertible``
lemma which has an ``Invertible`` type-class assumption, so it will trigger
only if this can be found by the type-class synthesis system.
Here we make this fact available using a ``have`` statement.
OMIT. -/
/- TEXT:
もちろん，この定義は可逆な行列に対してのみ有効です．これを記すための一般的な型クラス ``Invertible`` があります．例えば，次の例の ``simp`` の呼び出しは補題 ``inv_mul_of_invertible`` を使用しますが，この補題は ``Invertible`` という型クラスの仮定を有します．ここでは ``have`` 文を使ってこの事実を利用できるようにしています．
EXAMPLES: -/
-- QUOTE:

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

-- QUOTE.
/- OMIT:
In this fully concrete case, we could also use the ``norm_num`` machinery,
and ``apply?`` to find the final line:
OMIT. -/
/- TEXT:
これの完全に具体的なケースでは， ``norm_num`` という機構と，最後の行を探すために ``apply?`` を使うこともできます：
EXAMPLES: -/
-- QUOTE:
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

-- QUOTE.
/- OMIT:
All the concrete matrices above have their rows and columns indexed by ``Fin n`` for
some ``n`` (not necessarily the same for rows and columns).
But sometimes it is more convenient to index matrices using arbitrary finite types.
For instance the adjacency matrix of a finite graph has rows and columns naturally indexed by
the vertices of the graph.

OMIT. -/
/- TEXT:
上記のすべての具体的な行列は，ある ``n`` に対して行と列のインデックスが ``Fin n`` でした（行と列が同じとは限りません）．しかし，任意の有限型を使って行列にインデックスを付けた方が便利な場合もあります．例えば，有限グラフの隣接行列は，行と列がグラフの頂点によって自然に添字付けられます．

TEXT. -/
/- OMIT:
In fact when simply wants to define matrices without defining any operation on them,
finiteness of the indexing types are not even needed, and coefficients can have any type,
without any algebraic structure.
So Mathlib simply defines ``Matrix m n α`` to be ``m → n → α`` for any types ``m``, ``n`` and ``α``,
and the matrices we have been using so far had types such as ``Matrix (Fin 2) (Fin 2) ℝ``.
Of course algebraic operations require more assumptions on ``m``, ``n`` and ``α``.

OMIT. -/
/- TEXT:
実は，行列に対する演算を定義せずに行列を定義したい場合，インデックスの型の有限性は必要なく，係数は代数的な構造なしに任意の型を持つことができます．そのため，Mathlibは ``Matrix m n α`` を ``m`` ， ``n`` ， ``α`` の型に対してただ ``m → n → α`` とだけ定義しており，これまで使ってきた行列は ``Matrix (Fin 2) (Fin 2) ℝ`` のような型を持っていました．もちろん，代数演算には ``m`` ， ``n`` ， ``α`` により仮定を置く必要があります．

TEXT. -/
/- OMIT:
Note the main reason why we do not use ``m → n → α`` directly is to allow the type class
system to understand what we want. For instance, for a ring ``R``, the type ``n → R`` is
endowed with the point-wise multiplication operation, and similarly ``m → n → R``
has this operation which is *not* the multiplication we want on matrices.

OMIT. -/
/- TEXT:
``m → n → α`` を直接使用しない主な理由は，型クラスシステムが利用者が必要なものを理解できるようにするためです．例えば，環 ``R`` の場合，型 ``n → R`` は点ごと単位の乗算演算を持つのと同様に， ``m → n → R`` も同じ演算を持っており，これは行列に対して欲しい乗算 **ではありません** ．

TEXT. -/
/- OMIT:
In the first example below, we force Lean to see through the definition of ``Matrix``
and accept the statement as meaningful, and then prove it by checking all entries.

OMIT. -/
/- TEXT:
以下の最初の例では，Leanに ``Matrix`` の定義を見破らせ，この文を意味のあるものとして受け入れさせ，すべての要素をチェックすることで証明しています．

TEXT. -/
/- OMIT:
But then the next two examples reveal that Lean uses the point-wise multiplication
on ``Fin 2 → Fin 2 → ℤ`` but the matrix multiplication on ``Matrix (Fin 2) (Fin 2) ℤ``.
OMIT. -/
/- TEXT:
しかし，その次の2つの例からは，Leanは ``Fin 2 → Fin 2 → ℤ`` の点ごとの乗算ではなく ``Matrix (Fin 2) (Fin 2) ℤ`` の行列演算を使っていることがわかります．
EXAMPLES: -/
-- QUOTE:
section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num
-- QUOTE.
/- OMIT:
In order to define matrices as functions without loosing the benefits of ``Matrix``
for type class synthesis, we can use the equivalence ``Matrix.of`` between functions
and matrices. This equivalence is secretly defined using ``Equiv.refl``.

OMIT. -/
/- TEXT:
型クラス合成のための ``Matrix`` の利点を失うことなく，行列を関数として定義するために，関数と行列の間の等価性 ``Matrix.of`` を使用することができます．この等価性は ``Equiv.refl`` によって密かに定義されています．

TEXT. -/
/- OMIT:
For instance we can define Vandermonde matrices corresponding to a vector ``v``.
OMIT. -/
/- TEXT:
例えば，ベクトル ``v`` に対応するVandermonde行列を定義することができます．
EXAMPLES: -/
-- QUOTE:

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl
end
end matrices
-- QUOTE.
/- OMIT:
Bases
^^^^^

OMIT. -/
/- TEXT:
基底
^^^^^

TEXT. -/
/- OMIT:
We now want to discuss bases of vector spaces. Informally there are many ways to define this notion.
One can use a universal property.
One can say a basis is a family of vectors that is linearly independent and spanning.
Or one can combine those properties and directly say that a basis is a family of vectors
such that every vectors can be written uniquely as a linear combination of bases vectors.
Yet another way to say it is that a basis provides a linear isomorphism with a power of
the base field ``K``, seen as a vector space over ``K``.

OMIT. -/
/- TEXT:
ここでベクトル空間の基底について議論したいと思います．非形式的にこの概念を定義する方法はたくさんあります．一方で普遍性を使うこともできます．また線形独立で空間を張るベクトルの族であるということもできます．あるいはこれらの性質を組み合わせて，基底とはすべてのベクトルが基底ベクトルの線形結合として一意に書けるようなベクトルの族であると直接言うこともできます．さらに別の言い方をすると，基底は ``K`` 上のベクトル空間として見たときに，基底の体 ``K`` のべき乗と線形同型を提供します．

TEXT. -/
/- OMIT:
This isomorphism version is actually the one that Mathlib uses as a definition under the hood, and
other characterizations are proven from it.
One must be slightly careful with the “power of ``K``” idea in the case of infinite bases.
Indeed only finite linear combinations make sense in this algebraic context. So what we need
as a reference vector space is not a direct product of copies of ``K`` but a direct sum.
We could use ``⨁ i : ι, K`` for some type ``ι`` indexing the basis
But we rather use the more specialized spelling ``ι →₀ K`` which means
“functions from ``ι`` to ``K`` with finite support”, i.e. functions which vanish outside a finite set
in ``ι`` (this finite set is not fixed, it depends on the function).
Evaluating such a function coming from a basis ``B`` at a vector ``v`` and
``i : ι`` returns the component (or coordinate) of ``v`` on the ``i``-th basis vector.

OMIT. -/
/- TEXT:
この同型バージョンがMathlibにて実際に定義として採用されているもので，他の特徴づけはここから証明されます．無限基底の場合，「 ``K`` のべき乗」という考え方に少し注意が必要です．実際，この代数的な文脈で意味を持つのは有限の線形結合の場合だけです．したがって，参照するベクトル空間として必要なのは ``K`` のコピーの直積ではなく直和です．これのために基底の添字としてある型 ``ι`` によって ``⨁ i : ι, K`` を使うことも可能ですが，こちらではなくより特殊化した ``ι →₀ K`` という書き方を使います．これは「有限台を持つ ``ι`` から ``K`` への関数」，つまり ``ι`` の有限集合（この有限集合は固定ではなく，関数に依存します）の外側で消える関数を意味します．このような関数を規定 ``B`` からベクトル ``v`` と ``i : ι`` で評価すると， ``i`` 番目の基底ベクトル ``v`` の成分（または座標）が返されます．

TEXT. -/
/- OMIT:
The type of bases indexed by a type ``ι`` of ``V`` as a ``K`` vector space is ``Basis ι K V``.
The isomorphism is called ``Basis.repr``.
OMIT. -/
/- TEXT:
``K`` ベクトル空間としての ``V`` の型 ``ι`` を添字とする基底の型は ``Basis ι K V`` です．この同型を ``Basis.repr`` と呼びます．
EXAMPLES: -/
-- QUOTE:
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- OMIT: The basis vector with index ``i``
-- ``i`` 番目の基底ベクトル
#check (B i : V)

-- OMIT: the linear isomorphism with the model space given by ``B``
-- ``B`` から与えられるモデル空間の線形同型
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- OMIT: the component function of ``v``
-- ``v`` の成分の関数
#check (B.repr v : ι →₀ K)

-- OMIT: the component of ``v`` with index ``i``
-- ``i`` 番目の ``v`` の成分
#check (B.repr v i : K)

-- QUOTE.
/- OMIT:
Instead of starting with such an isomorphism, one can start with a family ``b`` of vectors that is
linearly independent and spanning, this is ``Basis.mk``.

OMIT. -/
/- TEXT:
このような同型から始める代わりに，線形独立で空間を張るベクトルの族 ``b`` から始めることができ，これは ``Basis.mk`` と名付けられています．

TEXT. -/
/- OMIT:
The assumption that the family is spanning is spelled out as ``⊤ ≤ Submodule.span K (Set.range b)``.
Here ``⊤`` is the top submodule of ``V``, i.e. ``V`` seen as submodule of itself.
This spelling looks a bit tortuous, but we will see below that it is almost equivalent by definition
to the more readable ``∀ v, v ∈ Submodule.span K (Set.range b)`` (the underscores in the snippet
below refers to the useless information ``v ∈ ⊤``).
OMIT. -/
/- TEXT:
この族が空間を張るという仮定は ``⊤ ≤ Submodule.span K (Set.range b)`` として記述されます．ここで ``⊤`` は ``V`` の最上位の部分加群，つまり ``V`` をそれ自身の部分加群として見たものです．この書き方は少し面倒に見えるでしょうが，以下で見るようにこれはより読みやすい ``∀ v, v ∈ Submodule.span K (Set.range b)`` と定義上ほぼ等しいです（以下のコード片中のアンダースコアは有益ではない情報 ``v ∈ ⊤`` を意味しています）．
EXAMPLES: -/
-- QUOTE:
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- OMIT: The family of vectors underlying the above basis is indeed ``b``.
-- 上記の基底の台となるベクトルの族が実際に ``b`` であること．
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

-- QUOTE.
/- OMIT:
In particular the model vector space ``ι →₀ K`` has a so-called canonical basis whose ``repr``
function evaluated on any vector is the identity isomorphism. It is called
``Finsupp.basisSingleOne`` where ``Finsupp`` means function with finite support and
``basisSingleOne`` refers to the fact that basis vectors are functions which
vanish expect for a single input value. More precisely the basis vector indexed by ``i : ι``
is ``Finsupp.single i 1`` which is the finitely supported function taking value ``1`` at ``i``
and ``0`` everywhere else.

OMIT. -/
/- TEXT:
特に，モデルベクトル空間 ``ι →₀ K`` はいわゆる正準基底を持っており，任意のベクトル上で評価される ``repr`` 関数は恒等同型です．これは ``Finsupp.basisSingleOne`` と呼ばれ，ここで ``Finsupp`` は有限台の関数を意味し， ``basisSingleOne`` は基底ベクトルが1つの入力値に対して消える関数であることを意味します．より正確には， ``i : ι`` で添字付けられる基底ベクトルは ``Finsupp.single i 1`` であり，これは ``i`` で値 ``1`` を取り，それ以外の場所では ``0`` を取る有限台の関数です．
EXAMPLES: -/
-- QUOTE:
variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- QUOTE.
/- OMIT:
The story of finitely supported functions is unneeded when the indexing type is finite.
In this case we can use the simpler ``Pi.basisFun`` which gives a basis of the whole
``ι → K``.
OMIT. -/
/- TEXT:
添字の型が有限の場合，有限台の関数の話は不要です．この場合，より単純な ``Pi.basisFun`` を使うことができ，これは ``ι → K`` 全体の基底を与えます．
EXAMPLES: -/
-- QUOTE:

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- QUOTE.
/- OMIT:
Going back to the general case of bases of abstract vector spaces, we can express
any vector as a linear combination of basis vectors.
Let us first see the easy case of finite bases.
OMIT. -/
/- TEXT:
抽象ベクトル空間の基底の一般的なケースに戻ると，任意のベクトルを基底ベクトルの線形結合として表現することができます．まずは有限基底の簡単な場合を見てみましょう．
EXAMPLES: -/
-- QUOTE:

example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v


-- QUOTE.

/- OMIT:
When ``ι`` is not finite, the above statement makes no sense a priori: we cannot take a sum over ``ι``.
However the support of the function being summed is finite (it is the support of ``B.repr v``).
But we need to apply a construction that takes this into account.
Here Mathlib uses a special purpose function that requires some time to get used to:
``Finsupp.linearCombination`` (which is built on top of the more general ``Finsupp.sum``).
Given a finitely supported function ``c`` from a type ``ι`` to the base field ``K`` and any
function ``f`` from ``ι`` to ``V``, ``Finsupp.linearCombination K f c`` is the
sum over the support of ``c`` of the scalar multiplication ``c • f``. In
particular, we can replace it by a sum over any finite set containing the
support of ``c``.

OMIT. -/
/- TEXT:
``ι`` が有限でない場合，上の文は先験的に意味を為しません：すなわち ``ι`` 上で和を取れません．しかし，和の対象となる関数の台は有限です（ ``B.repr v`` の台です）．ただし，そのためにはこれを考慮した構成を適用する必要があります．ここでMathlibは取っつき辛い特殊な関数を使います： ``Finsupp.linearCombination`` （これはより一般的な ``Finsupp.sum`` の上に構築されています）．ある型 ``ι`` から基底の体 ``K`` への有限台の関数 ``c`` と ``ι`` から ``V`` への任意の関数 ``f`` が与えられた時， ``Finsupp.linearCombination K f c`` はスカラー倍 ``c • f`` の ``c`` の台の上の和です．特に， ``c`` の台を含む任意の有限集合上の和で置き換えることができます．
EXAMPLES: -/
-- QUOTE:

example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h
-- QUOTE.
/- OMIT:
One could also assume that ``f`` is finitely supported and still get a well defined sum.
But the choice made by ``Finsupp.linearCombination`` is the one relevant to our basis discussion since it allows
to state the generalization of ``Basis.sum_repr``.
OMIT. -/
/- TEXT:
また， ``f`` が有限台であると仮定しても，well-definedな和を得ることができます．しかし， ``Finsupp.linearCombination`` による選択は， ``Basis.sum_repr`` の一般化を記述することができるため，基底の議論に関連します．
EXAMPLES: -/
-- QUOTE:

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
-- QUOTE.
/- OMIT:
One could wonder why ``K`` is an explicit argument here, despite the fact it can be inferred from
the type of ``c``. The point is that the partially applied ``Finsupp.linearCombination K f``
is interesting in itself. It is not a bare function from ``ι →₀ K`` to ``V`` but a
``K``-linear map.
OMIT. -/
/- TEXT:
``K`` は ``c`` の型から推測できるにもかかわらず，なぜここで明示的な引数になっているのか不思議に思われるかもしれません．ポイントは，部分適用される ``Finsupp.linearCombination K f`` 自体が興味深い対象であるということです．これは ``ι →₀ K`` から ``V`` へのただの関数ではなく， ``K`` の線形写像です．
EXAMPLES: -/
-- QUOTE:
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)
-- QUOTE.
/- OMIT:
The above subtlety also explains why dot notation cannot be used to write
``c.linearCombination K f`` instead of ``Finsupp.linearCombination K f c``.
Indeed ``Finsupp.linearCombination`` does not take ``c`` as an argument,
``Finsupp.linearCombination K f`` is coerced to a function type and then this function
takes ``c`` as an argument.

OMIT. -/
/- TEXT:
上記の微妙な点は， ``Finsupp.linearCombination K f c`` の代わりにドット記法で ``c.linearCombination K f`` と書けないことの理由にもなります．実際， ``Finsupp.linearCombination`` は ``c`` を引数に取らず， ``Finsupp.linearCombination K f`` は関数型に強制され，この関数は ``c`` を引数に取ります．

TEXT. -/
/- OMIT:
Returning to the mathematical discussion, it is important to understand that the
representation of vectors in a basis is less useful in formalized
mathematics than you may think.
Indeed it is very often more efficient to directly use more abstract properties of bases.
In particular the universal property of bases connecting them to other free objects in algebra
allows to construct linear maps by specifying the images of basis vectors.
This is ``Basis.constr``. For any ``K``-vector space ``W``, our basis ``B``
gives a linear isomorphism ``Basis.constr B K`` from ``ι → W`` to ``V →ₗ[K] W``.
This isomorphism is characterized by the fact that it sends any function ``u : ι → W``
to a linear map sending the basis vector ``B i`` to ``u i``, for every ``i : ι``.
OMIT. -/
/- TEXT:
数学的な議論に戻ると，ベクトルを基底で表現することは形式化された数学では思ったより役に立たないということを理解することが重要です．実際，基底のより抽象的な性質を直接利用する方が効率的な場合が多いです．特に，代数学における他の自由な対象に接続する基底の普遍性は，基底ベクトルの像を指定することによって線形写像を構成することを可能にします．これが ``Basis.constr`` です．任意の ``K`` ベクトル空間 ``W`` に対して，基底 ``B`` は ``ι → W`` から ``V →ₗ[K] W`` への線形同型 ``Basis.constr B K`` を与えます．この同型は，任意の関数 ``u : ι → W`` を，あらゆる ``i : ι`` に対して，基底ベクトル ``B i`` を ``u i`` に送る線形写像へと送られるという事実によって特徴づけられます．
EXAMPLES: -/
-- QUOTE:
section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

-- QUOTE.
/- OMIT:
This property is indeed characteristic because linear maps are determined by their values
on bases:
OMIT. -/
/- TEXT:
線形写像は基底の上の値によって決定されるため，この性質は実に特徴的です：
EXAMPLES: -/
-- QUOTE:
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h


-- QUOTE.
/- OMIT:
If we also have a basis ``B'`` on the target space then we can identify linear maps
with matrices. This identification is a ``K``-linear isomorphism.
OMIT. -/
/- TEXT:
もし対象の空間にも基底 ``B`` があれば，線形写像と行列を同定することができます．この同定は ``K`` 線形同型です．
EXAMPLES: -/
-- QUOTE:


variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end

-- QUOTE.
/- OMIT:
As an exercise on this topic, we will prove part of the theorem which guarantees that
endomorphisms have a well-defined determinant.
Namely we want to prove that when two bases are indexed by the same type, the matrices
they attach to any endomorphism have the same determinant.
This would then need to be complemented using that bases all have isomorphic indexing types to
get the full result.

OMIT. -/
/- TEXT:
この話題の演習として，自己準同型がwell-definedな行列式を持つことを保証する定理の一部を証明します．すなわち，2つの基底が同じ型によって添字付けられる時，それらのどのような自己準同型に対応する行列も同じ行列式を持つことを証明しましょう．これは完全な結果を得るためには，すべての基底が同型の添字型を持つことを利用して補完する必要があります．

TEXT. -/
/- OMIT:
Of course Mathlib already knows this, and ``simp`` can close the goal immediately, so you
shouldn’t use it too soon, but rather use the provided lemmas.
OMIT. -/
/- TEXT:
もちろんMathlibはこの事実をすでに知っており， ``simp`` はすぐにゴールを閉じることができるため，早急に用いず，代わりに補題を用いましょう．
EXAMPLES: -/
-- QUOTE:

open Module LinearMap Matrix

-- OMIT: Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
-- `LinearMap.toMatrix` が代数の射であることから導かれるいくつかの補題
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- OMIT: Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
-- ``Matrix.det`` が乗法的モノイド射であることから導かれるいくつかの補題
#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have F : M = P' * M' * P := by
    rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  have F' : P' * P = 1 := by
    rw [← toMatrix_comp, id_comp, toMatrix_id]
  rw [F, Matrix.det_mul, Matrix.det_mul,
      show P'.det * M'.det * P.det = P'.det * P.det * M'.det by ring, ← Matrix.det_mul, F',
      Matrix.det_one, one_mul]
-- BOTH:
end

-- QUOTE.
/- OMIT:

Dimension
^^^^^^^^^

OMIT. -/
/- TEXT:
次元
^^^^^^^^^

TEXT. -/
/- OMIT:
Returning to the case of a single vector space, bases are also useful to define the concept of
dimension.
Here again, there is the elementary case of finite-dimensional vector spaces.
For such spaces we expect a dimension which is a natural number.
This is ``Module.finrank``. It takes the base field as an explicit argument
since a given abelian group can be a vector space over different fields.

OMIT. -/
/- TEXT:
単一のベクトル空間の場合に戻ると，基底は次元の概念を定義するのにも便利です．ここでもまた，有限次元ベクトル空間のための初歩的なケースがあります．このような空間では，自然数である次元が期待されます．これが ``Module.finrank`` です．これは基底の体を明示的な引数として取ります．というのも与えられた可換群は異なる体上のベクトル空間になりうるからです．
EXAMPLES: -/
-- QUOTE:
section
#check (Module.finrank K V : ℕ)

-- OMIT: `Fin n → K` is the archetypical space with dimension `n` over `K`.
-- `Fin n → K` は `K` 上の次元 `n` の典型的な空間です．
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- OMIT: Seen as a vector space over itself, `ℂ` has dimension one.
-- それ自身をベクトル空間と見なすと， `ℂ` は1次元です．
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- OMIT: But as a real vector space it has dimension two.
-- しかし，実数ベクトル空間では2次元です．
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- QUOTE.
/- OMIT:
Note that ``Module.finrank`` is defined for any vector space. It returns
zero for infinite dimensional vector spaces, just as division by zero returns zero.

OMIT. -/
/- TEXT:
``Module.finrank`` は任意のベクトル空間に対して定義されることに注意してください．0による除算が0を返すように，無限次元のベクトル空間では0を返します．

TEXT. -/
/- OMIT:
Of course many lemmas require a finite dimension assumption. This is the role of
the ``FiniteDimensional`` typeclass. For instance, think about how the next
example fails without this assumption.
OMIT. -/
/- TEXT:
もちろん，多くの補題は有限次元の仮定を必要とします．これが ``FiniteDimensional`` 型クラスの役割です．例えば，次の例がこの仮定なしでどのように失敗するか考えてみましょう．
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff

-- QUOTE.
/- OMIT:
In the above statement, ``Nontrivial V`` means ``V`` has at least two different elements.
Note that ``Module.finrank_pos_iff`` has no explicit argument.
This is fine when using it from left to right, but not when using it from right to left
because Lean has no way to guess ``K`` from the statement ``Nontrivial V``.
In that case it is useful to use the name argument syntax, after checking that the lemma
is stated over a ring named ``R``. So we can write:
OMIT. -/
/- TEXT:
上記の文において， ``Nontrivial V`` は ``V`` が少なくとも2つの異なる要素を持つことを意味します． ``Module.finrank_pos_iff`` には明示的な引数が無いことに注意してください．これは左から右へ使う場合には問題ありませんが，右から左へ使う場合には問題があります．というのも，Leanは ``Nontrivial V`` という文から ``K`` を推測することができないからです．このような場合，補題が ``R`` という名前の環の上で述べられていることを確認した後，名前引数の構文を使うことが便利です．従って以下のように書くことができます：
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

-- QUOTE.
/- OMIT:
The above spelling is strange because we already have ``h`` as an assumption, so we could
just as well give the full proof ``Module.finrank_pos_iff.1 h`` but it
is good to know for more complicated cases.

OMIT. -/
/- TEXT:
上記の書き方は奇妙です．というのもすでに仮定として ``h`` があるため，完全な証明である ``Module.finrank_pos_iff.1 h`` を与えることができるためです．とはいえ，より複雑なケースのために知っておいて損はないでしょう．

TEXT. -/
/- OMIT:
By definition, ``FiniteDimensional K V`` can be read from any basis.
OMIT. -/
/- TEXT:
定義より， ``FiniteDimensional K V`` は任意の基底からも読むことができます．
EXAMPLES: -/
-- QUOTE:
variable {ι : Type*} (B : Basis ι K V)

example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
-- QUOTE.
/- OMIT:
Using that the subtype corresponding to a linear subspace has a vector space structure,
we can talk about the dimension of a subspace.
OMIT. -/
/- TEXT:
線形部分空間に対応する部分型がベクトル空間構造を持つことを利用して，部分空間の次元について話すことができます．
EXAMPLES: -/
-- QUOTE:

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E
-- QUOTE.
/- OMIT:
In the first statement above, the purpose of the type ascriptions is to make sure that
coercion to ``Type*`` does not trigger too early.

OMIT. -/
/- TEXT:
上記の最初の文では，型を明記するの目的は ``Type*`` への強制が早く発動しすぎないようにすることです．

TEXT. -/
/- OMIT:
We are now ready for an exercise about ``finrank`` and subspaces.
OMIT. -/
/- TEXT:
これで ``finrank`` と部分空間についての演習の準備が整いました．
EXAMPLES: -/
-- QUOTE:
example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← finrank_pos_iff (R := K)]
  have := Submodule.finrank_sup_add_finrank_inf_eq E F
  have := Submodule.finrank_le E
  have := Submodule.finrank_le F
  have := Submodule.finrank_le (E ⊔ F)
  linarith
-- BOTH:
end
-- QUOTE.

/- OMIT:
Let us now move to the general case of dimension theory. In this case
``finrank`` is useless, but we still have that, for any two bases of the same
vector space, there is a bijection between the types indexing those bases. So we
can still hope to define the rank as a cardinal, i.e. an element of the “quotient of
the collection of types under the existence of a bijection equivalence
relation”.

OMIT. -/
/- TEXT:
ここで次元論について一般的なケースに移りましょう．この場合， ``finrank`` は役に立ちませんが，同じベクトル空間の任意の2つの基底に対して，それらの基底を添字付ける型の間に全単射が存在することに変わりはありません．したがって，ランクを濃度，つまり「全単射の同値関係が存在する場合の型の集合の商」の要素として定義することが望めます．

TEXT. -/
/- OMIT:
When discussing cardinal, it gets harder to ignore foundational issues around Russel’s paradox
like we do everywhere else in this book.
There is no type of all types because it would lead to logical inconsistencies.
This issue is solved by the hierarchy of universes that
we usually try to ignore.

OMIT. -/
/- TEXT:
濃度を論じるとき，本書の他のあらゆるところでそうしているように，ラッセルのパラドックスにまつわる基礎的な問題を無視することは難しくなります．論理的矛盾につながるため，すべての型の型は存在しません．この問題は，通常無視しようとしている宇宙の階層によって解決されます．

TEXT. -/
/- OMIT:
Each type has a universe level, and those levels behave similarly to natural
numbers. In particular there is zeroth level, and the corresponding universe
``Type 0`` is simply denoted by ``Type``. This universe is enough to hold
almost all of classical mathematics. For instance ``ℕ`` and ``ℝ`` have type ``Type``.
Each level ``u`` has a successor denoted
by ``u + 1``, and ``Type u`` has type ``Type (u+1)``.

OMIT. -/
/- TEXT:
各型には宇宙レベルがあり，それらのレベルは自然数と同じように振る舞います．特に，0番目のレベルが存在し，対応する宇宙 ``Type 0`` は単に ``Type`` を表記されます．この宇宙は古典数学のほとんどすべてを保持するのに十分です．例えば， ``ℕ`` と ``ℝ`` は ``Type`` 型を持ちます．各レベル ``u`` は ``u + 1`` で示される後続を持ち， ``Type u`` は ``Type (u+1)`` 型を持ちます．

TEXT. -/
/- OMIT:
But universe levels are not natural numbers, they have a really different nature and don’t
have a type. In particular you cannot state in Lean something like ``u ≠ u + 1``.
There is simply no type where this would take place. Even stating
``Type u ≠ Type (u+1)`` does not make any sense since ``Type u`` and ``Type (u+1)``
have different types.

OMIT. -/
/- TEXT:
しかし，宇宙レベルは自然数ではなく，実際に異なる性質を持っており，また型を持ちません．特に， ``u ≠ u + 1`` おようなことをLeanで述べることはできません．シンプルにこのようなことを表現する場所となる方が無いのです． ``Type u`` と ``Type (u+1)`` は型が異なるため， ``Type u ≠ Type (u+1)`` と書いたとしても意味を為さないのです．

TEXT. -/
/- OMIT:
Whenever we write ``Type*``, Lean inserts a universe level variable named ``u_n`` where ``n`` is a
number. This allows definitions and statements to live in all universes.

OMIT. -/
/- TEXT:
``Type*`` と書くと，Leanは ``u_n`` （ ``n`` は数値）という名前の宇宙レベルの変数を挿入します．これにより，定義や文がすべての宇宙で存在できるようになります．

TEXT. -/
/- OMIT:
Given a universe level ``u``, we can define an equivalence relation on ``Type u`` saying
two types ``α`` and ``β`` are equivalent if there is a bijection between them.
The quotient type ``Cardinal.{u}`` lives in ``Type (u+1)``. The curly braces
denote a universe variable. The image of ``α : Type u`` in this quotient is
``Cardinal.mk α : Cardinal.{u}``.

OMIT. -/
/- TEXT:
ある宇宙レベル ``u`` が与えられると， ``Type u`` に対して2つの型 ``α`` と ``β`` の間に全単射があれば等価であるという同値関係を定義することができます．商の型 ``Cardinal.{u}`` は ``Type (u+1)`` の中に存在します．波括弧は宇宙変数を表します．この商における ``α : Type u`` の像は ``Cardinal.mk α : Cardinal.{u}`` です．

TEXT. -/
/- OMIT:
But we cannot directly compare cardinals in different universes. So technically we
cannot define the rank of a vector space ``V`` as the cardinal of all types indexing
a basis of ``V``.
So instead it is defined as the supremum ``Module.rank K V`` of cardinals of
all linearly independent sets in ``V``. If ``V`` has universe level ``u`` then
its rank has type ``Cardinal.{u}``.


OMIT. -/
/- TEXT:
しかし，異なる宇宙の濃度を直接比較することはできません．したがって技術的にはベクトル空間 ``V`` のランクを ``V`` の基底を添字付けるすべての型の濃度として定義することはできません．そのため，代わりに ``V`` におけるすべての線形独立集合の濃度の上限 ``Module.rank K V`` として定義します． ``V`` が宇宙レベル ``u`` を持つ場合，そのランクは ``Cardinal.{u}`` 型を持ちます．
EXAMPLES: -/
-- QUOTE:
#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}

-- QUOTE.
/- OMIT:
One can still relate this definition to bases. Indeed there is also a commutative ``max``
operation on universe levels, and given two universe levels ``u`` and ``v``
there is an operation ``Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}``
that allows to put cardinals in a common universe and state the dimension theorem.
OMIT. -/
/- TEXT:
この定義を基底に関連付けることもできます．実際，宇宙レベルには可換な演算 ``max`` も存在し，2つの宇宙レベル ``u`` と ``v`` が与えられると共通の宇宙に濃度を置くことができる演算 ``Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}`` が存在し，次元についての定理を述べることができます．
EXAMPLES: -/
-- QUOTE:

universe u v -- `u` and `v` will denote universe levels

variable {ι : Type u} (B : Basis ι K V)
         {ι' : Type v} (B' : Basis ι' K V)

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
-- QUOTE.
/- OMIT:
We can relate the finite dimensional case to this discussion using the coercion
from natural numbers to finite cardinals (or more precisely the finite cardinals which live in ``Cardinal.{v}`` where ``v`` is the universe level of ``V``).
OMIT. -/
/- TEXT:
自然数から有限濃度（正確には ``Cardinal.{v}`` に存在する有限濃度で， ``v`` は ``V`` の宇宙レベル）への強制を使って，有限次元のケースをこの議論に関連づけることができます．
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
-- QUOTE.
