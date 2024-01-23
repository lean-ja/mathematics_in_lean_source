import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true

/- OMIT:
Basics
------

OMIT. -/
/- TEXT:
.. _section_hierarchies_basics:

基礎
------

TEXT. -/
/- OMIT:
At the very bottom of all hierarchies in Lean, we find data-carrying
classes. The following class records that the given type ``α`` is endowed with
a distinguished element called ``one``. At this stage, it has no property at all.
OMIT. -/
/- TEXT:
Leanのすべての階層の一番下にはデータを格納するためのクラスが存在します．次のクラスは与えられた型 ``α`` が ``one`` という名前で識別される要素を保持します．この段階ではこのクラスはなんの性質も持ちません．
BOTH: -/

-- QUOTE:
class One₁ (α : Type) where
  /-- The element one -/
  one : α
-- QUOTE.

/- OMIT:
Since we'll make a much heavier use of classes in this chapter, we need to understand some
more details about what the ``class`` command is doing.
First, the ``class`` command above defines a structure ``One₁`` with parameter ``α : Type`` and
a single field ``one``. It also mark this structure as a class so that arguments of type
``One₁ α`` for some type ``α`` will be inferrable using the instance resolution procedure,
as long as they are marked as instance-implicit, ie appear between square brackets.
Those two effects could also have been achieved using the ``structure`` command with ``class``
attribute, ie writing ``@[class] structure`` instance of ``class``. But the class command also
ensures that ``One₁ α`` appears as an instance-implicit argument in its own fields. Compare:
OMIT. -/
/- TEXT:
この章ではクラスを頻繁に使用するため， ``class`` コマンドが何を行っているか，もう少し詳しく理解する必要があります．まず，上記の ``class`` コマンドは， ``α : Type`` をパラメータとし，1つのフィールド ``one`` を持つ構造体 ``One₁`` を定義します．また，この構造体をクラスとしてマークすることで，ある型 ``α`` に対する ``One₁ α`` 型の引数は，暗黙のインスタンスとしてマークされている限り，つまり角括弧の間に表示されている限り，インスタンスを解決する手順を使用して推論できるようになります．この2つの効果は ``structure`` コマンドで ``class`` 属性を指定することで実現することもできます．つまり， ``@[class] structure`` のように記述するのです．しかし，classコマンドは， ``One₁ α`` が自身のフィールドの暗黙のインスタンスの引数として現れることを保証します．以下の例と比べてみましょう:
BOTH: -/

-- QUOTE:
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
-- QUOTE.

/- OMIT:
In the second check, we can see that ``self : One₂ α`` is an explicit argument.
Let us make sure the first version is indeed usable without any explicit argument.
OMIT. -/
/- TEXT:
2つ目のチェックでは， ``self : One₂ α`` が明示的な引数となっていることがわかります．最初のバージョンが本当に明示的な引数なしで使えるか確認してみましょう．
BOTH: -/

-- QUOTE:
example (α : Type) [One₁ α] : α := One₁.one
-- QUOTE.

/- OMIT:
Remark: in the above example, the argument ``One₁ α`` is marked as instance-implicit,
which is a bit silly since this affects only *uses* of the declaration and declaration created by
the ``example`` command cannot be used. However it allows to avoid giving a name to that
argument and, more importantly, it starts installing the good habit of marking ``One₁ α``
arguments as instance-implicit.

OMIT. -/
/- TEXT:
注意: 上記の例では，引数 ``One₁ α`` を暗黙のインスタンスとしてマークしていますが，これは宣言を *する* ことにのみ影響し， ``example`` コマンドで作成された宣言は使うことができないため少し馬鹿げています．しかし，これによりその引数に名前を避けることができ，さらに重要なことは ``One₁ α`` 引数を暗黙のインスタンスとしてマークする良い習慣を身につけ始めることができるでしょう．

TEXT. -/
/- OMIT:
Another remark is that all this will work only when Lean knows what is ``α``. In the above
example, leaving out the type ascription ``: α`` would generate an error message like:
``typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)``
where ``?m.263 α`` means "some type depending on ``α``" (and 263 is simply an auto-generated
index that would be useful to distinguish between several unknown things). Another way
to avoid this issue would be to use a type annotation, as in:
OMIT. -/
/- TEXT:
もう一つの注意点は，Leanが ``α`` がなんであるかを知っている場合にのみ，この操作は機能するという点です．上の例で全体の型 ``: α`` を省略すると ``typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)`` というようなエラーメッセージが表示されます．ここで ``?m.263 α`` は「 ``α`` に依存する何らかの型」を意味します．（263は単に自動生成されたインデックスで，未知のものを区別するのに便利です）この問題を避けるもう一つの方法は，次のように型注釈を使うことです:
BOTH: -/
-- QUOTE:
example (α : Type) [One₁ α] := (One₁.one : α)
-- QUOTE.

/- OMIT:
You may have already encountered that issue when playing with limits of sequences
in :numref:`sequences_and_convergence` if you tried to state for instance that
``0 < 1`` without telling Lean whether you meant this inequality to be about natural numbers
or real numbers.

OMIT. -/
/- TEXT:
:numref:`sequences_and_convergence` で数列の極限の話題において，例えば ``0 < 1`` を述べようとする際にこの不等式が自然数に関するものなのか実数に関するものなのかLeanに明示していなかった場合，すでにこの問題に遭遇しているかもしれません．

TEXT. -/
/- OMIT:
Our next task is to assign a notation to ``One₁.one``. Since we don't want collisions
with the builtin notation for ``1``, we will use ``𝟙``. This is achieved by the following
command where the first line tells Lean to use the documentation
of ``One₁.one`` as documentation for the symbol ``𝟙``.
OMIT. -/
/- TEXT:
次の目標は ``One₁.one`` に記法を割り当てることです．ここでは組み込みの ``1`` の表記と衝突したくないため， ``𝟙`` を使用します．これは以下のコマンドで実現されます．1行目ではLeanに ``One₁.one`` に関する情報を ``𝟙`` に関するものとして使用するように指示しています．
BOTH: -/
-- QUOTE:
@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
-- QUOTE.

/- OMIT:
We now want a data-carrying class recording a binary operation. We don't want to choose
between addition and multiplication for now so we'll use diamond.
OMIT. -/
/- TEXT:
次に二項演算を保持するデータ用のクラスを考えてみましょう．現時点では加算と乗算のどちらかを選びたくないため，ひし形を使うことにします．
BOTH: -/

-- QUOTE:
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
-- QUOTE.

/- OMIT:
As in the ``One₁`` example, the operation has no property at all at this stage. Let us
now define the class of semigroup structures where the operation is denoted by ``⋄``.
For now, we define it by hand as a structure with two fields, a ``Dia₁`` instance and some
``Prop``-valued field ``dia_assoc`` asserting associativity of ``⋄``.
OMIT. -/
/- TEXT:
``One₁`` の例と同様に，この演算はこの段階ではなんの性質も持ちません．ここで ``⋄`` で表現される演算を半群構造のクラスとして定義してみましょう．これにあたってとりあえず， ``Dia₁`` のインスタンスと ``⋄`` の結合性を保証する ``Prop`` -値のフィールド ``dia_assoc`` の2つのフィールドを持つ構造体として定義します．
BOTH: -/

-- QUOTE:
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- OMIT:
Note that while stating `dia_assoc`, the previously defined field `toDia₁` is in the local
context hence can be used when Lean searches for an instance of `Dia₁ α` to make sense
of `a ⋄ b`. However this `toDia₁` field does not become part of the type class instances database.
Hence doing ``example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b`` would fail with
error message ``failed to synthesize instance Dia₁ α``.

OMIT. -/
/- TEXT:
`dia_assoc` を記述する際に，これより上に定義しているフィールド `toDia₁` はここでのローカルな文脈にあるため，Leanが `Dia₁ α` のインスタンスを検索してくれるようになることで，Leanが `a ⋄ b` の意味を解釈してくれます．しかし，この `toDia₁` フィールドは型クラスのインスタンスの情報のデータベースには取り込まれません．したがって， ``example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b`` を実行すると， ``failed to synthesize instance Dia₁ α`` というエラーメッセージが表示されて失敗してしまいます．

TEXT. -/
/- OMIT:
We can fix this by adding the ``instance`` attribute later.
OMIT. -/
/- TEXT:
この問題は後から ``instance`` 属性を追加することで解決できます．
BOTH: -/

-- QUOTE:
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- OMIT:
Before building up, we need a more convenient way to extend structures than explicitly
writing fields like `toDia₁` and adding the instance attribute by hand. The ``class``
supports this using the ``extends`` syntax as in:
OMIT. -/
/- TEXT:
半群構造を組み上げる前に， `toDia₁` のようなフィールドを明示的に記述してインスタンス属性を手で追加するよりも便利な方法で構造体を拡張する方法がほしいところです． ``class`` は ``extends`` 記法を使ってこれをサポートします:
BOTH: -/

-- QUOTE:
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- OMIT:
Note this syntax is also available in the ``structure`` command, although it that
case it fixes only the hurdle of writing fields such as `toDia₁` since there
is no instance to define in that case.


OMIT. -/
/- TEXT:
この構文は ``structure`` コマンドでも利用出来ますが，その場合は定義するインスタンスがないため， `toDia₁` のようなフィールドを記述する手間を改善するだけです．

TEXT. -/
/- OMIT:
Let us now try to combine a diamond operation and a distinguished one with axioms saying
this element is neutral on both sides.
OMIT. -/
/- TEXT:
さて，ひし形の演算子と区別された1がこの演算子の両サイドで中立となるという公理を組み合わせてみましょう．
BOTH: -/
-- QUOTE:
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- QUOTE.

/- OMIT:
In the next example, we tell Lean that ``α`` has a ``DiaOneClass₁`` structure and state a
property that uses both a `Dia₁` instance and a `One₁` instance. In order to see how Lean finds
those instances we set a tracing option whose result can be seen in the info view. This result
is rather terse by default but can be expended by clicking one lines ending with black arrows.
It includes failed attempts where Lean tried to find instances before having enough type
information to succeed. The successful attempts do involve the instances generated by the
``extends`` syntax.
OMIT. -/
/- TEXT:
次の例では， ``α`` が ``DiaOneClass₁`` 構造を持つことをLeanに伝え， `Dia₁` インスタンスと `One₁` インスタンスの両方を使用するプロパティを定めます．Leanがこれらのインスタンスをどのように見つけるかを観察できるように，トレースオプションを設定しています．これで出力されるようになる結果は既定ではかなり簡潔ですが，黒い矢印で終わる行をクリックすることで詳細が表示されます．この中にはLeanがインスタンスの検索を成功するために十分な型情報を得る前に検索を行って失敗した結果もふくまれます．
BOTH: -/

-- QUOTE:
set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
-- QUOTE.

/- OMIT:
Note that we don't need to include extra fields where combining existing classes. Hence we can
define monoids as:
OMIT. -/
/- TEXT:
既存のクラスを組み合わせる際に，余分なフィールドを含める必要はないことに注意しましょう．したがって，モノイドを次のように定義することができます．
BOTH: -/

-- QUOTE:
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
-- QUOTE.

/- OMIT:
While the above definition seems straightforward, it hides an important subtlety. Both
``Semigroup₁ α`` and ``DiaOneClass₁ α`` extend ``Dia₁ α``, so one could fear that having
a ``Monoid₁ α`` instance gives two unrelated diamond operations on ``α``, one coming from
a field ``Monoid₁.toSemigroup₁`` and one coming from a field ``Monoid₁.toDiaOneClass₁``.

OMIT. -/
/- TEXT:
上記の定義は簡単なように見える一方，微妙ですが重要な点が隠されています． ``Semigroup₁ α`` と ``DiaOneClass₁ α`` のどちらも ``Dia₁ α`` を拡張しているので， ``Monoid₁ α`` のインスタンスを持つと， ``α`` に対して，1つは ``Monoid₁.toSemigroup₁`` から，そしてもう1つは ``Monoid₁.toDiaOneClass₁`` からと2つの無関係なひし形演算が生じてしまうのではないかという懸念が出てきます．

TEXT. -/
/- OMIT:
Indeed if we try to build a monoid class by hand using:
OMIT. -/
/- TEXT:
実際，モノイドクラスを明示的に手で作ろうとすると以下のようになります:
BOTH: -/

-- QUOTE:
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
-- QUOTE.

/- OMIT:
then we get two completely unrelated diamond operations
``Monoid₂.toSemigroup₁.toDia₁.dia`` and ``Monoid₂.toDiaOneClass₁.toDia₁.dia``.

OMIT. -/
/- TEXT:
したがって全く関係のない2つのひし形演算 ``Monoid₂.toSemigroup₁.toDia₁.dia`` と ``Monoid₂.toDiaOneClass₁.toDia₁.dia`` が得られます．

TEXT. -/
/- OMIT:
The version generated using the ``extends`` syntax does not have this defect.
OMIT. -/
/- TEXT:
しかし ``extends`` 構文を使って生成されたバージョンにはこの欠陥はありません．
BOTH: -/

-- QUOTE:
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
-- QUOTE.

/- OMIT:
So the ``class`` command did some magic for us (and the ``structure`` command would have done it
too). An easy way to see what are the fields of our classes is to check their constructor. Compare:
OMIT. -/
/- TEXT:
つまり ``class`` コマンドは私達のためにいくつかの魔法を使ってくれているのです．（そして ``structure`` コマンドでも同様でしょう）クラスのフィールドを確認する簡単な方法は，コンストラクタをチェックすることです．以下の2つを比較してみましょう:
BOTH: -/

-- QUOTE:
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
-- QUOTE.

/- OMIT:
So we see that ``Monoid₁`` takes ``Semigroup₁ α`` argument as expected but then it won't
take a would-be overlapping ``DiaOneClass₁ α`` argument but instead tears it apart and includes
only the non-overlapping parts. And it also auto-generated an instance ``Monoid₁.toDiaOneClass₁``
which is *not* a field but has the expected signature which, from the end-user point of view,
restores the symmetry between the two extended classes ``Semigroup₁`` and ``DiaOneClass₁``.
OMIT. -/
/- TEXT:
つまり， ``Monoid₁`` は期待される通り ``Semigroup₁ α`` を引数として取りますが，重複するはずの ``DiaOneClass₁ α`` を引数として取らず，代わりにそれをバラバラにして重複市内部分のみを含めるようにしていることがわかります．また，インスタンス ``Monoid₁.toDiaOneClass₁`` も自動生成されました．これはフィールドではありませんが，利用者から見て2つの拡張クラス ``Semigroup₁`` と ``DiaOneClass₁`` の間の対称性を保存することが期待されるはずで，これに対応した型注釈を持ちます．
BOTH: -/

-- QUOTE:
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
-- QUOTE.

/- OMIT:
We are now very close to defining groups. We could add to the monoid structure a field asserting
the existence of an inverse for every element. But then we would need to work to access these
inverses. In practice it is more convenient to add it as data. To optimize reusability,
we define a new data-carrying class, and then give it some notation.
OMIT. -/
/- TEXT:
これで群の定義にかなり近づきました．群にするために，モノイド構造のすべての元に逆元が存在することを保証するフィールドを追加することもできます．しかし，そうするとこれらの逆元にアクセスするための作業が必要になります．実際にはデータとして追加するほうが便利です．再利用性を高めるために，新しいデータ保持クラスを定義し，それにいくつかの表記法を与えることとします．
BOTH: -/

-- QUOTE:
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
-- QUOTE.

/- OMIT:
The above definition may seem too weak, we only ask that ``a⁻¹`` is a left-inverse of ``a``.
But the other side is automatic. In order to prove that, we need a preliminary lemma.
OMIT. -/
/- TEXT:
上記の定義では ``a⁻¹`` が ``a`` の左逆であることのみを要求しているため，弱すぎるように思えるかもしれません．しかし，もう一方の逆は自動的に求まります．それを証明するためには別で補題を用意する必要があります．
BOTH: -/

-- QUOTE:
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]
-- QUOTE.

/- OMIT:
In this lemma, it is pretty annoying to give full names, especially since it requires knowing
which part of the hierarchy provides those facts. One way to fix this is to use the ``export``
command to copy those facts as lemmas in the root name space.
OMIT. -/
/- TEXT:
この補題の証明で使っている各事実にはどの階層からのものかを知っておく必要があるため，各事実のフルネームを与えるのはかなり面倒です．これを解決する1つの方法は ``export`` コマンドを使ってこれらの事実をルートの名前空間に補題としてコピーすることです．
BOTH: -/

-- QUOTE:
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)
-- QUOTE.

/- OMIT:
We can then rewrite the above proof as:
OMIT. -/
/- TEXT:
これにより上記の証明を次のように書き換えることができます:
BOTH: -/

-- QUOTE:
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]
-- QUOTE.

/- OMIT:
It is now your turn to prove things about our algebraic structures.
OMIT. -/
/- TEXT:
次はここまで構築してきた代数的構造について読者が証明を行う番です．
BOTH: -/

-- QUOTE:
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv₁ (inv_dia a) h
-- BOTH:

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  by rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]
-- QUOTE.

/- OMIT:
At this stage we would like to move on to define rings, but there is a serious issue.
A ring structure on a type contains both an additive group structure and a multiplicative
monoid structure, and some properties about their interaction. But so far we hard-coded
a notation ``⋄`` for all our operations. More fundamentally, the type class system
assumes every type has only one instance of each type class. There are various
ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate
everything for additive and multiplicative theories with the help of some code-generating
attribute. Structures and classes are defined in both additive and multiplicative notation
with an attribute ``to_additive`` linking them. In case of multiple inheritance like for
semi-groups, the auto-generated "symmetry-restoring" instances need also to be marked.
This is a bit technical you don't need to understand details. The important point is that
lemmas are then only stated in multiplicative notation and marked with the attribute ``to_additive``
to generate the additive version as ``left_inv_eq_right_inv'`` with it's auto-generated additive
version ``left_neg_eq_right_neg'``. In order to check the name of this additive version we
used the ``whatsnew in`` command on top of ``left_inv_eq_right_inv'``.
OMIT. -/
/- TEXT:
この段階で環の定義に進みたいところですが，重大な問題が残っています．型上の環構造には加法群構造と乗法モノイド構造の両方がふくまれ，それらの相互作用についていくつかの性質があります．しかし，ここまですべての演算に ``⋄`` という表記法をハードコードしてしまっています．より基本的な事実として，型クラスシステムはすべての方がそれぞれの型クラスのインスタンスを1つだけ持っていると仮定します．この問題には多くの解決法があります．以外なことに，Mathlibは加法と乗法の理論のすべてを何らかのコード生成されたものを複製するという素朴な方法を採用しています．構造体やクラスは加法・乗法の両方で定義され，属性 ``to_additive`` がそれらをリンクします．半群のような多重継承の場合，自動生成される「対称性を保存する」インスタンスにもマークする必要があります．これは少し専門的な話なので，詳細を理解する必要はありません．重要な点は，補題は乗法の記法でのみ記述され， ``to_additive`` 属性をマークすることで加法バージョンを自動生成します．例えば ``left_inv_eq_right_inv'`` の自動生成される加法バージョンは version ``left_neg_eq_right_neg'`` です．この追加バージョンの名前を確認するために， ``left_inv_eq_right_inv'`` の上で ``whatsnew in`` コマンドを使用しました．
BOTH: -/

-- QUOTE:



class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- OMIT:
Equipped with this technology, we can easily define also commutative semigroups, monoids and
groups, and then define rings.

OMIT. -/
/- TEXT:
この技術を使えば，可換半群，モノイド，群も簡単に定義でき，環も定義できます．
BOTH: -/
-- QUOTE:
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
-- QUOTE.

/- OMIT:
We should remember to tag lemmas with ``simp`` when appropriate.
OMIT. -/
/- TEXT:
適切な場合には補題に ``simp`` タグをつけることを覚えておきましょう．
BOTH: -/

-- QUOTE:
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

-- QUOTE.

/- OMIT:
Then we need to repeat ourselves a bit since we switch to standard notations, but at least
``to_additive`` does the work of translating from the multiplicative notation to the additive one.
OMIT. -/
/- TEXT:
ひし形演算子から標準的な表記に切り替えたため，ここから少し今までやったことを繰り返す必要がありますが，少なくとも ``to_additive`` によって乗法表記から加法表記への変換を行ってくれます．
BOTH: -/

-- QUOTE:
@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv' (Group₃.inv_mul a) h
-- BOTH:
-- QUOTE.

/- OMIT:
Note that ``to_additive`` can be ask to tag a lemma with ``simp`` and propagate that attribute
to the additive version as follows.
OMIT. -/
/- TEXT:
なお， ``to_additive`` は以下のように補題に ``simp`` タグを付け，その属性を加法バージョンに伝搬させるために使うことができます．
BOTH: -/

-- QUOTE:
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]
-- BOTH:

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [← mul_assoc₃] using congr_arg (a⁻¹ * ·) h
-- BOTH:

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h
-- BOTH:

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

-- QUOTE.

/- OMIT:
We are now ready for rings. For demonstration purposes we won't assume that addition is
commutative, and then immediately provide an instance of ``AddCommGroup₃``. Mathlib does not
play this game, first because in practice this does not make any ring instance easier and
also because Mathlib's algebraic hierarchy goes through semi-rings which are like rings but without
opposites so that the proof below does not work for them. What we gain here, besides a nice exercise
if you have never seen it, is an example of building an instance using the syntax that allows
to provide a parent structure and some extra fields.
OMIT. -/
/- TEXT:
これで環のための準備が整いました．ここでは階層構造の実演が目的なので，足し算が可換であると仮定してすぐに ``AddCommGroup₃`` のインスタンスを提供することはしません．Mathlibでもこのような方針はとりません．第一に，実際にはどの環のインスタンスも簡単なものにならず，またMathlibの代数階層は環と似ていますが加法の逆元のない半環を通るため，以下の証明が機能しないからです．ここで得られるものは，これらの代数構造を見たことがない人にとってのいい練習となること以外にも，親構造といくつかの追加フィールドを提供できる構文を使ったインスタンス構築の例を見られることです．
BOTH: -/

-- QUOTE:
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
/- EXAMPLES:
    sorry }
SOLUTIONS: -/
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := calc
      a + (a + b + b) = (a + a) + (b + b) := by simp [add_assoc₃, add_assoc₃]
      _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
      _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
      _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
      _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
      _ = (a + b) + (a + b) := by simp
      _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this) }
-- QUOTE.
/- OMIT:
Of course we can also build concrete instances, such as a ring structure on integers (of course
the instance below uses that all the work is already done in Mathlib).
OMIT. -/
/- TEXT:
もちろん整数上の環構造などの具体的なインスタンスを構築することもできます．（と言いつつ以下のインスタンスではMathlibですでに定義されているものを使っているだけですが．）
BOTH: -/

-- QUOTE:
instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- QUOTE.
/- OMIT:
As an exercise you can now set up a simple hierarchy for order relations, including a class
for ordered commutative monoids, which have both a partial order and a commutative monoid structure
such that ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b``. Of course you need to add fields and maybe
``extends`` clauses to the following classes.
OMIT. -/
/- TEXT:
ここまで理解できたなら半順序と ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b`` のような可換モノイド構造を持つ順序付けられた可換モノイドを含む簡単な順序関係の構築は良い演習となるでしょう．これにあたってはもちろん以下のクラスをそのまま使うのではなく，いくつかのフィールドや，場合によっては ``extends`` 節を追加する必要があります．
BOTH: -/
-- QUOTE:

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)
-- SOLUTIONS:
  extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
-- BOTH:

class PartialOrder₁ (α : Type)
-- SOLUTIONS:
  extends Preorder₁ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b
-- BOTH:

class OrderedCommMonoid₁ (α : Type)
-- SOLUTIONS:
  extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b
-- BOTH:

instance : OrderedCommMonoid₁ ℕ where
-- SOLUTIONS:
  le := (· ≤ ·)
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ ↦ le_trans
  le_antisymm := fun _ _ ↦ le_antisymm
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := fun _ _ h c ↦ Nat.mul_le_mul_left c h
-- QUOTE.
/- OMIT:



We now want to discuss algebraic structures involving several types. The prime example
is modules over rings. If you don't know what is a module, you can pretend it means vector space
and think that all our rings are fields. Those structures are commutative additive groups
equipped with a scalar multiplication by elements of some ring.

OMIT. -/
/- TEXT:

ここで複数の型から構成される代数的構造について議論したいと思います．代表的なものは環上のモジュールです．もしモジュールが何かを知らない場合，これはベクトル空間のことを指し，環ではなく体だと考えておくといいでしょう．これらの構造は，ある環の要素によるスカラー倍を備えた可換加法群です．

TEXT. -/
/- OMIT:
We first define the data-carrying type class of scalar multiplication by some type ``α`` on some
type ``β``, and give it a right associative notation.
OMIT. -/
/- TEXT:
まず，ある型 ``β`` 上のある型 ``α`` によるスカラー倍の計算を保持する型クラスを定義し，これに右に結合する記法を割り当てます．
BOTH: -/

-- QUOTE:
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
-- QUOTE.

/- OMIT:
Then we can define modules (again think about vector spaces if you don't know what is a module).
TEXT. -/
/- OMIT:
次にモジュールを定義します．（モジュールとは何か知らない人はベクトル空間を思い出しましょう．）
BOTH: -/

-- QUOTE:
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
-- QUOTE.

/- OMIT:
There is something interesting going on here. While it isn't too surprising that the
ring structure on ``R`` is a parameter in this definition, you probably expected ``AddCommGroup₃ M``
to be part of the ``extends`` clause just as ``SMul₃ R M`` is.  Trying to do that would lead
to a mysterious sounding error message:
``cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M
all remaining arguments have metavariables: Ring₃ ?R @Module₁ ?R ?inst✝ M``.
In order to understand this message, you need to remember that such an ``extends`` clause would
lead to a field ``Module₃.toAddCommGroup₃`` marked as an instance. This instance
would have the signature appearing in the error message:
``(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M``.
With such an instance in the type class database, each time Lean would look for a
``AddCommGroup₃ M`` instance for some ``M``, it would need to go hunting for a completely
unspecified type ``R`` and a ``Ring₃ R`` instance before embarking on the main quest of finding a
``Module₁ R M`` instance. Those two side-quests are represented by the meta-variables mentioned in
the error message and denoted by ``?R`` and ``?inst✝`` there. Such a ``Module₃.toAddCommGroup₃``
instance would then be a huge trap for the instance resolution procedure and then ``class`` command
refuses to set it up.

OMIT. -/
/- TEXT:
ここでは興味深い書き方がされています．この定義でにおいて ``R`` 上の環構造がパラメータであることはそれほど驚くことではありませんが，おそらく ``SMul₃ R M`` と同じように ``AddCommGroup₃ M`` も ``extends`` 節の一部になると思われたのではないでしょうか？試しにそのようにすると次のような謎めいたエラーメッセージが表示されます． ``cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M all remaining arguments have metavariables: Ring₃ ?R @Module₁ ?R ?inst✝ M`` このメッセージを理解するためには，このような ``extends`` 節は，インスタンスとしてマークされたフィールド ``Module₃.toAddCommGroup₃`` を導入することを思い出しましょう．このインスタンスはエラーメッセージに表示されている ``(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M`` という型注釈を持ちます．型クラスのデータベースにこのようなインスタンスがある場合，Leanは ``M`` に対して ``AddCommGroup₃ M`` インスタンスを探すたびに，メインである ``Module₁ R M`` インスタンスの探索を行う前に，完全に未指定の型 ``R`` と ``Ring₃ R`` インスタンスを探しに行く必要があります．この2つの副次的な探索はエラーメッセージにて ``?R`` と ``?inst✝`` で示されるメタ変数として言及されます．この ``Module₃.toAddCommGroup₃`` のようなインスタンスはインスタンス解決プロセスにおいて大きな罠となり， ``class`` コマンドはこのクラスの設定を拒否します．

TEXT. -/
/- OMIT:
What about ``extends SMul₃ R M`` then? That one creates a field
``Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M``
whose end result ``SMul₃ R M`` mentions both ``R`` and ``M`` so this field can
safely be used as an instance. The rule is easy to remember: each class appearing in the
``extends`` clause should mention every type appearing in the parameters.

OMIT. -/
/- TEXT:
では ``extends SMul₃ R M`` はどうでしょうか？これは ``Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M`` というフィールドを作りますが，最終的な ``SMul₃ R M`` で ``R`` と ``M`` の両方に言及しているためこのフィールドはインスタンスとして安全に使うことができます．このルールを覚えるのは簡単です． ``extends`` 節に登場する各クラスは，パラメータに登場するすべての型に言及しなければならないのです．

TEXT. -/
/- OMIT:
Let us create our first module instance: a ring is a module over itself using its multiplication
as a scalar multiplication.
OMIT. -/
/- TEXT:
モジュールのインスタンスの1つ目を作成しましょう．環は，スカラー倍として乗算を使用するそれ自体の上のモジュールです．
BOTH: -/
-- QUOTE:
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib
-- QUOTE.
/- OMIT:
As a second example, every abelian group is a module over ``ℤ`` (this is one of the reason to
generalize the theory of vector spaces by allowing non-invertible scalars). First one can define
scalar multiplication by a natural number for any type equipped with a zero and an addition:
``n • a`` is defined as ``a + ⋯ + a`` where ``a`` appears ``n`` times. Then this is extended
to scalar multiplication by an integer by ensuring ``(-1) • a = -a``.
OMIT. -/
/- TEXT:
第二の例として，すべてのアーベル群は ``ℤ`` 上のモジュールとなります．（これは非可逆なスカラーを許容することでベクトル空間の理論を一般化するための理由の1つです）まず，0と加法を備えた任意の型への整数によるスカラー倍を定義します．ここで ``n • a`` は ``a`` が ``n`` 回現れる ``a + ⋯ + a`` として定義されます．ついで ``(-1) • a = -a`` を保証することで整数によるスカラー倍に拡張されます．
BOTH: -/
-- QUOTE:

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
-- QUOTE.
/- OMIT:
Proving this gives rise to a module structure is a bit tedious and not interesting for the
current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries
with proofs. If you insist on doing it then you will probably want to state and prove several
intermediate lemmas about ``nsmul₁`` and ``zsmul₁``.
OMIT. -/
/- TEXT:
これがモジュール構造を生むことを証明するのは少々面倒で，また今の議論においては面白くないのですべての公理をsorryとします．これらのsorryは *演習問題ではありません* ．もしどうしてもこれらのsorryを証明に置き換えたいのであれば， ``nsmul₁`` と ``zsmul₁`` に関するいくつかの中間的な補題を用意してから証明することになるでしょう．
BOTH: -/
-- QUOTE:

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- QUOTE.
/- OMIT:
A much more important issue is that we now have two module structures over the ring ``ℤ``
for ``ℤ`` itself: ``abGrpModule ℤ`` since ``ℤ`` is a abelian group, and ``selfModule ℤ`` since
``ℤ`` is a ring. Those two module structure correspond to the same abelian group structure,
but it is not obvious that they have the same scalar multiplication. They actually do, but
this isn't true by definition, it requires a proof. This is very bad news for the type class
instance resolution procedure and will lead to very frustrating failures for users of this
hierarchy. When directly asked to find an instance, Lean will pick one, and we can see
which one using:
OMIT. -/
/- TEXT:
より重要な問題は，環 ``ℤ`` は自身について2つのモジュール構造があるということです． ``abGrpModule ℤ`` は ``ℤ`` がアーベル群であること，そして ``selfModule ℤ`` は ``ℤ`` が環であることによるモジュールのインスタンスです．これら2つのモジュール構造は同じアーベル群構造に対応しますが，スカラー倍が同じであることは自明ではありません．実際には同じなのですが，これは定義上は真ではなく，証明が必要です．これは型クラスのインスタンス解決プロセスにとって非常に悪いニュースであり，この階層を利用するユーザーにとって非常にいらいらする失敗に繋がります．直接インスタンスを見つけることを要求すると，Leanは何か1つ選んできて，それが以下であることを確認できます．
BOTH: -/
-- QUOTE:

#synth Module₁ ℤ ℤ -- abGrpModule ℤ

-- QUOTE.
/- OMIT:
But in a more indirect context it can happen that Lean infers the one and then gets confused.
This situation is known as a bad diamond. This has nothing to do with the diamond operation
we used above, it refers to the way one can draw the paths from ``ℤ`` to its ``Module₁ ℤ``
going through either ``AddCommGroup₃ ℤ`` or ``Ring₃ ℤ``.

OMIT. -/
/- TEXT:
しかし，より間接的な文脈では，Leanはこのインスタンスを推測するため，混乱を生じることがあります．このような状況は悪いダイアモンドとして知られています．これは上記で使用したひし形演算子とは関係ないもので， ``ℤ`` から ``Module₁ ℤ`` への道を ``AddCommGroup₃ ℤ`` か ``Ring₃ ℤ`` のどちらをも経由できてしまうことを指します．

TEXT. -/
/- OMIT:
It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere
in Mathlib, and also in this chapter. Already at the very beginning we saw one can go
from ``Monoid₁ α`` to ``Dia₁ α`` through either ``Semigroup₁ α`` or ``DiaOneClass₁ α`` and
thanks to the work done by the ``class`` command, the resulting two ``Dia₁ α`` instances
are definitionally equal. In particular a diamond having a ``Prop``-valued class at the bottom
cannot be bad since any too proofs of the same statement are definitionally equal.

OMIT. -/
/- TEXT:
すべてのダイアモンドが悪いわけではないことを理解することが重要です．実際，Mathlibにはいたるところにダイアモンドがあり，この章にもダイアモンドがあります．すでに冒頭で ``Monoid₁ α`` から ``Semigroup₁ α`` または ``DiaOneClass₁ α`` のどちらかを経由して ``Dia₁ α`` に行くことができ， ``class`` コマンドのおかげで結果として得られる2つの ``Dia₁ α`` インスタンスが定義上等しいことを見ました．特に，一番下に ``Prop`` 値のクラスを持つダイアモンドは，同じ文の証明が定義上等しくなることから悪いダイアモンドとなることはありません．

TEXT. -/
/- OMIT:
But the diamond we created with modules is definitely bad. The offending piece is the ``smul``
field which is data, not a proof, and we have two constructions that are not definitionally equal.
The robust way of fixing this issue is to make sure that going from a rich structure to a
poor structure is always done by forgetting data, not by defining data. This well-known pattern
as been named "forgetful inheritance" and extensively discussed in
https://inria.hal.science/hal-02463336.

OMIT. -/
/- TEXT:
しかしモジュールで作ったダイアモンドは間違いなく悪いものです．問題なのは証明ではなくデータである ``smul`` フィールドで，2つの定義的に等しくない構成を持つことに成ります．この問題を解決する確実な方法は，豊かな構造から貧しい構造への移行がデータの定義によってではなく常にデータを忘れることによって行われることを自覚することです．このよく知られたパターンは「忘却継承」と名付けられ， https://inria.hal.science/hal-02463336 で広く議論されています．

TEXT. -/
/- OMIT:
In our concrete case, we can modify the definition of ``AddMonoid₃`` to include a ``nsmul`` data
field and some ``Prop``-valued fields ensuring this operation is provably the one we constructed
above. Those fields are given default values using ``:=`` after their type in the definition below.
Thanks to these default values, most instances would be constructed exactly as with our previous
definitions. But in the special case of ``ℤ`` we will be able to provide specific values.
OMIT. -/
/- TEXT:
今回のケースでは， ``AddMonoid₃`` の定義を変更して， ``nsmul`` データフィールドと，この演算が上記で構成した証明可能なものであることを保証するいくつかの ``Prop`` 値フィールドを含めるように修正することができます．これらのフィールドは以下の定義で型の後に ``:=`` を使ってデフォルト値が与えられている．これらのデフォルト値のおかげで，ほとんどのインスタンスは以前の定義と同じように構築されます．しかし， ``ℤ`` の特殊なケースでは，特定の値を指定することができます．
BOTH: -/
-- QUOTE:

class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
-- QUOTE.
/- OMIT:

Let us check we can still construct a product monoid instance without providing the ``nsmul``
related fields.
OMIT. -/
/- TEXT:
``nsmul`` に関連するフィールドを提供しなくても積モノイドのインスタンスを構築できることを確認してみましょう．
BOTH: -/
-- QUOTE:

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
-- QUOTE.
/- OMIT:
And now let us handle the special case of ``ℤ`` where we want to build ``nsmul`` using the coercion
of ``ℕ`` to ``ℤ`` and the multiplication on ``ℤ``. Note in particular how the proof fields
contain more work than in the default value above.
OMIT. -/
/- TEXT:
いよいよ ``ℤ`` の特殊なケースを扱いましょう．ここでは， ``ℕ`` から ``ℤ`` への型強制と， ``ℤ`` の乗算を使用して ``nsmul`` を構築します．特に証明フィールドには上記のデフォルト値よりも多くの作業がふくまれていることに注意してください．
BOTH: -/
-- QUOTE:

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
-- QUOTE.
/- OMIT:
Let us check we solved our issue. Because Lean already has a definition of scalar multiplication
of a natural number and an integer, and we want to make sure our instance is used, we won't use
the ``•`` notation but call ``SMul.mul`` and explicitly provide our instance defined above.
OMIT. -/
/- TEXT:
問題が解決下かどうか確認してみましょう．Leanにはすでに自然数と整数のスカラー倍の定義があり，またここでは上記で定義したインスタンスが使われることを確認したいため， ``•`` 表記は使わず， ``SMul.mul`` を呼び出し，上記のインスタンスを明示的に提供します．
BOTH: -/
-- QUOTE:

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- QUOTE.
/- OMIT:
This story then continues with incorporating a ``zsmul`` field into the definition of groups
and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules
in Mathlib. There are more complicated than what we have seen here, because they are part of a huge
hierarchy, but all principles have been explained above.

OMIT. -/
/- TEXT:
この話は群の定義に ``zsmul`` フィールドを組み込んだり，似たようなトリックを使ったりしながら続きます．これでMathlibのモノイド，群，環，モジュールの定義を読む準備ができました．これらは巨大な階層の一部であるため，ここで見たものよりも複雑ですが，すべての原理は上で説明したとおりです．

TEXT. -/
/- OMIT:
As an exercise, you can come back to the order relation hierarchy you built above and try
to incorporate a type class ``LT₁`` carrying the Less-Than notation ``<₁`` and make sure
that every preorder comes with a ``<₁`` which has a default value built from ``≤₁`` and a
``Prop``-valued field asserting the natural relation between those two comparison operators.
OMIT. -/
/- TEXT:
演習として上で構築した順序関係階層に戻り，「より小さい」記法 ``<₁`` を持つ型クラス ``LT₁`` を組み込み，すべての前順序に ``≤₁`` から構築されたデフォルト値を持つ ``<₁`` とこれら2つの比較演算子の間の自然な関係を確認する ``Prop`` 値フィールドが付属していることを確認しましょう．
TEXT. -/

-- SOLUTIONS:

class LT₁ (α : Type) where
  /-- The Less-Than relation -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class PreOrder₂ (α : Type) extends LE₁ α, LT₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
  lt := fun a b ↦ a ≤₁ b ∧ ¬b ≤₁ a
  lt_iff_le_not_le : ∀ a b : α, a <₁ b ↔ a ≤₁ b ∧ ¬b ≤₁ a := by intros; rfl
