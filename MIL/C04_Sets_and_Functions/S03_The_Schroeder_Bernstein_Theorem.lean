import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

/- OMIT:
The Schröder-Bernstein Theorem
------------------------------

OMIT. -/
/- TEXT:
.. _the_schroeder_bernstein_theorem:

シュレーダー＝ベルンシュタインの定理
-------------------------------------

TEXT. -/
/- OMIT:
We close this chapter with an elementary but nontrivial theorem of set theory.
Let :math:`\alpha` and :math:`\beta` be sets.
(In our formalization, they will actually be types.)
Suppose :math:`f : \alpha → \beta` and :math:`g : \beta → \alpha`
are both injective.
Intuitively, this means that :math:`\alpha` is no bigger than :math:`\beta` and vice-versa.
If :math:`\alpha` and :math:`\beta` are finite, this implies that
they have the same cardinality, which is equivalent to saying that there
is a bijection between them.
In the nineteenth century, Cantor stated that same result holds even in the
case where :math:`\alpha` and :math:`\beta` are infinite.
This was eventually established by Dedekind, Schröder, and Bernstein
independently.

OMIT. -/
/- TEXT:
本章の最後として，集合論の初歩ですが，自明ではない定理を述べましょう． :math:`\alpha` と :math:`\beta` を集合とします．（ここで行う形式化においては型とします） :math:`f : \alpha → \beta` と :math:`g : \beta → \alpha` がどちらも単射であると仮定します．直観的に， :math:`\alpha` が :math:`\beta` よりも大きくなく，また逆も同様であることを意味します．もし :math:`\alpha` と :math:`\beta` が有限集合である場合，これは両者が同じ濃度を持つことを意味します．19世紀，カントールは :math:`\alpha` と :math:`\beta` が無限の場合でも同じ結果が成り立つことを示しました．この事実はデデキント，シュレーダー，ベルンシュタインによってもそれぞれ独立に証明されています．

TEXT. -/
/- OMIT:
Our formalization will introduce some new methods that we will explain
in greater detail in chapters to come.
Don't worry if they go by too quickly here.
Our goal is to show you that you already have the skills to contribute
to the formal proof of a real mathematical result.

OMIT. -/
/- TEXT:
本書での形式化では後の章で詳しく説明する予定の新しい技法をいくつか導入します．ここではさっと説明するにとどめますが心配しないでください．ここでのゴールは実際の数学的結果の形式的な証明に貢献するスキルを，読者がすでに持っていることを示すことです．

TEXT. -/
/- OMIT:
To understand the idea behind the proof, consider the image of the map
:math:`g` in :math:`\alpha`.
On that image, the inverse of :math:`g` is defined and is a bijection
with :math:`\beta`.

OMIT. -/
/- TEXT:
この証明の背後にある考え方を理解するために， :math:`\alpha` における写像 :math:`g` の像を考えてみましょう．この像において， :math:`g` の逆関数が定義され， :math:`\beta` について全単射となります．

.. image:: /figures/schroeder_bernstein1.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

TEXT. -/
/- OMIT:
The problem is that the bijection does not include the shaded region
in the diagram, which is nonempty if :math:`g` is not surjective.
Alternatively, we can use :math:`f` to map all of
:math:`\alpha` to :math:`\beta`,
but in that case the problem is that if :math:`f` is not surjective,
it will miss some elements of :math:`\beta`.

OMIT. -/
/- TEXT:
問題は， :math:`g` が全射出ない場合にはこの全単射が図中の斜線部分を含まないことです．これに対して :math:`f` を使って :math:`\alpha` の全要素を :math:`\beta` に写すこともできますが，その場合 :math:`f` が全射でなければ :math:`\beta` の要素がいくつか漏れてしまうという問題があります．

.. image:: /figures/schroeder_bernstein2.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

TEXT. -/
/- OMIT:
But now consider the composition :math:`g \circ f` from :math:`\alpha` to
itself. Because the composition is injective, it forms a bijection between
:math:`\alpha` and its image, yielding a scaled-down copy of :math:`\alpha`
inside itself.

OMIT. -/
/- TEXT:
しかし，ここで :math:`\alpha` からそれ自身への合成 :math:`g \circ f` を考えてみましょう．この合成は単射となるため， :math:`\alpha` とその像の間に全単射を構成し， :math:`\alpha` の縮小されたコピーを :math:`\alpha` 自身の中に生成します．

.. image:: /figures/schroeder_bernstein3.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

TEXT. -/
/- OMIT:
This composition maps the inner shaded ring to yet another such
set, which we can think of as an even smaller concentric shaded ring,
and so on.
This yields a
concentric sequence of shaded rings, each of which is in
bijective correspondence with the next.
If we map each ring to the next and leave the unshaded
parts of :math:`\alpha` alone,
we have a bijection of :math:`\alpha` with the image of :math:`g`.
Composing with :math:`g^{-1}`, this yields the desired
bijection between :math:`\alpha` and :math:`\beta`.

OMIT. -/
/- TEXT:
この合成は内側の斜線となっているリング [#f1]_ を，同心円状で小さくしたリングとしてさらにもう片方の集合の中に写します．これによって斜線のリングによる同心円の列が形成されます．この列のそれぞれの斜線のリングは次のリングと全単射となっています．もし各リングを次のリングに対応させ， :math:`\alpha` の斜線となっていない部分だけ残すと， :math:`\alpha` と :math:`g` のイメージの全単射が得られます．これを :math:`g^{-1}` と合成すると，お望みの :math:`\alpha` と :math:`\beta` の間の全単射が得られます．

TEXT. -/
/- OMIT:
We can describe this bijection more simply.
Let :math:`A` be the union of the sequence of shaded regions, and
define :math:`h : \alpha \to \beta` as follows:

OMIT. -/
/- TEXT:
この全単射をもっと簡単に説明することもできます． :math:`A` を一連の斜線領域の合併とし， :math:`h : \alpha \to \beta` を以下のように定義します:

.. math::

  h(x) = \begin{cases}
    f(x) & \text{if $x \in A$} \\
    g^{-1}(x) & \text{otherwise.}
  \end{cases}

TEXT. -/
/- OMIT:
In other words, we use :math:`f` on the shaded parts,
and we use the inverse of :math:`g` everywhere else.
The resulting map :math:`h` is injective
because each component is injective
and the images of the two components are disjoint.
To see that it is surjective,
suppose we are given a :math:`y` in :math:`\beta`, and
consider :math:`g(y)`.
If :math:`g(y)` is in one of the shaded regions,
it cannot be in the first ring, so we have :math:`g(y) = g(f(x))`
for some :math:`x` is in the previous ring.
By the injectivity of :math:`g`, we have :math:`h(x) = f(x) = y`.
If :math:`g(y)` is not in the shaded region,
then by the definition of :math:`h`, we have :math:`h(g(y))= y`.
Either way, :math:`y` is in the image of :math:`h`.

OMIT. -/
/- TEXT:
言い換えると，斜線部分には :math:`f` を用い，それ以外には :math:`g` の逆関数を使います．この結果得られる写像 :math:`h` は単射となります．なぜなら :math:`h` を構成している2つの関数はそれぞれ単射であり，この2つの像は互いに素であるためです．この関数が全射であることを確認するために， :math:`\beta` の要素 :math:`y` が与えられたと仮定し， :math:`g(y)` を考えます．もし :math:`g(y)` が斜線領域のどこかにいるならば，この斜線領域のリングの列の一番最初のリングにいることはありえないため， :math:`x` が前のリングに存在する場合， :math:`g(y) = g(f(x))` となります． :math:`g` の単射性により， :math:`h(x) = f(x) = y` が成り立ちます．もし :math:`g(y)` が斜線領域に入っていなければ， :math:`h` の定義により， :math:`h(g(y))= y` となります．いずれにせよ :math:`y` は :math:`h` の像の中にいることになります．

TEXT. -/
/- OMIT:
This argument should sound plausible, but the details are delicate.
Formalizing the proof will not only improve our confidence in the
result, but also help us understand it better.
Because the proof uses classical logic, we tell Lean that our definitions
will generally not be computable.
OMIT. -/
/- TEXT:
この議論はもっともらしく聞こえることでしょうが，細部は微妙です．証明を形式化することは結果に対する信頼性を高めるだけでなく，よりよく理解するための助けにもなります．この証明では古典論理を使うため，本書の定義が一般には計算不可能であることをLeanに伝えます．
BOTH: -/
-- QUOTE:
noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]
-- QUOTE.

/- OMIT:
The annotation ``[Nonempty β]`` specifies that ``β`` is nonempty.
We use it because the Mathlib primitive that we will use to
construct :math:`g^{-1}` requires it.
The case of the theorem where :math:`\beta` is empty is trivial,
and even though it would not be hard to generalize the formalization to cover
that case as well, we will not bother.
Specifically, we need the hypothesis ``[Nonempty β]`` for the operation
``invFun`` that is defined in Mathlib.
Given ``x : α``, ``invFun g x`` chooses a preimage of ``x``
in ``β`` if there is one,
and returns an arbitrary element of ``β`` otherwise.
The function ``invFun g`` is always a left inverse if ``g`` is injective
and a right inverse if ``g`` is surjective.

OMIT. -/
/- TEXT:
注釈 ``[Nonempty β]`` は ``β`` が空でないことを示します．これは :math:`g^{-1}` を構成するために使用するMathlibのプリミティブがこの前提を必要とするためです． :math:`\beta` がからである場合，定理は自明になります．そのケースをカバーするために形式化を一般化することは難しくありませんが，ここでは省略します．具体的にはMathlibで定義されている演算 ``invFun`` を使うにあたって仮定 ``[Nonempty β]`` が必要になります． ``x : α`` が与えられた時， ``invFun g x`` は ``β`` に ``x`` の逆像があればそれを選び，なければ ``β`` の任意の要素を返します．関数 ``invFun g`` は ``g`` が単射であれば常に左逆であり， ``g`` が全射であれば常に右逆です．

-- LITERALINCLUDE: inv_fun g

TEXT. -/
/- OMIT:
We define the set corresponding to the union of the shaded regions as follows.

OMIT. -/
/- TEXT:
斜線領域の合併に対応する集合を次のように定義します．

BOTH: -/
section
-- QUOTE:
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
-- QUOTE.

/- OMIT:
The definition ``sb_aux`` is an example of a *recursive definition*,
which we will explain in the next chapter.
It defines a sequence of sets

OMIT. -/
/- TEXT:
定義 ``sb_aux`` は次章で説明する *再帰的定義(recursive definition)* の一例です．これは以下の集合の列を定義します．

.. math::

  S_0 &= \alpha ∖ g(\beta) \\
  S_{n+1} &= g(f(S_n)).

TEXT. -/
/- OMIT:
The definition ``sb_set`` corresponds to the set
:math:`A = \bigcup_{n \in \mathbb{N}} S_n` in our proof sketch.
The function :math:`h` described above is now defined as follows:
OMIT. -/
/- TEXT:
定義 ``sb_set`` は証明のスケッチで出てきた集合 :math:`A = \bigcup_{n \in \mathbb{N}} S_n` に対応します．上述の関数 :math:`h` は次のように定義されます:
BOTH: -/
-- QUOTE:
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
-- QUOTE.

/- OMIT:
We will need the fact that our definition of :math:`g^{-1}` is a
right inverse on the complement of :math:`A`,
which is to say, on the non-shaded regions of :math:`\alpha`.
This is so because the outermost ring, :math:`S_0`, is equal to
:math:`\alpha \setminus g(\beta)`, so the complement of :math:`A` is
contained in :math:`g(\beta)`.
As a result, for every :math:`x` in the complement of :math:`A`,
there is a :math:`y` such that :math:`g(y) = x`.
(By the injectivity of :math:`g`, this :math:`y` is unique,
but next theorem says only that ``inv_fun g x`` returns some ``y``
such that ``g y = x``.)

OMIT. -/
/- TEXT:
本書で定義した :math:`g^{-1}` が :math:`A` の補集合，つまり :math:`\alpha` の斜線外の領域に対して右逆であるという事実が必要です．これは一番外側のリングである :math:`S_0` が :math:`\alpha \setminus g(\beta)` に等しいため， :math:`A` の補集合は :math:`g(\beta)` に含まれるからです．その結果 :math:`A` の補集合に含まれるすべての :math:`x` に対して， :math:`g(y) = x` となる :math:`y` が存在します．（ :math:`g` の単射性により，この :math:`y` は一意ですが，次の定理では ``invFun g x`` は ``g y = x`` となる ``y`` を返すだけです．）

TEXT. -/
/- OMIT:
Step through the proof below, make sure you understand what is going on,
and fill in the remaining parts.
You will need to use ``inv_fun_eq`` at the end.
Notice that rewriting with ``sb_aux`` here replaces ``sb_aux f g 0``
with the right-hand side of the corresponding defining equation.
OMIT. -/
/- TEXT:
以下の証明を見て，大筋をつかめたら残りの部分を埋めてみてください．最後に ``inv_fun_eq`` を使う必要があります．ここで ``sb_aux`` を使って書き直すと ``sb_aux f g 0`` が対応する定義している等式の右辺に置き換わることに注意しましょう．
BOTH: -/
-- QUOTE:
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact ⟨mem_univ _, hx⟩
-- BOTH:
  have : ∃ y, g y = x := by
/- EXAMPLES:
    sorry
  sorry
SOLUTIONS: -/
    simp at this
    assumption
  exact invFun_eq this
-- BOTH:
-- QUOTE.

/- OMIT:
We now turn to the proof that :math:`h` is injective.
Informally, the proof goes as follows.
First, suppose :math:`h(x_1) = h(x_2)`.
If :math:`x_1` is in :math:`A`, then :math:`h(x_1) = f(x_1)`,
and we can show that :math:`x_2` is in :math:`A` as follows.
If it isn't, then we have :math:`h(x_2) = g^{-1}(x_2)`.
From :math:`f(x_1) = h(x_1) = h(x_2)` we have :math:`g(f(x_1)) = x_2`.
From the definition of :math:`A`, since :math:`x_1` is in :math:`A`,
:math:`x_2` is in :math:`A` as well, a contradiction.
Hence, if :math:`x_1` is in :math:`A`, so is :math:`x_2`,
in which case we have :math:`f(x_1) = h(x_1) = h(x_2) = f(x_2)`.
The injectivity of :math:`f` then implies :math:`x_1 = x_2`.
The symmetric argument shows that if :math:`x_2` is in :math:`A`,
then so is :math:`x_1`, which again implies :math:`x_1 = x_2`.

OMIT. -/
/- TEXT:
次に :math:`h` が単射であることの証明に移りましょう．非形式的には証明は次のようになります．まず :math:`h(x_1) = h(x_2)` とします．もし :math:`x_1` が :math:`A` の中にあれば， :math:`h(x_1) = f(x_1)` であり， :math:`x_2` が :math:`A` の中にあることは以下のように示すことができます．仮に :math:`A` の中にない場合， :math:`h(x_2) = g^{-1}(x_2)` となります． :math:`f(x_1) = h(x_1) = h(x_2)` より， :math:`g(f(x_1)) = x_2` が成り立ちます． :math:`A` の定義から， :math:`x_1` は :math:`A` の中にあるため :math:`x_2` も :math:`A` の中にあることになり，矛盾します．従って :math:`x_1` が :math:`A` にあれば， :math:`x_2` も :math:`A` にあり， :math:`f(x_1) = h(x_1) = h(x_2) = f(x_2)` となります． :math:`f` の単射性から :math:`x_1 = x_2` が導かれます．上記の対称的な議論から :math:`x_2` が :math:`A` にあれば :math:`x_1` も同様であることが示され， :math:`x_1 = x_2` が導かれます．

TEXT. -/
/- OMIT:
The only remaining possibility is that neither :math:`x_1` nor :math:`x_2`
is in :math:`A`. In that case, we have
:math:`g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)`.
Applying :math:`g` to both sides yields :math:`x_1 = x_2`.

OMIT. -/
/- TEXT:
残る可能性は :math:`x_1` と :math:`x_2` のどちらも :math:`A` にないということだけです．この場合， :math:`g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)` となります．両辺に :math:`g` を適用することで :math:`x_1 = x_2` となります．

TEXT. -/
/- OMIT:
Once again, we encourage you to step through the following proof
to see how the argument plays out in Lean.
See if you can finish off the proof using ``sb_right_inv``.
OMIT. -/
/- TEXT:
もう一度，Leanでどのように議論が展開されるかを見るために，以下の証明を一行ごとに確認することをお勧めします． ``sb_right_inv`` を使って証明を終わらせることができるかも試してみてください．
BOTH: -/
-- QUOTE:
theorem sb_injective (hf : Injective f) (hg : Injective g) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
/- EXAMPLES:
        sorry
SOLUTIONS: -/
        rw [hxeq, sb_right_inv f g x₂nA]
-- BOTH:
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
-- BOTH:
  push_neg  at xA
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]
-- BOTH:
-- QUOTE.

/- OMIT:
The proof introduces some new tactics.
To start with, notice the ``set`` tactic, which introduces abbreviations
``A`` and ``h`` for ``sb_set f g`` and ``sb_fun f g`` respectively.
We name the corresponding defining equations ``A_def`` and ``h_def``.
The abbreviations are definitional, which is to say, Lean will sometimes
unfold them automatically when needed.
But not always; for example, when using ``rw``, we generally need to
use ``A_def`` and ``h_def`` explicitly.
So the definitions bring a tradeoff: they can make expressions shorter
and more readable, but they sometimes require us to do more work.

OMIT. -/
/- TEXT:
この証明ではいくつか新しいタクティクを導入しています．まず ``set`` タクティクに注目します．これは ``sb_set f g`` と ``sb_fun f g`` に対してそれぞれ ``A`` と ``h`` という略語を導入するものです．またこの対応を定義する等式に ``A_def`` と ``h_def`` と名付けています．この省略は定義的なものであり，Leanは必要に応じて自動的に省略形を展開することがあります．しかし常に行われるわけではありません．例えば， ``rw`` を使用する場合，一般的には ``A_def`` と ``h_def`` を明示的に使用する必要があります．つまり，定義はトレードオフの関係にあるのです．式をより短く読みやすくすることができますが，時にはより多くの作業が必要に成ります．

TEXT. -/
/- OMIT:
A more interesting tactic is the ``wlog`` tactic, which encapsulates
the symmetry argument in the informal proof above.
We will not dwell on it now, but notice that it does exactly what we want.
If you hover over the tactic you can take a look at its documentation.

OMIT. -/
/- TEXT:
より興味深いタクティクは ``wlog`` タクティクで，これは上記の非形式的な証明における対称性の議論をカプセル化したものです．このタクティクについては今触れませんが，このタクティクはまさに望みの挙動を実現しています．このタクティクにカーソルを合わせるとドキュメントを見ることができます．

TEXT. -/
/- OMIT:
The argument for surjectivity is even easier.
Given :math:`y` in :math:`\beta`,
we consider two cases, depending on whether :math:`g(y)` is in :math:`A`.
If it is, it can't be in :math:`S_0`, the outermost ring,
because by definition that is disjoint from the image of :math:`g`.
Thus it is an element of :math:`S_{n+1}` for some :math:`n`.
This means that it is of the form :math:`g(f(x))` for some
:math:`x` in :math:`S_n`.
By the injectivity of :math:`g`, we have :math:`f(x) = y`.
In the case where :math:`g(y)` is in the complement of :math:`A`,
we immediately have :math:`h(g(y))= y`, and we are done.

OMIT. -/
/- TEXT:
全射の議論はもっと簡単です． :math:`y` が :math:`\beta` にあるとすると， :math:`g(y)` が :math:`A` にあるかどうかによって2つのケースが考えられます．もし :math:`A` にある場合，定義上 :math:`g` の像とは素であるため，一番外側のリングである :math:`S_0` には入りえません．従って，これはある :math:`n` の :math:`S_{n+1}` の要素となります．これは :math:`S_n` の要素 :math:`x` に対して :math:`g(f(x))` の形であることを意味します． :math:`g` の単射性から :math:`f(x) = y` が成り立ちます． :math:`g(y)` が :math:`A` の補集合にある場合， :math:`h(g(y))= y` が直ちに得られるため，これで証明が完了します．

TEXT. -/
/- OMIT:
Once again, we encourage you to step through the proof and fill in
the missing parts.
The tactic ``cases n with n`` splits on the cases ``g y ∈ sb_aux f g 0``
and ``g y ∈ sb_aux f g n.succ``.
In both cases, calling the simplifier with ``simp [sb_aux]``
applies the corresponding defining equation of ``sb_aux``.
OMIT. -/
/- TEXT:
繰り返しになりますが，以下の証明を見て欠けている部分を埋めることをお勧めします．タクティク ``cases n with n`` は ``g y ∈ sb_aux f g 0`` と ``g y ∈ sb_aux f g n.succ`` の2つの場合に分かれます．どちらの場合も， ``simp [sb_aux]`` で簡約化器を呼び出すと， ``sbAux`` の対応する定義の等式が適用されます．
BOTH: -/
-- QUOTE:
theorem sb_surjective (hf : Injective f) (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  use g y
  simp only [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg
-- BOTH:
-- QUOTE.

end

/- OMIT:
We can now put it all together. The final statement is short and sweet,
and the proof uses the fact that ``Bijective h`` unfolds to
``Injective h ∧ Surjective h``.
OMIT. -/
/- TEXT:
これですべてをまとめることができます．この証明は ``Bijective h`` が ``Injective h ∧ Surjective h`` に展開されることを利用しているため，短く，そして美しいものになっています．
EXAMPLES: -/
-- QUOTE:
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩
-- QUOTE.

-- Auxiliary information
section
variable (g : β → α) (x : α)

-- TAG: inv_fun g
#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)
-- TAG: end

end
/- TEXT:
.. [#f1] 訳注: 本節中で「リング」と書いている箇所はすべて説明に用いられた図中の集合内にある斜線等で表現された輪を指し，代数構造の環のことを指しません．
TEXT. -/
