-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

/- OMIT:
Sequences and Convergence
-------------------------

OMIT. -/
/- TEXT:
.. _sequences_and_convergence:

数列と収束
-----------

TEXT. -/
/- OMIT:
We now have enough skills at our disposal to do some real mathematics.
In Lean, we can represent a sequence :math:`s_0, s_1, s_2, \ldots` of
real numbers as a function ``s : ℕ → ℝ``.
Such a sequence is said to *converge* to a number :math:`a` if for every
:math:`\varepsilon > 0` there is a point beyond which the sequence
remains within :math:`\varepsilon` of :math:`a`,
that is, there is a number :math:`N` such that for every
:math:`n \ge N`, :math:`| s_n - a | < \varepsilon`.
In Lean, we can render this as follows:
OMIT. -/
/- TEXT:
これで本格的な数学ができる準備が整いました．Leanでは実数上の数列 :math:`s_0, s_1, s_2, \ldots` は関数 ``s : ℕ → ℝ`` で表すことができます．すべての :math:`\varepsilon > 0` に対して，数列上のある点以降の点がすべて :math:`a` から :math:`\varepsilon > 0` 以内の範囲に収まる場合，この数列は :math:`a` に *収束* すると言います．つまり，すべての :math:`n \ge N` に対して :math:`| s_n - a | < \varepsilon` となるような数 :math:`N` が存在するということです．Leanではこれは次のように表現できます．
BOTH: -/
-- QUOTE:
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

/- OMIT:
The notation ``∀ ε > 0, ...`` is a convenient abbreviation
for ``∀ ε, ε > 0 → ...``, and, similarly,
``∀ n ≥ N, ...`` abbreviates ``∀ n, n ≥ N →  ...``.
And remember that ``ε > 0``, in turn, is defined as ``0 < ε``,
and ``n ≥ N`` is defined as ``N ≤ n``.

OMIT. -/
/- TEXT:
``∀ ε > 0, ...`` という記法は ``∀ ε, ε > 0 → ...`` の便利な省略形で，また同じように ``∀ n ≥ N, ...`` も ``∀ n, n ≥ N →  ...`` の省略形です．そして ``ε > 0`` は ``0 < ε`` として， ``n ≥ N`` は ``N ≤ n`` としてそれぞれ定義されるということも覚えておきましょう．

.. index:: extensionality, ext, tactics ; ext

TEXT. -/
/- OMIT:
In this section, we'll establish some properties of convergence.
But first, we will discuss three tactics for working with equality
that will prove useful.
The first, the ``ext`` tactic,
gives us a way of proving that two functions are equal.
Let :math:`f(x) = x + 1` and :math:`g(x) = 1 + x`
be functions from reals to reals.
Then, of course, :math:`f = g`, because they return the same
value for every :math:`x`.
The ``ext`` tactic enables us to prove an equation between functions
by proving that their values are the same
at all the values of their arguments.
OMIT. -/
/- TEXT:
本節では，収束に関していくつかの性質を証明します．しかしその前に，等式を扱う際に役立つ3つのタクティクについて説明しましょう．まず初めに， ``ext`` タクティクは2つの関数が等しいことを証明するのに役立ちます．例えば :math:`f(x) = x + 1` と :math:`g(x) = 1 + x` を実数から実数への関数とします．このとき当たり前ですが，2つの関数はすべての :math:`x` に対して同じ値を返すため :math:`f = g` となります．このように ``ext`` タクティクは関数が等しいということの証明を，すべての引数に対して等しい値を返すことの証明に帰着してくれます．
TEXT. -/
-- QUOTE:
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring
-- QUOTE.

/- OMIT:
We'll see later that ``ext`` is actually more general, and also one can
specify the name of the variables that appear.
For instance you can try to replace ``ext`` with ``ext u v`` in the
above proof.
The second tactic, the ``congr`` tactic,
allows us to prove an equation between two expressions
by reconciling the parts that are different:
OMIT. -/
/- TEXT:
.. index:: congr, tactics ; congr

後で見ていきますが， ``ext`` は実はもっと汎用的で，登場する変数の名前を指定することもできます．例えば上記の例で ``ext`` を ``ext u v`` に置き換えることができます．2つ目のタクティクは ``congr`` タクティクで，これは2つの式が等しいということの証明を式中の異なる部分が実は等しいという証明に帰着するものです．
TEXT. -/
-- QUOTE:
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring
-- QUOTE.

/- OMIT:
Here the ``congr`` tactic peels off the ``abs`` on each side,
leaving us to prove ``a = a - b + b``.

OMIT. -/
/- TEXT:
ここでは ``congr`` タクティクが両辺の ``abs`` を剥がし， ``a = a - b + b`` を証明すればいいだけの状態にします．

.. index:: convert, tactics ; convert

TEXT. -/
/- OMIT:
Finally, the ``convert`` tactic is used to apply a theorem
to a goal when the conclusion of the theorem doesn't quite match.
For example, suppose we want to prove ``a < a * a`` from ``1 < a``.
A theorem in the library, ``mul_lt_mul_right``,
will let us prove ``1 * a < a * a``.
One possibility is to work backwards and rewrite the goal
so that it has that form.
Instead, the ``convert`` tactic lets us apply the theorem
as it is,
and leaves us with the task of proving the equations that
are needed to make the goal match.
OMIT. -/
/- TEXT:
最後に， ``convert`` タクティクを使うことで結論がゴールに完全に一致しないような定理でもゴールに適用することができます．例えば ``1 < a`` から ``a < a * a`` を証明したいとしましょう．ライブラリには ``mul_lt_mul_right`` という定理があり，これを使えば ``1 * a < a * a`` を証明することができます．これを用いる方法の一つは，逆算してその形になるようにゴールを書き直すことでしょう．この代わりに ``convert`` タクティクは定理をそのまま適用でき，ゴールと定理の差分を埋めるのに必要な等式を，新たな証明すべきゴールとします．
TEXT. -/
-- QUOTE:
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
-- QUOTE.

/- OMIT:
This example illustrates another useful trick: when we apply an
expression with an underscore
and Lean can't fill it in for us automatically,
it simply leaves it for us as another goal.

OMIT. -/
/- TEXT:
この例ではまた別の便利な技法を示しています．アンダースコアを含む式を ``apply`` すると，Leanはまずそれを自動的に埋めようとし，埋められない場合には単にそれが新しいゴールになります．

TEXT. -/
/- OMIT:
The following shows that any constant sequence :math:`a, a, a, \ldots`
converges.
OMIT. -/
/- TEXT:
以下では定数列 :math:`a, a, a, \ldots` が収束することを示しています．
BOTH: -/
-- QUOTE:
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
-- QUOTE.

/- OMIT:
Lean has a tactic, ``simp``, which can often save you the
trouble of carrying out steps like ``rw [sub_self, abs_zero]``
by hand.
We will tell you more about it soon.

OMIT. -/
/- TEXT:
.. TODO: reference to the simplifier

Leanには ``simp`` というタクティクがあり，これは ``rw [sub_self, abs_zero]`` のような式変形のステップを手作業で書く手間を省いてくれます．これについては近々詳しく説明しましょう．

TEXT. -/
/- OMIT:
For a more interesting theorem, let's show that if ``s``
converges to ``a`` and ``t`` converges to ``b``, then
``fun n ↦ s n + t n`` converges to ``a + b``.
It is helpful to have a clear pen-and-paper
proof in mind before you start writing a formal one.
Given ``ε`` greater than ``0``,
the idea is to use the hypotheses to obtain an ``Ns``
such that beyond that point, ``s`` is within ``ε / 2``
of ``a``,
and an ``Nt`` such that beyond that point, ``t`` is within
``ε / 2`` of ``b``.
Then, whenever ``n`` is greater than or equal to the
maximum of ``Ns`` and ``Nt``,
the sequence ``fun n ↦ s n + t n`` should be within ``ε``
of ``a + b``.
The following example begins to implement this strategy.
See if you can finish it off.
OMIT. -/
/- TEXT:
より興味深い定理として，もし ``s`` が ``a`` に， ``t`` が ``b`` に収束するならば， ``fun n ↦ s n + t n`` は ``a + b`` に収束することを示しましょう．形式的な証明を始める前に，紙とペンでどう証明するか明確にイメージしておくと良いでしょう．証明の方針は正の数 ``ε`` が与えられたとき， ``s`` の添え字でそれ以降 ``s`` が常に ``a`` から ``ε / 2`` 以内に収まるような ``Ns`` と， ``t`` の添え字でそれ以降 ``t`` が常に ``b`` から ``ε / 2`` 以内に収まるような ``Nt`` を仮定を使ってそれぞれ求めることです．そして ``n`` が ``Ns`` と ``Nt`` の最大値以上であるとき， ``fun n ↦ s n + t n`` は ``a + b`` から ``ε`` 以内にあるはずです．以下ではこの方針を実装します．証明を完成させてみましょう．
TEXT. -/
-- QUOTE:
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_addαα {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := (abs_add _ _)
    _ < ε / 2 + ε / 2 := (add_lt_add (hs n ngeNs) (ht n ngeNt))
    _ = ε := by norm_num

/- OMIT:
As hints, you can use ``le_of_max_le_left`` and ``le_of_max_le_right``,
and ``norm_num`` can prove ``ε / 2 + ε / 2 = ε``.
Also, it is helpful to use the ``congr`` tactic to
show that ``|s n + t n - (a + b)|`` is equal to
``|(s n - a) + (t n - b)|,``
since then you can use the triangle inequality.
Notice that we marked all the variables ``s``, ``t``, ``a``, and ``b``
implicit because they can be inferred from the hypotheses.

OMIT. -/
/- TEXT:
ヒントとして， ``le_of_max_le_left`` と ``le_of_max_le_right`` が役に立ちます．あと ``norm_num`` を使うことで ``ε / 2 + ε / 2 = ε`` を証明できます．また， ``|s n + t n - (a + b)|`` が ``|(s n - a) + (t n - b)|`` と等しいことを示すにあたっては ``congr`` が有用でしょう．これによって三角不等式を使うことができる形になります．ここで変数 ``s`` ， ``t`` ， ``a`` ， ``b`` は仮定から推測できるため，すべて暗黙の変数としました．

TEXT. -/
/- OMIT:
Proving the same theorem with multiplication in place
of addition is tricky.
We will get there by proving some auxiliary statements first.
See if you can also finish off the next proof,
which shows that if ``s`` converges to ``a``,
then ``fun n ↦ c * s n`` converges to ``c * a``.
It is helpful to split into cases depending on whether ``c``
is equal to zero or not.
We have taken care of the zero case,
and we have left you to prove the result with
the extra assumption that ``c`` is nonzero.
OMIT. -/
/- TEXT:
足し算を掛け算に換えて同様の定理を証明しようとすると，少し難しくなります．まずいくつか補助的な命題を証明することが必要です．次の，もし ``s`` が ``a`` に収束するならば， ``fun n ↦ c * s n`` は ``c * a`` に収束するという命題の証明も完成させてみましょう．この証明にあたって ``c`` が0に等しいかどうかでケースを分けると便利です．0のケースについては埋めておくので， ``c`` が0ではない場合のケースを証明してみましょう．
TEXT. -/
-- QUOTE:
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_mul_constαα {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := (mul_lt_mul_of_pos_left (hs n ngt) acpos)
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm

/- OMIT:
The next theorem is also independently interesting:
it shows that a convergent sequence is eventually bounded
in absolute value.
We have started you off; see if you can finish it.
OMIT. -/
/- TEXT:
次の定理も興味深いものです: 収束する数列は，有限個を除けば絶対値を一様に上から抑えることができることを示しています．初めの部分は示しているので，残りを証明してみましょう．
TEXT. -/
-- QUOTE:
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem exists_abs_le_of_convergesToαα {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |s n - a + a| := by
      congr
      abel
    _ ≤ |s n - a| + |a| := (abs_add _ _)
    _ < |a| + 1 := by linarith [h n ngt]

/- OMIT:
In fact, the theorem could be strengthened to assert
that there is a bound ``b`` that holds for all values of ``n``.
But this version is strong enough for our purposes,
and we will see at the end of this section that it
holds more generally.

OMIT. -/
/- TEXT:
実は，この定理をより強く，すべての ``n`` の値に対して成り立つ上界 ``b`` が存在するとしても証明できます．この事実は今の目的には十分強力ですが，本節の最後でより一般的に成り立つことを確かめます．

TEXT. -/
/- OMIT:
The next lemma is auxiliary: we prove that if
``s`` converges to ``a`` and ``t`` converges to ``0``,
then ``fun n ↦ s n * t n`` converges to ``0``.
To do so, we use the previous theorem to find a ``B``
that bounds ``s`` beyond some point ``N₀``.
See if you can understand the strategy we have outlined
and finish the proof.
OMIT. -/
/- TEXT:
次の補題は補助的なもので，もし ``s`` が ``a`` に収束し， ``t`` が ``0`` に収束するならば， ``fun n ↦ s n * t n`` は ``0`` に収束することを証明します．このためには前の定理を用いてある点 ``N₀`` 以降で ``s`` の上界となる ``B`` を見つけます．おおまかな方針が理解できたら以下の証明をやってみましょう．
TEXT. -/
-- QUOTE:
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

/- OMIT:
If you have made it this far, congratulations!
We are now within striking distance of our theorem.
The following proof finishes it off.
OMIT. -/
/- TEXT:
うまくできましたか？おめでとうございます！私達は今や，目指す定理を射程圏内に収めました．次の証明で完成です．
TEXT. -/
-- QUOTE:
-- BOTH:
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
-- QUOTE.

/- OMIT:
For another challenging exercise,
try filling out the following sketch of a proof that limits
are unique.
(If you are feeling bold,
you can delete the proof sketch and try proving it from scratch.)
OMIT. -/
/- TEXT:
演習問題として，極限が一意であることを証明する以下のスケッチを完成させることに挑戦してみましょう．（もしいけそうなら証明のスケッチを削除してイチから証明してみてもいいでしょう．）
TEXT. -/
-- QUOTE:
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_uniqueαα {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this

/- OMIT:
We close the section with the observation that our proofs can be generalized.
For example, the only properties that we have used of the
natural numbers is that their structure carries a partial order
with ``min`` and ``max``.
You can check that everything still works if you replace ``ℕ``
everywhere by any linear order ``α``:
OMIT. -/
/- TEXT:
本節を終えるにあたってここまでの証明は一般化できることを述べておきましょう．例えば自然数について本節のここまでで用いてきた性質は，自然数の構造が半順序を持ち， ``min`` と ``max`` が定義できるということだけでした．証明中の ``ℕ`` をすべて線形順序を持つ任意の集合 ``α`` に置き換えてもうまく行くことを確認できます:
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

end

/- OMIT:
In :numref:`filters`, we will see that Mathlib has mechanisms
for dealing with convergence in vastly more general terms,
not only abstracting away particular features of the domain
and codomain,
but also abstracting over different types of convergence.
OMIT. -/
/- TEXT:
:numref:`filters` では，Mathlibには収束をより一般的に扱うためのメカニズムが用意されていることを見ていきます．フィルタは始域と終域の特定の特徴を抽象化するだけではなく，様々なタイプの収束を抽象化します．
TEXT. -/
