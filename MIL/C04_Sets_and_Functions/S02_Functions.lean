-- BOTH:
import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- OMIT:
Functions
---------

OMIT. -/
/- TEXT:
.. _functions:

関数
-----

TEXT. -/
/- OMIT:
If ``f : α → β`` is a function and  ``p`` is a set of
elements of type ``β``,
the library defines ``preimage f p``, written ``f ⁻¹' p``,
to be ``{x | f x ∈ p}``.
The expression ``x ∈ f ⁻¹' p`` reduces to ``f x ∈ p``.
This is often convenient, as in the following example:
OMIT. -/
/- TEXT:
``f : α → β`` が関数で ``p`` が ``β`` 型の項の集合であるとします．このとき ``p`` の ``f`` による逆像を考えることができますが，これはMathlibでは ``preimage f p`` と呼ばれ，``{x | f x ∈ p}`` として定義され，``f ⁻¹' p`` と表記されます．式 ``x ∈ f ⁻¹' p`` は ``f x ∈ p`` に簡約されます．次の例のようにこれはしばしば便利です:
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

-- EXAMPLES:
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl
-- QUOTE.

/- OMIT:
If ``s`` is a set of elements of type ``α``,
the library also defines ``image f s``,
written ``f '' s``,
to be ``{y | ∃ x, x ∈ s ∧ f x = y}``.
So a hypothesis  ``y ∈ f '' s`` decomposes to a triple
``⟨x, xs, xeq⟩`` with ``x : α`` satisfying the hypotheses ``xs : x ∈ s``
and ``xeq : f x = y``.
The ``rfl`` tag in the ``rintro`` tactic (see :numref:`the_existential_quantifier`) was made precisely
for this sort of situation.
OMIT. -/
/- TEXT:
また ``s`` が ``α`` 型の集合であるとします．このとき ``s`` の ``f`` による像が考えられますが，これはMathlibでは ``image f s`` と呼ばれ，``{y | ∃ x, x ∈ s ∧ f x = y}`` で定義され，``f '' s`` と表記されます．よって仮定 ``y ∈ f '' s`` は ``⟨x, xs, xeq⟩`` という３つ組に分解できます．これは ``x : α`` が仮定 ``xs : x ∈ s`` と ``xeq : f x = y`` を満たすことを意味しています． ``rintro`` タクティク内で用いられている ``rfl`` タグ（ :numref:`the_existential_quantifier` 参照）はまさにこのような状況のために設計されています．
TEXT. -/
-- QUOTE:
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt
-- QUOTE.

/- OMIT:
Notice also that the ``use`` tactic applies ``rfl``
to close goals when it can.

OMIT. -/
/- TEXT:
また ``use`` タクティクを使うと， ``rfl`` を適用することでゴールに近づけることができる場合には ``rfl`` を適用してくれることにも注意してください．

TEXT. -/
/- OMIT:
Here is another example:
OMIT. -/
/- TEXT:
ここで別の例を見てみましょう．
TEXT. -/
-- QUOTE:
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs
-- QUOTE.

/- OMIT:
We can replace the line ``use x, xs`` by
``apply mem_image_of_mem f xs`` if we want to
use a theorem specifically designed for that purpose.
But knowing that the image is defined in terms
of an existential quantifier is often convenient.

OMIT. -/
/- TEXT:
``use x, xs`` という行は，まさに ``f x ∈ f '' s`` を示すための専用の定理 ``mem_image_of_mem f xs`` で置き換えることもできます．しかし，像が存在量化子で定義されていることを知っていると何かと便利なことが多いものです．

TEXT. -/
/- OMIT:
The following equivalence is a good exercise:
OMIT. -/
/- TEXT:
次の同値を示すことは良い演習問題になるでしょう．
TEXT. -/
-- QUOTE:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

/- OMIT:
It shows that ``image f`` and ``preimage f`` are
an instance of what is known as a *Galois connection*
between ``Set α`` and ``Set β``,
each partially ordered by the subset relation.
In the library, this equivalence is named
``image_subset_iff``.
In practice, the right-hand side is often the
more useful representation,
because ``y ∈ f ⁻¹' t`` unfolds to ``f y ∈ t``
whereas working with ``x ∈ f '' s`` requires
decomposing an existential quantifier.

OMIT. -/
/- TEXT:
この命題は ``image f`` と ``preimage f`` が一種の **ガロア接続** （Galois connection） [#f21]_ であることを主張しています．ここではベキ集合 ``Set α`` と ``Set β`` が部分集合の包含関係に関して半順序集合になっています．Mathlibでは，この同値性は ``image_subset_iff`` と名付けられています．実際に使う場合には右辺がより便利な表現であることが多いです．なぜなら， ``y ∈ f ⁻¹' t`` は ``f y ∈ t`` に展開されるのに対し， ``x ∈ f '' s`` を扱うには存在量化子を分解する必要があるからです．

TEXT. -/
/- OMIT:
Here is a long list of set-theoretic identities for
you to enjoy.
You don't have to do all of them at once;
do a few of them,
and set the rest aside for a rainy day.
OMIT. -/
/- TEXT:
読者に楽しんでいただくため，ここに集合についての等式をたくさん用意しました．これらすべてを一度にやる必要はありません．いくつかやったら，残りは雨の日のためにとっておきましょう．
TEXT. -/
-- QUOTE:
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xmem, rfl⟩
  exact xmem

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxeq⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x; apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  · use x, xs
  · use x, xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
  use x₁
  constructor
  · use x₁s
    rw [← h fx₂eq]
    exact x₂t
  · rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, h⟩
  use x₁
  constructor
  · constructor
    · exact x₁s
    · intro h'
      apply h
      use x₁, h'
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  right; exact fxu

/- OMIT:
You can also try your hand at the next group of exercises,
which characterize the behavior of images and preimages
with respect to indexed unions and intersections.
In the third exercise, the argument ``i : I`` is needed
to guarantee that the index set is nonempty.
To prove any of these, we recommend using ``ext`` or ``intro``
to unfold the meaning of an equation or inclusion between sets,
and then calling ``simp`` to unpack the conditions for membership.
OMIT. -/
/- TEXT:
また，次に挙げる集合族の合併と共通部分に関する像と逆像の挙動についての演習問題に挑戦するのもよいでしょう．3番目の演習問題では，添字集合が空でないことを保証するために ``i : I`` という引数が必要です．これらの証明にあたっては， ``ext`` や ``intro`` を使って集合間の等式や包含関係を要素の式に展開し，次いで ``simp`` を使って要素の帰属についての条件を展開することをお勧めします．
BOTH: -/
-- QUOTE:
variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
-- BOTH:

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩
-- BOTH:

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq
-- BOTH:

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp
-- BOTH:

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp
-- QUOTE.

-- OMIT:
/-
In type theory, a function ``f : α → β`` can be applied to any
element of the domain ``α``,
but we sometimes want to represent functions that are
meaningfully defined on only some of those elements.
For example, as a function of type ``ℝ → ℝ → ℝ``,
division is only meaningful when the second argument is nonzero.
In mathematics, when we write an expression of the form ``s / t``,
we should have implicitly or explicitly ruled out
the case that ``t`` is zero.

OMIT. -/
/- TEXT:
型理論では，関数 ``f : α → β`` は始域 ``α`` の任意の要素に適用することができますが，一部の要素にのみ意味のある関数を表現したいこともあります．例えば， ``ℝ → ℝ → ℝ`` 型の関数として，除算は第2引数が0でないときのみ意味を持ちます．数学をする上で， ``s / t`` という形の式を書く時は， ``t`` が0である場合を暗黙的または明示的に除外しているはずです．

TEXT. -/
/- OMIT:
But since division has type ``ℝ → ℝ → ℝ`` in Lean,
it also has to return a value when the second argument is zero.
The strategy generally followed by the library is to assign such
functions convenient values outside their natural domain.
For example, defining ``x / 0`` to be ``0`` means that the
identity ``(x + y) / z = x / z + y / z`` holds for every
``x``, ``y``, and ``z``.

OMIT. -/
/- TEXT:
しかし，Leanでは除算は ``ℝ → ℝ → ℝ`` 型を持つので第2引数が0のときにも値を返さなければなりません．このような問題に対してMathlibでは，関数の自然な定義域の外でも便宜的に値を与えるという戦略が一般的に取られています．例えば， ``x / 0`` を ``0`` と定義すればすべての ``x`` ， ``y`` ， ``z`` に対して， ``(x + y) / z = x / z + y / z`` という等式が成り立ちます．

TEXT. -/
/- OMIT:
As a result, when we read an expression ``s / t`` in Lean,
we should not assume that ``t`` is a meaningful input value.
When we need to, we can restrict the statement of a theorem to
guarantee that it is.
For example, theorem ``div_mul_cancel`` asserts ``x ≠ 0 → x / y * y = x`` for
``x`` and ``y`` in suitable algebraic structures.

OMIT. -/
/- TEXT:
そのため，Leanで ``s / t`` という式を読むときに ``t`` が意味のある入力値であることを仮定すべきではありません．もしその仮定が必要である場合は，定理の仮定に制限を加えて，それが意味のある値であることを保証することができます．例えば，定理 ``div_mul_cancel`` は適切な代数構造の ``x`` と ``y`` に対して ``x ≠ 0 → x / y * y = x`` を保証するものです．

TEXT. -/
/- OMIT:
.. TODO: previous text (delete eventually)

.. The fact that in type theory a function is always totally
.. defined on its domain type
.. sometimes forces some difficult choices.
.. For example, if we want to define ``x / y`` and ``log x``
.. as functions on the reals,
.. we have to assign a value to the first when ``y`` is ``0``,
.. and a value to the second for ``x ≤ 0``.
.. The strategy generally followed by the Lean library
.. in these situations is to assign such functions somewhat arbitrary
.. but convenient values outside their natural domain.
.. For example, defining ``x / 0`` to be ``0`` means that the
.. identity ``(x + y) / z = x / z + y / z`` holds
.. for every ``x``, ``y``, and ``z``.
.. When you see a theorem in the library that uses the
.. division symbol,
.. you should be mindful that theorem depends on this
.. nonstandard definition,
.. but this generally does not cause problems in practice.
.. When we need to,
.. we can restrict the statement of a theorem so that
.. it does not rely on such values.
.. For example, if a theorem begins ``∀ x > 0, ...``,
.. dividing by ``x`` in the body of the statement is not problematic.
.. Limiting the scope of a quantifier in this way is known
.. as *relativization*.

.. TODO: comments from Patrick
.. This discussion is very important and we should really get it right. The natural tendency of mathematicians here is to think Lean does bullshit and will let them prove false things. So we should focus on why there is no issue, not on apologies or difficulties.

.. I think we could include a discussion of the fact that the meaning of f : α → β is actually more subtle that it seems. Saying f is a function from α to β is actually a slight oversimplification. The more nuanced meaning is that f is a function whose possible meaningful input values all have type α and whose output values have type β, but we should not assume that every term with type α is a meaningful input value.

.. Then we of course need to point out that defining terms of type α → β required to assign a value to every term of type α, and this can be irritating but this is balanced by the convenience of having a couple of unconditional lemma like the (x+y)/z thing.

.. Also, I feel it is very important to point out that real world math doesn't force you to (x+y)/⟨z, proof that z doesn't vanish⟩. So type theory is not different here.

.. TODO: deleted because we haven't discussed subtypes yet.
.. Be sure to do that eventually.
.. There are ways around this, but they are generally unpleasant.
.. For example, we can take ``log`` to be defined on
.. the subtype ``{ x // x > 0 }``,
.. but then we have to mediate between two different types,
.. the reals and that subtype.
-/

/- OMIT:
The library defines a predicate ``InjOn f s`` to say that
``f`` is injective on ``s``.
It is defined as follows:
OMIT. -/
/- TEXT:
Mathlibでは ``f`` が ``s`` 上で単射であることを示す ``InjOn f s`` という述語が定義されています．これは以下のように定義されています:
TEXT. -/
-- QUOTE:

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _
-- QUOTE.

-- BOTH:
end

/- OMIT:
The statement ``Injective f`` is provably equivalent
to ``InjOn f univ``.
Similarly, the library defines ``range f`` to be
``{x | ∃y, f y = x}``,
so ``range f`` is provably equal to ``f '' univ``.
This is a common theme in Mathlib:
although many properties of functions are defined relative
to their full domain,
there are often relativized versions that restrict
the statements to a subset of the domain type.

OMIT. -/
/- TEXT:
``Injective f`` は ``InjOn f univ`` に等価であることを証明することができます．同様にMathlibには ``{x | ∃y, f y = x}`` と定義される ``range f`` があり， ``range f`` と ``f '' univ`` が等しいことも証明可能です．このように関数の多くの特性は定義域全体に対して定義されますが，なかには定理の内容を定義域の部分集合に制限した相対化されたバージョンも存在します．これはMathlibでよく見られる方針です．

TEXT. -/
/- OMIT:
Here is are some examples of ``InjOn`` and ``range`` in use:
OMIT. -/
/- TEXT:
以下に ``InjOn`` と ``range`` の使用例を示します:
BOTH: -/
section

-- QUOTE:
open Set Real

-- EXAMPLES:
example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]
-- QUOTE.

/- OMIT:
Try proving these:
OMIT. -/
/- TEXT:
以下を証明してみましょう:
EXAMPLES: -/
-- QUOTE:
example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynonneg]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynonneg]


example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2
  dsimp at *
  constructor
  apply pow_nonneg ynonneg
  apply sqrt_sq
  assumption

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y
  exact sq_sqrt ynonneg

-- BOTH:
end

/- OMIT:
To define the inverse of a function ``f : α → β``,
we will use two new ingredients.
First, we need to deal with the fact that
an arbitrary type in Lean may be empty.
To define the inverse to ``f`` at ``y`` when there is
no ``x`` satisfying ``f x = y``,
we want to assign a default value in ``α``.
Adding the annotation ``[Inhabited α]`` as a variable
is tantamount to assuming that ``α`` has a
preferred element, which is denoted ``default``.
Second, in the case where there is more than one ``x``
such that ``f x = y``,
the inverse function needs to *choose* one of them.
This requires an appeal to the *axiom of choice*.
Lean allows various ways of accessing it;
one convenient method is to use the classical ``choose``
operator, illustrated below.
OMIT. -/
/- TEXT:
関数 ``f : α → β`` の逆関数を定義するにあたって，新しい概念を2つ用意しましょう．まず，Leanの型が空であるかもしれないという事実に対処する必要があります． ``f`` の逆関数を定義するにあたって，ある ``y`` に対して ``f x = y`` を満たすような ``x`` が無い場合， ``α`` 型のデフォルト値を割り当てたいところです．注釈 ``[Inhabited α]`` を ``variable`` として追加することは ``α`` 型がまさにこのような要素を持つことと同義であり，この要素は ``default`` と表記されます．次に， ``f x = y`` を満たすような ``x`` が複数存在する場合，逆関数はそのうちの1つだけを **選択** する必要があります．これには **選択公理** （axiom of choice）の力を借りる必要があります．Leanでは様々な方法で選択公理にアクセスすることができます．1つの便利な方法は，以下に示す古典論理に基づいた  ``choose`` 関数を使用することです．
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α β : Type*} [Inhabited α]

-- EXAMPLES:
#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h
-- QUOTE.

/- OMIT:
Given ``h : ∃ x, P x``, the value of ``Classical.choose h``
is some ``x`` satisfying ``P x``.
The theorem ``Classical.choose_spec h`` says that ``Classical.choose h``
meets this specification.

OMIT. -/
/- TEXT:
``h : ∃ x, P x`` が与えられた時， ``Classical.choose h`` の値は ``P x`` を満たすような ``x`` です．定理 ``Classical.choose_spec h`` は， ``Classical.choose h`` がこの仕様を満たすことを意味しています．

TEXT. -/
/- OMIT:
With these in hand, we can define the inverse function
as follows:
OMIT. -/
/- TEXT:
これらをもとに，以下のように逆関数を定義することができます:
BOTH: -/
-- QUOTE:
noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h
-- QUOTE.

/- OMIT:
The lines ``noncomputable section`` and ``open Classical``
are needed because we are using classical logic in an essential way.
On input ``y``, the function ``inverse f``
returns some value of ``x`` satisfying ``f x = y`` if there is one,
and a default element of ``α`` otherwise.
This is an instance of a *dependent if* construction,
since in the positive case, the value returned,
``Classical.choose h``, depends on the assumption ``h``.
The identity ``dif_pos h`` rewrites ``if h : e then a else b``
to ``a`` given ``h : e``,
and, similarly, ``dif_neg h`` rewrites it to ``b`` given ``h : ¬ e``.
There are also versions ``if_pos`` and ``if_neg`` that works for non-dependent
if constructions and will be used in the next section.
The theorem ``inverse_spec`` says that ``inverse f``
meets the first part of this specification.

OMIT. -/
/- TEXT:
``noncomputable section`` と ``open Classical`` の行は古典論理を本質的な意味で使っているため必要です．入力 ``y`` に対して，関数 ``inverse f`` は ``f x = y`` を満たす ``x`` の値があればそれを返し，なければ ``α`` のデフォルトの要素を返します．これは **依存的なif** （dependent if）による構成の例になっています．というのも条件が真の場合，返される値 ``Classical.choose h`` は仮定 ``h`` に依存するからです．条件式 ``if h : e then a else b`` は，等式 ``dif_pos h`` によって ``h : e`` が与えられると ``a`` に書き換えられ，同様に ``dif_neg h`` によって ``h : ¬ e`` が与えられると ``b`` に書き換えられます．また似たものとして ``if_pos`` と ``if_neg`` というものもあり，これは非依存なifの構成で機能し，これは次節で用いられます．定理 ``inverse_spec`` は ``inverse f`` が if 式の条件を満たすことを述べています．

TEXT. -/
/- OMIT:
Don't worry if you do not fully understand how these work.
The theorem ``inverse_spec`` alone should be enough to show
that ``inverse f`` is a left inverse if and only if ``f`` is injective
and a right inverse if and only if ``f`` is surjective.
Look up the definition of ``LeftInverse`` and ``RightInverse``
by double-clicking or right-clicking on them in VS Code,
or using the commands ``#print LeftInverse`` and ``#print RightInverse``.
Then try to prove the two theorems.
They are tricky!
It helps to do the proofs on paper before
you start hacking through the details.
You should be able to prove each of them with about a half-dozen
short lines.
If you are looking for an extra challenge,
try to condense each proof to a single-line proof term.
OMIT. -/
/- TEXT:
これらがどのようにはたらくか完全に理解できなくても心配しないでください．定理 ``inverse_spec`` 単体で， ``f`` が単射であることと ``inverse f`` が ``f`` の左逆写像であることが同値であること， ``f`` が全射であることと ``inverse f`` が ``f`` の右逆写像であることが同値であることを示すことができます．vscodeで ``LeftInverse`` と ``RightInverse`` の定義をダブルクリックか右クリック，もしくは ``#print LeftInverse`` と ``#print RightInverse`` コマンドを使って調べてみてください．それから以下の2つの定理を証明してください．難しいですよ！細部を試行錯誤する前に，紙の上で証明することをお勧めします．それぞれの証明は6行程度で行えるはずです．更に挑戦したい場合は，それぞれの証明を1行の証明項に凝縮してみましょう．
BOTH: -/
-- QUOTE:
variable (f : α → β)

open Function

-- EXAMPLES:
example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  intro h y
  use inverse f y
  apply h

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h y ↦ inverse_spec _ (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

-- BOTH:
end

-- OMIT:
/-
.. TODO: These comments after this paragraph are from Patrick.
.. We should decide whether we want to do this here.
.. Another possibility is to wait until later.
.. There may be good examples for the topology chapter,
.. at which point, the reader will be more of an expert.

.. This may be a good place to also introduce a discussion of the choose tactic, and explain why you choose (!) not to use it here.

.. Typically, you can include:

.. example {α β : Type*} {f : α → β} : surjective f ↔ ∃ g : β → α, ∀ b, f (g b) = b :=
.. begin
..   split,
..   { intro h,
..     dsimp [surjective] at h, -- this line is optional
..     choose g hg using h,
..     use g,
..     exact hg },
..   { rintro ⟨g, hg⟩,
..     intros b,
..     use g b,
..     exact hg b },
.. end
.. Then contrast this to a situation where we really want a def outputting an element or a function, maybe with a less artificial example than your inverse.

.. We should also tie this to the "function are global" discussion, and the whole thread of deferring proofs to lemmas instead of definitions. There is a lot going on here, and all of it is crucial for formalization.
-/
/- OMIT:
We close this section with a type-theoretic statement of Cantor's
famous theorem that there is no surjective function from a set
to its power set.
See if you can understand the proof,
and then fill in the two lines that are missing.
OMIT. -/
/- TEXT:
本節を終えるにあたって，ある集合からその冪集合への全射が存在しないというカントールの有名な定理を型理論的に述べましょう．証明を理解した上で，欠けている2行を埋めてみてください．
TEXT. -/
-- BOTH:
section
variable {α : Type*}
open Function

-- EXAMPLES:
-- QUOTE:
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction
-- QUOTE.

-- COMMENTS: TODO: improve this
-- SOLUTIONS:
theorem Cantorαα : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- BOTH:
end

/- TEXT:

.. [#f21] 訳注: ガロア接続は半順序集合の間の順序を保つ関数についての性質です
TEXT. -/
