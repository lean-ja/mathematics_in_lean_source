import MIL.Common
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

/- OMIT:
Differential Calculus in Normed Spaces
--------------------------------------

OMIT. -/
/- TEXT:
.. index:: normed space

.. _normed_spaces:

ノルム空間の微分法
--------------------------------------

TEXT. -/
/- OMIT:
Normed spaces
^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
ノルム空間
^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Differentiation can be generalized beyond ``ℝ`` using the notion of a
*normed vector space*, which encapsulates both direction and distance.
We start with the notion of a *normed group*, which is an additive commutative
group equipped with a real-valued norm function
satisfying the following conditions.
OMIT. -/
/- TEXT:
微分は，方向と距離の両方を備えた **ノルム線形空間** （normed vector space）の概念を用いることで ``ℝ`` を超えて一般化することができます．まず **ノルム化された群** （normed group）の概念から始めましょう．これは以下の条件を満たす実数値ノルム関数を備えた加法可換群です．
EXAMPLES: -/
section

-- QUOTE:
variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- QUOTE.

/- OMIT:
Every normed space is a metric space with distance function
:math:`d(x, y) = \| x - y \|`, and hence it is also a topological space.
Lean and Mathlib know this.
OMIT. -/
/- TEXT:
すべてのノルム空間は距離関数 :math:`d(x, y) = \| x - y \|` を持つ距離空間であり，したがって位相空間でもあります．LeanとMathlibはこの事実を知っています．
EXAMPLES: -/
-- QUOTE:
example : MetricSpace E := by infer_instance

example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ :=
  hf.norm
-- QUOTE.

/- OMIT:
In order to use the notion of a norm with concepts from linear algebra,
we add the assumption ``NormedSpace ℝ E`` on top of ``NormedAddGroup E``.
This stipulates that ``E`` is a vector space over ``ℝ`` and that
scalar multiplication satisfies the following condition.
OMIT. -/
/- TEXT:
線形代数からのコンセプトとノルムの概念を使うために， ``NormedAddGroup E`` の上に ``NormedSpace ℝ E`` という仮定を追加します．これは ``E`` が ``ℝ`` 上のベクトル空間であり，スカラー倍が以下の条件を満たすことを定めます．
EXAMPLES: -/
-- QUOTE:
variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x
-- QUOTE.

/- OMIT:
A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete.
OMIT. -/
/- TEXT:
完備なノルム空間は **バナッハ空間** （Banach space）として知られています．すべての有限次元ベクトル空間は完備です．
EXAMPLES: -/
-- QUOTE:
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance
-- QUOTE.

/- OMIT:
In all the previous examples, we used the real numbers as the base field.
More generally, we can make sense of calculus with a vector space over any
*nontrivially normed field*. These are fields that are equipped with a
real-valued norm that is multiplicative and has the property that
not every element has norm zero or one
(equivalently, there is an element whose norm is bigger than one).
OMIT. -/
/- TEXT:
これまでの例はすべてベースの体として実数を使いました．より一般的には，任意の **非自明なノルム化された体** （nontrivially normed field）上のベクトル空間を使って微積分を理解することができます．これは乗法的ですべての要素のノルムが0か1ではない（つまり，ノルムが1より大きい要素が存在する）という性質を持つ実数値ノルムを備えた体です．
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜
-- QUOTE.

/- OMIT:
A finite-dimensional vector space over a nontrivially normed field is
complete as long as the field itself is complete.
OMIT. -/
/- TEXT:
非自明なノルム化された体上の有限次元ベクトル空間はその体自体が完備である場合に限り完備です．
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E
-- QUOTE.

end

/- OMIT:
Continuous linear maps
^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
連続線形写像
^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We now turn to the morphisms in the category of normed spaces, namely,
continuous linear maps.
In Mathlib, the type of ``𝕜``-linear continuous maps between normed spaces
``E`` and ``F`` is written ``E →L[𝕜] F``.
They are implemented as *bundled maps*, which means that an element of this type
a structure that that includes the function itself and the properties
of being linear and continuous.
Lean will insert a coercion so that a continuous linear map can be treated
as a function.
OMIT. -/
/- TEXT:
次にノルム空間の圏における射，つまり連続線形写像について説明します．Mathlibでは，ノルム空間 ``E`` と ``F`` の間の ``𝕜`` 線形連続写像の型を ``E →L[𝕜] F`` と表記します．これらは **束縛写像** （bundled maps）として実装されます．束縛写像とは，この型の要素が関数そのものと線形で連続であるという性質を含む構造を持つことを意味します．Leanは連続線形写像を関数として扱えるように型強制を備えています．
EXAMPLES: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f :=
  f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x
-- QUOTE.

/- OMIT:
Continuous linear maps have an operator norm that is characterized by the
following properties.
OMIT. -/
/- TEXT:
連続線形写像は以下の性質で特徴づけられる作用素ノルムを持ちます．
EXAMPLES: -/
-- QUOTE:
variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hMp hM
-- QUOTE.

end

/- OMIT:
There is also a notion of bundled continuous linear *isomorphism*.
Their type of such isomorphisms is ``E ≃L[𝕜] F``.

OMIT. -/
/- TEXT:
また束縛された連続線形 **同型** （isomorphism）という概念が存在します．この型は ``E ≃L[𝕜] F`` です．

TEXT. -/
/- OMIT:
As a challenging exercise, you can prove the Banach-Steinhaus theorem, also
known as the Uniform Boundedness Principle.
The principle states that a family of continuous linear maps from a Banach space
into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded.
The main ingredient is Baire's theorem
``nonempty_interior_of_iUnion_of_closed``. (You proved a version of this in the topology chapter.)
Minor ingredients include ``continuous_linear_map.opNorm_le_of_shell``,
``interior_subset`` and ``interior_iInter_subset`` and ``isClosed_le``.
OMIT. -/
/- TEXT:
発展的な演習として，一様有界性原理としても知られているバナッハ-シュタインハウスの定理を証明してみましょう．この原理はバナッハ空間からノルム空間への連続線形写像の族が点ごとに有界であれば，これらの線形写像のノルムは一様に有界であることを述べています．この証明の主成分はベールの定理 ``nonempty_interior_of_iUnion_of_closed`` です．（位相の章でこれを証明しました．）それ以外の材料として ``continuous_linear_map.opNorm_le_of_shell`` と ``interior_subset`` ， ``interior_iInter_subset`` ， ``isClosed_le`` が含まれます．
BOTH: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

-- EXAMPLES:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n) := fun i ↦
    isClosed_iInter fun i ↦ isClosed_le (g i).cont.norm continuous_const
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    rcases h x with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨e m, mem_range_self m, mem_iInter.mpr fun i ↦ le_trans (hC i) hm⟩
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := NormedField.exists_one_lt_norm 𝕜
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    intro z hz i
    replace hz := mem_iInter.mp (interior_iInter_subset _ (hε hz)) i
    apply interior_subset hz
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk)
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) εk_pos.le
  intro y le_y y_lt
  calc
    ‖g i y‖ = ‖g i (y + x) - g i x‖ := by rw [(g i).map_add, add_sub_cancel_right]
    _ ≤ ‖g i (y + x)‖ + ‖g i x‖ := (norm_sub_le _ _)
    _ ≤ m + m :=
      (add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
        (real_norm_le x (mem_ball_self ε_pos) i))
    _ = (m + m : ℕ) := by norm_cast
    _ ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖)) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos ε_pos (zero_lt_one.trans hk)).2 le_y))
    _ = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ := (mul_comm_div _ _ _).symm


-- BOTH:
end

/- OMIT:
Asymptotic comparisons
^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
漸近比較
^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Defining differentiability also requires asymptotic comparisons.
Mathlib has an extensive library covering the big O and little o relations,
whose definitions are shown below.
Opening the ``asymptotics`` locale allows us to use the corresponding
notation.
Here we will only use little o to define differentiability.
OMIT. -/
/- TEXT:
微分可能性の定義には漸近比較も必要です．Mathlibにはビッグオーとリトルオーの関係をカバーする広範なライブラリがあり，その定義を以下に示されるものです． ``asymptotics`` 名前空間を開くと，対応する表記法を使うことができます．ここでは微分可能性を定義するためにリトルオーのみを使用します．
EXAMPLES: -/
-- QUOTE:
open Asymptotics

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl
-- QUOTE.

/- OMIT:
Differentiability
^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
微分可能性
^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We are now ready to discuss differentiable functions between normed spaces.
In analogy the elementary one-dimensional,
Mathlib defines a predicate ``HasFDerivAt`` and a function ``fderiv``.
Here the letter
"f" stands for *Fréchet*.
OMIT. -/
/- TEXT:
これでノルム空間のあいだの微分可能な関数について議論する準備が整いました．初等的な一次元の場合になぞらえて，Mathlibでは ``HasFDerivAt`` という述語と ``fderiv`` という関数と定義しています．ここで ``f`` は **フレシェ** （Fréchet）を表します．
EXAMPLES: -/
section

-- QUOTE:
open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
  hasFDerivAtFilter_iff_isLittleO ..

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv
-- QUOTE.

/- OMIT:
We also have iterated derivatives that take values in the type of multilinear maps
``E [×n]→L[𝕜] F``,
and we have continuously differential functions.
The type ``WithTop ℕ`` is ``ℕ`` with an additional element ``⊤`` that
is bigger than every natural number.
So :math:`\mathcal{C}^\infty` functions are functions ``f`` that satisfy
``ContDiff 𝕜 ⊤ f``.
OMIT. -/
/- TEXT:
またMathlibには，多重線形写像 ``E [×n]→L[𝕜] F`` 型で値をとる反復微分や，連続微分関数も存在します．型 ``WithTop ℕ`` は ``ℕ`` にすべての自然数より大きい要素 ``⊤`` を加えたものです．つまり関数 :math:`\mathcal{C}^\infty` は ``ContDiff 𝕜 ⊤ f`` を満たす関数 ``f`` です．
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f

example (n : WithTop ℕ) {f : E → F} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m f x :=
  contDiff_iff_continuous_differentiable
-- QUOTE.

/- OMIT:
There is a stricter notion of differentiability called
``HasStrictFDerivAt``, which is used in the statement
of the inverse function theorem and the statement of the implicit function
theorem, both of which are in Mathlib.
Over ``ℝ`` or ``ℂ``, continuously differentiable
functions are strictly differentiable.
OMIT. -/
/- TEXT:
より狭義な微分可能性の概念で ``HasStrictFDerivAt`` と呼ばれるものがあります．これはMathlibにある逆関数定理と陰関数定理の記述で使われています． ``ℝ`` もしくは ``ℂ`` 上の連続微分可能な関数は狭義微分可能です．
EXAMPLES: -/
-- QUOTE:
example {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ}
    (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt hn
-- QUOTE.

/- OMIT:
The local inverse theorem is stated using an operation that produces an
inverse function from a
function and the assumptions that the function is strictly differentiable at a
point ``a`` and that its derivative is an isomorphism.

OMIT. -/
/- TEXT:
局所的な逆関数定理は，ある関数から逆関数を生成する操作と，その関数がある点 ``a`` において狭義微分可能であり，その導関数と同型であるという仮定を用いて述べられます．

TEXT. -/
/- OMIT:
The first example below gets this local inverse.
The next one states that it is indeed a local inverse
from the left and from the right, and that it is strictly differentiable.
OMIT. -/
/- TEXT:
以下の最初の例は，この局所的な逆関数を求めるためのものです．その次の例はこれが左右どちらからも局所的な逆であることを確かめ，そして狭義微分可能であることを述べています．
EXAMPLES: -/
-- QUOTE:
section LocalInverse
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  HasStrictFDerivAt.localInverse f f' a hf

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse

example {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFDerivAt.to_localInverse hf

end LocalInverse
-- QUOTE.

/- OMIT:
This has been only a quick tour of the differential calculus in Mathlib.
The library contains many variations that we have not discussed.
For example, you may want to use one-sided derivatives in the
one-dimensional setting. The means to do so are found in Mathlib in a more
general context;
see ``HasFDerivWithinAt`` or the even more general ``HasFDerivAtFilter``.
OMIT. -/
/- TEXT:
以上，Mathlibの微分をざっと見てきました．Mathlibにはこれまでに説明しなかった多くの情報が含まれています．例えば，1次元の設定での片側微分を使いたいとしましょう．これについてMathlibにはより一般的な文脈のものがあります; ``HasFDerivWithinAt`` や，さらに一般的な ``HasFDerivAtFilter`` を参照してください．
EXAMPLES: -/
#check HasFDerivWithinAt

#check HasFDerivAtFilter

end
