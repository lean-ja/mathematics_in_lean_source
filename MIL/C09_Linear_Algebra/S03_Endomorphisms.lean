-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


/- OMIT:

Endomorphisms
--------------

OMIT. -/
/- TEXT:
自己準同型
--------------

TEXT. -/
/- OMIT:
An important special case of linear maps are endomorphisms: linear maps from a vector space to itself.
They are interesting because they form a ``K``-algebra. In particular we can evaluate polynomials
with coefficients in ``K`` on them, and they can have eigenvalues and eigenvectors.

OMIT. -/
/- TEXT:
線形写像の重要な特殊ケースは自己準同型です：これはあるベクトル空間からそれ自体への線形写像です．これらは ``K`` 代数を形成するため興味深いものです．特に， ``K`` に係数を持つ多項式を評価することができ，固有値と固有ベクトルを持つことができます．

TEXT. -/
/- OMIT:
Mathlib uses the abbreviation ``Module.End K V := V →ₗ[K] V`` which is convenient when
using a lot of these (especially after opening the ``Module`` namespace).

OMIT. -/
/- TEXT:
Mathlibでは ``Module.End K V := V →ₗ[K] V`` という略語を使いますが，これは（特に ``Module`` 名前空間を開いた後に）自己準同型をたくさん使う場合に便利です．
EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- OMIT: evaluating `P` on `φ`
-- `φ` にて `P` を評価する
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- OMIT: evaluating `X` on `φ` gives back `φ`
-- `φ` にて `X` を評価すると `φ` が戻ってくる
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ


-- QUOTE.
/- OMIT:
As an exercise manipulating endomorphisms, subspaces and polynomials, let us prove the
(binary) kernels lemma: for any endomorphism :math:`φ` and any two relatively
prime polynomials :math:`P` and :math:`Q`, we have :math:`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)`.

OMIT. -/
/- TEXT:
自己準同型と部分空間，多項式を操作する練習として，（二項）核の補題を証明しましょう：任意の自己準同型 :math:`φ` と2つの互いに素な多項式 :math:`P` と :math:`Q` に対して， :math:`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)` が成り立ちます．

TEXT. -/
/- OMIT:
Note that ``IsCoprime x y`` is defined as ``∃ a b, a * x + b * y = 1``.
OMIT. -/
/- TEXT:
``IsCoprime x y`` は ``∃ a b, a * x + b * y = 1`` と定義されていることに注意してください．
EXAMPLES: -/
-- QUOTE:

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simpa [hx]
-- BOTH:

#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- or alternative below:
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- or alternative as above
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]

-- QUOTE.
/- OMIT:
We now move to the discussions of eigenspaces and eigenvalues. By the definition, the eigenspace
associated to an endomorphism :math:`φ` and a scalar :math:`a` is the kernel of :math:`φ - aId`.
The first thing to understand is how to spell :math:`aId`. We could use
``a • LinearMap.id``, but Mathlib uses `algebraMap K (End K V) a` which directly plays nicely
with the ``K``-algebra structure.

OMIT. -/
/- TEXT:
ここで固有空間と固有値の議論に移ります．定義によれば，自己準同型 :math:`φ` とスカラー :math:`a` の固有空間は :math:`φ - aId` の核です．まず理解しなければならないのは， :math:`aId` の書き方です． ``a • LinearMap.id`` を使うこともできますが，Mathlibでは `algebraMap K (End K V) a` を使っており，これは ``K`` 代数構造と直接うまく動きます．
EXAMPLES: -/
-- QUOTE:
example (a : K) : algebraMap K (End K V) a = a • LinearMap.id := rfl

-- QUOTE.
/- OMIT:
Then the next thing to note is that eigenspaces are defined for all values of ``a``, although
they are interesting only when they are non-zero.
However an eigenvector is, by definition, a non-zero element of an eigenspace. The corresponding
predicate is ``End.HasEigenvector``.
OMIT. -/
/- TEXT:
次に注意しなければならないのは，固有空間はすべての ``a`` の値に対して定義されますが，それが0ではない場合にのみ興味があるということです．しかし，固有ベクトルは定義上，固有空間の非0要素です．対応する述語は ``End.HasEigenvector`` です．
EXAMPLES: -/
-- QUOTE:
example (φ : End K V) (a : K) :
    φ.eigenspace a = LinearMap.ker (φ - algebraMap K (End K V) a) :=
  rfl


-- QUOTE.
/- OMIT:
Then there is a predicate ``End.HasEigenvalue`` and the corresponding subtype ``End.Eigenvalues``.
OMIT. -/
/- TEXT:
そして述語 ``End.HasEigenvalue`` とこれに対応する部分型 ``End.Eigenvalues`` が存在します．
EXAMPLES: -/
-- QUOTE:

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- OMIT: Eigenvalue are roots of the minimal polynomial
-- 固有値は最小多項式の平方根
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- OMIT: In finite dimension, the converse is also true (we will discuss dimension below)
-- 有限次元では，その逆もまた真である（次元については以下で議論します）
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- OMIT: Cayley-Hamilton
-- ケーリーハミルトン
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly

-- QUOTE.
