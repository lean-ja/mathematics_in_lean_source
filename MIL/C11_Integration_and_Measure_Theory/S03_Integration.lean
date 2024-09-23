import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

open Topology Filter ENNReal

open MeasureTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/- OMIT:
Integration
-----------

OMIT. -/
/- TEXT:
.. _integration:

積分
-----------

TEXT. -/
/- OMIT:
Now that we have measurable spaces and measures we can consider integrals.
As explained above, Mathlib uses a very general notion of
integration that allows any Banach space as the target.
As usual, we don't want our notation to
carry around assumptions, so we define integration in such a way
that an integral is equal to zero if the function in question is
not integrable.
Most lemmas having to do with integrals have integrability assumptions.
OMIT. -/
/- TEXT:
可測空間と測度を得たので，積分を考えることができます．上記で説明したように，Mathlibは非常に一般的な積分の概念を使っており，どのようなバナッハ空間でも積分の対象とすることができます．いつものように，仮定をいちいち持ち出す記法は避けたいので，対象の関数が可積分でなければ0に等しくなるように積分を定義します．積分に関連するほとんどの補題は可積分の仮定を持っています．
EXAMPLES: -/
-- QUOTE:
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
-- QUOTE.

/- OMIT:
As an example of the complex interactions between our various conventions, let us see how to integrate constant functions.
Recall that a measure ``μ`` takes values in ``ℝ≥0∞``, the type of extended non-negative reals.
There is a function ``ENNReal.toReal : ℝ≥0∞ → ℝ`` which sends ``⊤``,
the point at infinity, to zero.
For any ``s : Set α``, if ``μ s = ⊤``, then nonzero constant functions are not integrable on ``s``.
In that case, their integrals are equal to zero by definition, as is ``(μ s).toReal``.
So in all cases we have the following lemma.
OMIT. -/
/- TEXT:
これまで見てきた諸々の事実を複雑に組み合わせた例として，定数関数の積分方法を見てみましょう．測度 ``μ`` は非負実数を拡張した型である ``ℝ≥0∞`` の値をとることを思い出してください．関数 ``ENNReal.toReal : ℝ≥0∞ → ℝ`` は無限遠点 ``⊤`` を0に送ります．任意の ``s : Set α`` に対して，もし ``μ s = ⊤`` ならば，非零定数関数は ``s`` 上で積分できません．その場合，積分は定義から ``(μ s).toReal`` となり，0に等しくなります．したがって，すべての場合において次の補題が成り立ちます．
EXAMPLES: -/
-- QUOTE:
example {s : Set α} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c
-- QUOTE.

/- OMIT:
We now quickly explain how to access the most important theorems in integration theory, starting
with the dominated convergence theorem. There are several versions in Mathlib,
and here we only show the most basic one.
OMIT. -/
/- TEXT:
ここでは積分理論の最も重要な定理を導く方法を，優収束定理から手短に説明します．Mathlibにはいくつかバリエーションが存在しますが，ここでは最も基本的なものだけを紹介します．
EXAMPLES: -/
-- QUOTE:
open Filter

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim
-- QUOTE.

/- OMIT:
Then we have Fubini's theorem for integrals on product type.
OMIT. -/
/- TEXT:
これによって直積型の積分に対するフビニの定理が得られます．
EXAMPLES: -/
-- QUOTE:
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
-- QUOTE.

end

/- OMIT:
There is a very general version of convolution that applies to any
continuous bilinear form.
OMIT. -/
/- TEXT:
畳み込みには任意の連続双線形形式に適用できる非常に一般的なバージョンがあります．
EXAMPLES: -/
section

-- QUOTE:
open Convolution

-- EXAMPLES:
variable {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedSpace ℝ F] [CompleteSpace F]
  [Sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) :
    f ⋆[L, μ] g = fun x ↦ ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
-- QUOTE.

end

/- OMIT:
Finally, Mathlib has a very general version of the change-of-variables formula.
In the statement below, ``BorelSpace E`` means the
:math:`\sigma`-algebra on ``E`` is generated by the open sets of ``E``,
and ``IsAddHaarMeasure μ`` means that the measure ``μ`` is left-invariant,
gives finite mass to compact sets, and give positive mass to open sets.
OMIT. -/
/- TEXT:
最後に，Mathlibには非常に一般的な変数変換の公式があります．以下の文において， ``BorelSpace E`` は ``E`` 上の :math:`\sigma`-代数が ``E`` 開集合によって生成されることを意味し， ``IsAddHaarMeasure μ`` は ``μ`` が左不変であり，コンパクト集合に有限の体積量を与え，開集合に正の体積量を与えることを意味します．
EXAMPLES: -/
-- QUOTE:
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {f : E → E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf : ∀ x : E, x ∈ s → HasFDerivWithinAt f (f' x) s x) (h_inj : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
  integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g
-- QUOTE.
