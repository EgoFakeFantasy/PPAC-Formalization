import PPAC.Migration.ReverseSyntax
import PPAC.Migration.TheoryTransport

/-! 纯句法规范化的理论呈现等价。两个方向均使用原Hilbert核；源自然演绎反向编译另行处理。 -/
namespace PPAC.Migration.Presentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

/-- 将任意原生理论的全部闭公理（含任意模式）回译成源8构造器语法。 -/
def source (T : FirstOrder.Theory ℒ) : Source.Theory :=
  fun q => ∃ p, T p ∧ q = Reverse.sentence p

/-- 回译理论再经正向翻译所得的原核理论。此处不将它认作OpenAI的Replacement版ZF。 -/
def theory (T : FirstOrder.Theory ℒ) : FirstOrder.Theory ℒ :=
  TheoryTransport.theory (source T)

theorem replay_normalized_axiom {T : FirstOrder.Theory ℒ}
    {p : FirstOrder.Sentence ℒ} (hp : theory T p) :
    FirstOrder.Derives T [] p := by
  rcases hp with ⟨q, ⟨r, hr, rfl⟩, rfl⟩
  apply Reverse.normalize_derives
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (free := []) hr)

theorem replay_original_axiom {T : FirstOrder.Theory ℒ}
    {p : FirstOrder.Sentence ℒ} (hp : T p) :
    FirstOrder.Derives (theory T) [] p := by
  apply Reverse.denormalize_derives
  have h : theory T (Translation.sentence (Reverse.sentence p)) :=
    ⟨Reverse.sentence p, ⟨p, hp, rfl⟩, rfl⟩
  simpa [FirstOrder.Formula.fromSentence, Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (free := []) h)

/-- 任意自由上下文、任意局部假设和任意结论；由实际原核theory_cut回放。 -/
theorem derives_iff {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives (theory T) Γ p ↔ FirstOrder.Derives T Γ p :=
  ⟨FirstOrder.Derives.theory_cut (fun hp => replay_normalized_axiom hp),
   FirstOrder.Derives.theory_cut (fun hp => replay_original_axiom hp)⟩

/-- 外部一致性等价仅是呈现变换的推论，不是内部Con蕴含主定理。 -/
theorem consistent_iff (T : FirstOrder.Theory ℒ) :
    FirstOrder.Derives.Consistent (theory T) ([] : FirstOrder.Context ℒ []) ↔
      FirstOrder.Derives.Consistent T ([] : FirstOrder.Context ℒ []) := by
  constructor
  · intro h d
    exact h (derives_iff.mpr d)
  · intro h d
    exact h (derives_iff.mp d)
end PPAC.Migration.Presentation
