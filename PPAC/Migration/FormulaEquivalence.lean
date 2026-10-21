import PPAC.Migration.Normalization

/-! 源公式的对象逻辑等价模式；每个实例直接返回原FirstOrder.Derives。 -/
namespace PPAC.Migration.FormulaEquivalence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

/-- 有限模式索引留在外部；每个项环境中的实例均有原核对象证明。 -/
def Equivalent {n} (p q : Source.Formula n) : Prop :=
  ∀ {free : Syntax.Ctx} (ρ : Fin n → Syntax.Tm [] free)
    (T : FirstOrder.Theory ℒ) (Γ : FirstOrder.Context ℒ free),
    FirstOrder.Derives T Γ (.iff (Syntax.formula ρ p) (Syntax.formula ρ q))

namespace Equivalent

theorem refl {n} (p : Source.Formula n) : Equivalent p p := by
  intro free ρ T Γ
  exact Normalization.iff_refl _

theorem symm {n} {p q : Source.Formula n} (h : Equivalent p q) : Equivalent q p := by
  intro free ρ T Γ
  exact Normalization.iff_symm (h ρ T Γ)

theorem trans {n} {p q r : Source.Formula n}
    (hpq : Equivalent p q) (hqr : Equivalent q r) : Equivalent p r := by
  intro free ρ T Γ
  exact Normalization.iff_trans (hpq ρ T Γ) (hqr ρ T Γ)

theorem imp {n} {p p' q q' : Source.Formula n}
    (hp : Equivalent p p') (hq : Equivalent q q') : Equivalent (.imp p q) (.imp p' q') := by
  intro free ρ T Γ
  exact Normalization.imp_congr (hp ρ T Γ) (hq ρ T Γ)

theorem conj {n} {p p' q q' : Source.Formula n}
    (hp : Equivalent p p') (hq : Equivalent q q') : Equivalent (.conj p q) (.conj p' q') := by
  intro free ρ T Γ
  exact Normalization.conj_congr (hp ρ T Γ) (hq ρ T Γ)

theorem all {n} {p q : Source.Formula (n+1)}
    (h : Equivalent p q) : Equivalent (.all p) (.all q) := by
  intro free ρ T Γ
  simpa only [Syntax.forall_fresh] using Normalization.forall_congr
    (h (Syntax.fresh ρ) T (FreshVariable.extendContext SetSort.set Γ))

theorem ex {n} {p q : Source.Formula (n+1)}
    (h : Equivalent p q) : Equivalent (.ex p) (.ex q) := by
  intro free ρ T Γ
  simpa only [Syntax.exists_fresh] using Normalization.exists_congr
    (h (Syntax.fresh ρ) T (FreshVariable.extendContext SetSort.set Γ))

theorem closed {p q : Source.Sentence} (h : Equivalent p q)
    {T : FirstOrder.Theory ℒ} {Γ : FirstOrder.Context ℒ []} :
    FirstOrder.Derives T Γ (.iff (Translation.sentence p) (Translation.sentence q)) := by
  simpa only [Syntax.empty_formula] using h Fin.elim0 T Γ
end Equivalent

theorem conj_comm {n} (p q : Source.Formula n) : Equivalent (.conj p q) (.conj q p) := by
  intro free ρ T Γ
  apply FirstOrder.Derives.iff_intro
  · exact .conj_intro (.conj_elim_right (.assumption List.mem_cons_self))
      (.conj_elim_left (.assumption List.mem_cons_self))
  · exact .conj_intro (.conj_elim_right (.assumption List.mem_cons_self))
      (.conj_elim_left (.assumption List.mem_cons_self))

theorem curry_swap {n} (p q r : Source.Formula n) :
    Equivalent (.imp p (.imp q r)) (.imp q (.imp p r)) := by
  intro free ρ T Γ
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.imp_intro
    exact .imp_elim (.imp_elim
      (.assumption (formula := Syntax.formula ρ (.imp p (.imp q r))) (by simp))
      (.assumption List.mem_cons_self))
      (.assumption (formula := Syntax.formula ρ q) (by simp))
  · apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.imp_intro
    exact .imp_elim (.imp_elim
      (.assumption (formula := Syntax.formula ρ (.imp q (.imp p r))) (by simp))
      (.assumption List.mem_cons_self))
      (.assumption (formula := Syntax.formula ρ p) (by simp))
end PPAC.Migration.FormulaEquivalence
