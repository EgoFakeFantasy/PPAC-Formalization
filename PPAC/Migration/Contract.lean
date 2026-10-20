import PPAC.Migration.Translation
import YesMetaZFC.SetTheory.Axioms.ZF
import YesMetaZFC.SetTheory.Definitional.Project.Derivation
import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional

/-! 目标理论公理接入只检查原核连线，不证明其一致，也不证明 ZF 可推出 PP。 -/
namespace PPAC.Migration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory

def PP : FirstOrder.Sentence ℒ := Translation.sentence Source.SetLanguage.PP
def AC : FirstOrder.Sentence ℒ := Translation.sentence Source.SetLanguage.AC
def ACwo : FirstOrder.Sentence ℒ := Translation.sentence Source.SetLanguage.ACwo
/-- 源否定是蕴含假式；保留其精确翻译。 -/
def notAC : FirstOrder.Sentence ℒ := Translation.sentence Source.SetLanguage.AC.neg

/-- 原生 ZF 的纯成员语言像；全 Collection，不加入 Choice。 -/
def nativeZF : FirstOrder.Theory ℒ :=
  Definitional.Project.fo_theory SetTheory.ZF

def targetTheory : FirstOrder.Theory ℒ :=
  fun p => nativeZF p ∨ p = PP ∨ p = ACwo ∨ p = notAC

def Consistent (T : FirstOrder.Theory ℒ) : Prop :=
  FirstOrder.Derives.Consistent T ([] : FirstOrder.Context ℒ [])

/-- 待证明的目标类型；此定义不提供该命题的证明。 -/
def RelativeConsistencyGoal : Prop := Consistent nativeZF → Consistent targetTheory

theorem target_extends_ZF (p : FirstOrder.Sentence ℒ) (h : nativeZF p) :
    targetTheory p := Or.inl h

theorem target_derives_PP : FirstOrder.Derives targetTheory [] PP := by
  simpa [FirstOrder.Formula.fromSentence, FirstOrder.Renaming.emptyFree] using (FirstOrder.Derives.theory_axiom
    (T := targetTheory) (Γ := []) (free := []) (sentence := PP) (Or.inr (Or.inl rfl)))

theorem target_derives_ACwo : FirstOrder.Derives targetTheory [] ACwo := by
  simpa [FirstOrder.Formula.fromSentence, FirstOrder.Renaming.emptyFree] using (FirstOrder.Derives.theory_axiom
    (T := targetTheory) (Γ := []) (free := []) (sentence := ACwo) (Or.inr (Or.inr (Or.inl rfl))))

theorem target_derives_source_notAC :
    FirstOrder.Derives targetTheory [] notAC := by
  simpa [FirstOrder.Formula.fromSentence, FirstOrder.Renaming.emptyFree] using
    (FirstOrder.Derives.theory_axiom (T := targetTheory) (Γ := []) (free := [])
      (sentence := notAC) (Or.inr (Or.inr (Or.inr rfl))))

theorem target_derives_notAC : FirstOrder.Derives targetTheory [] (.neg AC) :=
  FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.logical_axiom (.negation_intro AC))
    target_derives_source_notAC

/-- 无条件的一致性反向基线；另一方向仍待完成。 -/
theorem consistent_ZF_of_target (h : Consistent targetTheory) : Consistent nativeZF :=
  h.theory_mono (fun {p} hp => target_extends_ZF p hp)

theorem no_AC_of_target_consistent (h : Consistent targetTheory) :
    ¬ FirstOrder.Derives targetTheory [] AC := by
  intro hAC
  exact h (FirstOrder.Derives.neg_elim hAC target_derives_notAC)
end PPAC.Migration
