import PPAC.Migration.OrdinalLeastExistence

/-! 全参数最小序数的对象模式：每个公式实例均有完整闭句及原Derives证书。 -/
namespace PPAC.Migration.ObjectOrdinalLeast
open Source SourceAlgebra SourceLogic OrdinalLeastSyntax

def existenceSentence {n} (p : Formula (n+1)) : Source.Sentence :=
  ((has p (id : Fin n → Fin n)).imp (leastExists p id)).close

def uniquenessSentence {n} (p : Formula (n+1)) : Source.Sentence :=
  ((has p (id : Fin n → Fin n)).imp (fiber p id)).close

def equalitySentence {n} (p : Formula (n+1)) : Source.Sentence :=
  ((least p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc).imp
    ((least p (fun i => i.castSucc.castSucc) (Fin.last (n+1))).imp
      (.equal (Fin.last n).castSucc (Fin.last (n+1))))).close

theorem source_existence {n} (p : Formula (n+1)) : Derives (Source.SetLanguage.ZF.at 0) (existenceSentence p) := by
  apply close_derives
  apply Derives.impI
  have he : Derives (Source.SetLanguage.ZF.at n) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  have hf : Derives (Source.SetLanguage.ZF.at n) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  have hs : Derives (Source.SetLanguage.ZF.at n) ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OrdinalDifference.outsideMatrix, rfl⟩
  have hm : Derives (Source.SetLanguage.ZF.at n) ((Source.SetLanguage.separation (matrix p).neg.neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation (matrix p).neg.neg, rfl⟩
  have hc := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover n
  exact OrdinalLeastExistence.exists_least p id (add he _) (add hf _) (add hs _) (add hm _) (add hc _) (.hyp (Or.inl rfl))

theorem source_uniqueness {n} (p : Formula (n+1)) : Derives (Source.SetLanguage.ZF.at 0) (uniquenessSentence p) := by
  apply close_derives
  apply Derives.impI
  let Δ := Context.add (has p (id : Fin n → Fin n)) (Source.SetLanguage.ZF.at n)
  have hc : Derives Δ ((existenceSentence p).rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at (source_existence p) n) _
  have hi := specialize_close ((has p (id : Fin n → Fin n)).imp (leastExists p id)) id hc
  have he : Derives Δ ((has p (id : Fin n → Fin n)).imp (leastExists p id)) := by
    simpa only [Reverse.source_rename_id] using hi
  exact OrdinalLeastLogic.fiber_of_exists p id (.impE he (.hyp (Or.inl rfl)))

theorem source_equality {n} (p : Formula (n+1)) : Derives (Source.SetLanguage.ZF.at 0) (equalitySentence p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalLeastLogic.least_values_equal p (fun i => i.castSucc.castSucc)
    (Fin.last n).castSucc (Fin.last (n+1)) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem existence_kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (existenceSentence p)) := TheoryTransport.sentence (source_existence p)

theorem native_existence {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence p)) :=
  ZFReplay.replay (existence_kernel_certificate p)

theorem uniqueness_kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (uniquenessSentence p)) := TheoryTransport.sentence (source_uniqueness p)

theorem native_uniqueness {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence p)) :=
  ZFReplay.replay (uniqueness_kernel_certificate p)

theorem equality_kernel_certificate {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (equalitySentence p)) := TheoryTransport.sentence (source_equality p)

theorem native_equality {n} (p : Formula (n+1)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (equalitySentence p)) :=
  ZFReplay.replay (equality_kernel_certificate p)
end PPAC.Migration.ObjectOrdinalLeast
