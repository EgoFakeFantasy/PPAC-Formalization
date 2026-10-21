import PPAC.Migration.InsertLogic

/-! 原Pairing/Union内单元素插入集的实际存在构造。 -/
namespace PPAC.Migration.InsertExistence
open Source SourceAlgebra SourceLogic PairSyntax InsertSyntax

theorem exists_insert {m} {Γ : Context m} (a x : Fin m)
    (hpair : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hunion : Derives Γ (Source.SetLanguage.union.rename Fin.elim0)) : Derives Γ (insertExists a x) := by
  have hs := pairing_instance x x hpair
  let S := pair (Fin.last m) x.castSucc x.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have resultS : Derives Γs (insertExists a.castSucc x.castSucc) := by
    have hsS : Derives Γs S := .hyp (Or.inl rfl)
    have hpairS : Derives Γs (Source.SetLanguage.pairing.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hpair S
    have huS : Derives Γs (Source.SetLanguage.union.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hunion S
    have hp := pairing_instance a.castSucc (Fin.last m) hpairS
    let P := pair (Fin.last (m+1)) a.castSucc.castSucc (Fin.last m).castSucc
    let Γp := Context.add P (Context.image Formula.raise Γs)
    change Derives Γs (.ex P) at hp
    apply Derives.exE (p := P) hp
    have resultP : Derives Γp (insertExists a.castSucc.castSucc x.castSucc.castSucc) := by
      have hsP : Derives Γp (pair (Fin.last m).castSucc x.castSucc.castSucc x.castSucc.castSucc) := by
        simpa only [Formula.raise, S, pair_rename] using under hsS P
      have hpP : Derives Γp P := .hyp (Or.inl rfl)
      have huP : Derives Γp (Source.SetLanguage.union.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under huS P
      have hb := union_instance (Fin.last (m+1)) huP
      let B := unionOf (Fin.last (m+2)) (Fin.last (m+1)).castSucc
      let Γb := Context.add B (Context.image Formula.raise Γp)
      change Derives Γp (.ex B) at hb
      apply Derives.exE (p := B) hb
      have resultB : Derives Γb (insertExists a.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
        have hsB : Derives Γb (pair (Fin.last m).castSucc.castSucc
            x.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, pair_rename] using under hsP B
        have hpB : Derives Γb (pair (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := by
          simpa only [Formula.raise, P, pair_rename] using under hpP B
        have huB : Derives Γb B := .hyp (Or.inl rfl)
        have hi := InsertLogic.from_union (Fin.last (m+2)) a.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hsB hpB huB
        apply Derives.exI (Fin.last (m+2))
        simpa only [Formula.instantiate, insert_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
      simpa only [Formula.raise, insertExists_rename] using resultB
    simpa only [Formula.raise, insertExists_rename] using resultP
  simpa only [Formula.raise, insertExists_rename] using resultS
end PPAC.Migration.InsertExistence
