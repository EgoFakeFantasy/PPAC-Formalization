import PPAC.Migration.UnorderedPairLogic

/-! 三次对象配对构造原Kuratowski有序对；没有宿主配对函数。 -/
namespace PPAC.Migration.OrderedPairExistence
open Source SourceLogic SourceAlgebra PairSyntax

theorem intro_pair {m} {Γ : Context m} (p x y s t : Fin m)
    (hs : Derives Γ (pair s x x)) (ht : Derives Γ (pair t x y)) (hp : Derives Γ (pair p s t)) :
    Derives Γ (ordered p x y) := by
  unfold ordered
  apply Derives.exI s
  apply Derives.exI t
  simpa only [Formula.instantiate, Formula.rename, pair_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs (Derives.conjI ht hp)

theorem exists_pair {m} {Γ : Context m} (x y : Fin m)
    (hpair : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0)) :
    Derives Γ (orderedExists x y) := by
  have heS := pairing_instance x x hpair
  let S := pair (Fin.last m) x.castSucc x.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at heS
  apply Derives.exE (p := S) heS
  have resultS : Derives Γs (orderedExists x.castSucc y.castSucc) := by
    have hs : Derives Γs S := .hyp (Or.inl rfl)
    have hpairS : Derives Γs (Source.SetLanguage.pairing.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hpair S
    have heT := pairing_instance x.castSucc y.castSucc hpairS
    let T := pair (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc
    let Γt := Context.add T (Context.image Formula.raise Γs)
    change Derives Γs (.ex T) at heT
    apply Derives.exE (p := T) heT
    have resultT : Derives Γt (orderedExists x.castSucc.castSucc y.castSucc.castSucc) := by
      have hsT : Derives Γt (pair (Fin.last m).castSucc x.castSucc.castSucc x.castSucc.castSucc) := by
        simpa only [Formula.raise, S, pair_rename] using under hs T
      have ht : Derives Γt T := .hyp (Or.inl rfl)
      have hpairT : Derives Γt (Source.SetLanguage.pairing.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hpairS T
      have heP := pairing_instance (Fin.last m).castSucc (Fin.last (m+1)) hpairT
      let P := pair (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
      let Γp := Context.add P (Context.image Formula.raise Γt)
      change Derives Γt (.ex P) at heP
      apply Derives.exE (p := P) heP
      have resultP : Derives Γp (orderedExists x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
        have hsP : Derives Γp (pair (Fin.last m).castSucc.castSucc
            x.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, pair_rename] using under hsT P
        have htP : Derives Γp (pair (Fin.last (m+1)).castSucc
            x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, T, pair_rename] using under ht P
        have hp : Derives Γp P := .hyp (Or.inl rfl)
        have ho := intro_pair (Fin.last (m+2)) x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hsP htP hp
        apply Derives.exI (Fin.last (m+2))
        simpa only [Formula.instantiate, ordered_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
      simpa only [Formula.raise, orderedExists_rename] using resultP
    simpa only [Formula.raise, orderedExists_rename] using resultT
  simpa only [Formula.raise, orderedExists_rename] using resultS
end PPAC.Migration.OrderedPairExistence
