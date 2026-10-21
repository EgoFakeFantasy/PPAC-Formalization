import PPAC.Migration.GraphInsertSyntax

/-! 原Pairing/Union/Extensionality内实际构造新点图扩展。 -/
namespace PPAC.Migration.GraphInsertExistence
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax InsertSyntax GraphInsertSyntax

theorem exists_extension {m} {Γ : Context m} (f d x y : Fin m)
    (hpair : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hunion : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hext : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hn : Derives Γ (Formula.mem x d).neg) :
    Derives Γ (existsExtension f d x y) := by
  have hp := OrderedPairExistence.exists_pair x y hpair
  let P := ordered (Fin.last m) x.castSucc y.castSucc
  let Γp := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have resultP : Derives Γp (existsExtension f.castSucc d.castSucc x.castSucc y.castSucc) := by
    have hpP : Derives Γp P := .hyp (Or.inl rfl)
    have hpairP : Derives Γp (Source.SetLanguage.pairing.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hpair P
    have hunionP : Derives Γp (Source.SetLanguage.union.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hunion P
    have hextP : Derives Γp (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hext P
    have hfP : Derives Γp (functionOn f.castSucc d.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using under hf P
    have hnP : Derives Γp (Formula.mem x.castSucc d.castSucc).neg := under hn P
    have he := InsertExistence.exists_insert d.castSucc x.castSucc hpairP hunionP
    let E := insert (Fin.last (m+1)) d.castSucc.castSucc x.castSucc.castSucc
    let Γe := Context.add E (Context.image Formula.raise Γp)
    change Derives Γp (.ex E) at he
    apply Derives.exE (p := E) he
    have resultE : Derives Γe (existsExtension f.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
      have hpE : Derives Γe (ordered (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
        simpa only [Formula.raise, P, ordered_rename] using under hpP E
      have hdE : Derives Γe E := .hyp (Or.inl rfl)
      have hpairE : Derives Γe (Source.SetLanguage.pairing.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hpairP E
      have hunionE : Derives Γe (Source.SetLanguage.union.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hunionP E
      have hextE : Derives Γe (Source.SetLanguage.extensionality.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hextP E
      have hfE : Derives Γe (functionOn f.castSucc.castSucc d.castSucc.castSucc) := by
        simpa only [Formula.raise, functionOn_rename] using under hfP E
      have hnE : Derives Γe (Formula.mem x.castSucc.castSucc d.castSucc.castSucc).neg := under hnP E
      have hg := InsertExistence.exists_insert f.castSucc.castSucc (Fin.last m).castSucc hpairE hunionE
      let G := insert (Fin.last (m+2)) f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      let Γg := Context.add G (Context.image Formula.raise Γe)
      change Derives Γe (.ex G) at hg
      apply Derives.exE (p := G) hg
      have resultG : Derives Γg (existsExtension f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc
          x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
        have hpG : Derives Γg (ordered (Fin.last m).castSucc.castSucc
            x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, ordered_rename] using under hpE G
        have hdG : Derives Γg (insert (Fin.last (m+1)).castSucc
            d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, E, insert_rename] using under hdE G
        have hgG : Derives Γg G := .hyp (Or.inl rfl)
        have hextG : Derives Γg (Source.SetLanguage.extensionality.rename Fin.elim0) := by
          simpa only [Formula.raise, closed_rename] using under hextE G
        have hfG : Derives Γg (functionOn f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, functionOn_rename] using under hfE G
        have hnG : Derives Γg (Formula.mem x.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc).neg := under hnE G
        have hfunc := GraphInsertFunction.function_insert (Fin.last (m+2)) (Fin.last (m+1)).castSucc
          f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
          x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc hextG hfG hnG hgG hdG hpG
        have hlaw := all_edges (Fin.last (m+2)) f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
          x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc hextG hgG hpG
        exact intro_extension (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
          f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc
          (.conjI hpG (.conjI hdG (.conjI hgG (.conjI hfunc hlaw))))
      simpa only [Formula.raise, existsExtension_rename] using resultG
    simpa only [Formula.raise, existsExtension_rename] using resultE
  simpa only [Formula.raise, existsExtension_rename] using resultP
end PPAC.Migration.GraphInsertExistence
