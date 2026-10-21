import PPAC.Migration.SingletonGraphLogic

/-! 在对象层构造单点域及单点函数图，存在见证均由原exI/exE处理。 -/
namespace PPAC.Migration.SingletonMap
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic

def witness {m} (f d p x y : Fin m) : Formula m :=
  (pair d x x).conj ((pair f p p).conj ((ordered p x y).conj (functionOn f d)))

def existsMap {m} (x y : Fin m) : Formula m :=
  .ex (.ex (.ex (witness (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    (Fin.last (m+2)) x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc)))

theorem witness_rename {m k} (f d p x y : Fin m) (r : Fin m → Fin k) :
    (witness f d p x y).rename r = witness (r f) (r d) (r p) (r x) (r y) := by
  simp only [witness, Formula.rename, pair_rename, ordered_rename, functionOn_rename]

theorem existsMap_rename {m k} (x y : Fin m) (r : Fin m → Fin k) :
    (existsMap x y).rename r = existsMap (r x) (r y) := by
  simp only [existsMap, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_map {m} {Γ : Context m} (d f p x y : Fin m)
    (hw : Derives Γ (witness f d p x y)) : Derives Γ (existsMap x y) := by
  unfold existsMap
  apply Derives.exI d
  apply Derives.exI f
  apply Derives.exI p
  simpa only [Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw

theorem exists_map {m} {Γ : Context m} (x y : Fin m)
    (hpair : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hext : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) :
    Derives Γ (existsMap x y) := by
  have hp := OrderedPairExistence.exists_pair x y hpair
  let P := ordered (Fin.last m) x.castSucc y.castSucc
  let Γp := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have resultP : Derives Γp (existsMap x.castSucc y.castSucc) := by
    have hpP : Derives Γp P := .hyp (Or.inl rfl)
    have hpairP : Derives Γp (Source.SetLanguage.pairing.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hpair P
    have hextP : Derives Γp (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hext P
    have hd := pairing_instance x.castSucc x.castSucc hpairP
    let D := pair (Fin.last (m+1)) x.castSucc.castSucc x.castSucc.castSucc
    let Γd := Context.add D (Context.image Formula.raise Γp)
    change Derives Γp (.ex D) at hd
    apply Derives.exE (p := D) hd
    have resultD : Derives Γd (existsMap x.castSucc.castSucc y.castSucc.castSucc) := by
      have hpD : Derives Γd (ordered (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
        simpa only [Formula.raise, P, ordered_rename] using under hpP D
      have hdD : Derives Γd D := .hyp (Or.inl rfl)
      have hpairD : Derives Γd (Source.SetLanguage.pairing.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hpairP D
      have hextD : Derives Γd (Source.SetLanguage.extensionality.rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hextP D
      have hf := pairing_instance (Fin.last m).castSucc (Fin.last m).castSucc hpairD
      let F := pair (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last m).castSucc.castSucc
      let Γf := Context.add F (Context.image Formula.raise Γd)
      change Derives Γd (.ex F) at hf
      apply Derives.exE (p := F) hf
      have resultF : Derives Γf (existsMap x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
        have hpF : Derives Γf (ordered (Fin.last m).castSucc.castSucc
            x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, ordered_rename] using under hpD F
        have hdF : Derives Γf (pair (Fin.last (m+1)).castSucc
            x.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, D, pair_rename] using under hdD F
        have hfF : Derives Γf F := .hyp (Or.inl rfl)
        have hextF : Derives Γf (Source.SetLanguage.extensionality.rename Fin.elim0) := by
          simpa only [Formula.raise, closed_rename] using under hextD F
        have hfunc := SingletonGraphLogic.function_on_singleton (Fin.last (m+2)) (Fin.last m).castSucc.castSucc
          (Fin.last (m+1)).castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc hextF hfF hpF hdF
        exact intro_map (Fin.last (m+1)).castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc
          x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc (.conjI hdF (.conjI hfF (.conjI hpF hfunc)))
      simpa only [Formula.raise, existsMap_rename] using resultF
    simpa only [Formula.raise, existsMap_rename] using resultD
  simpa only [Formula.raise, existsMap_rename] using resultP
end PPAC.Migration.SingletonMap
