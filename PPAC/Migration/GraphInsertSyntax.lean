import PPAC.Migration.GraphInsertFunction

/-! 图扩展的完整对象结果，同时记录精确边刻画和完整functionOn。 -/
namespace PPAC.Migration.GraphInsertSyntax
open Source SourceAlgebra PairSyntax GraphSyntax InsertSyntax

def edgeLaw {m} (g f x y : Fin m) : Formula m :=
  .all (.all ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).disj
      ((Formula.equal (Fin.last m).castSucc x.castSucc.castSucc).conj (.equal (Fin.last (m+1)) y.castSucc.castSucc)))))

def witness {m} (g e p f d x y : Fin m) : Formula m :=
  (ordered p x y).conj ((insert e d x).conj ((insert g f p).conj
    ((functionOn g e).conj (edgeLaw g f x y))))

def existsExtension {m} (f d x y : Fin m) : Formula m :=
  .ex (.ex (.ex (witness (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc)))

theorem edgeLaw_rename {m k} (g f x y : Fin m) (r : Fin m → Fin k) :
    (edgeLaw g f x y).rename r = edgeLaw (r g) (r f) (r x) (r y) := by
  simp only [edgeLaw, Formula.iff, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m k} (g e p f d x y : Fin m) (r : Fin m → Fin k) :
    (witness g e p f d x y).rename r = witness (r g) (r e) (r p) (r f) (r d) (r x) (r y) := by
  simp only [witness, Formula.rename, ordered_rename, insert_rename, functionOn_rename, edgeLaw_rename]

theorem existsExtension_rename {m k} (f d x y : Fin m) (r : Fin m → Fin k) :
    (existsExtension f d x y).rename r = existsExtension (r f) (r d) (r x) (r y) := by
  simp only [existsExtension, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_edges {m} {Γ : Context m} (g f p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) : Derives Γ (edgeLaw g f x y) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hg' : Derives Δ (insert g.castSucc.castSucc f.castSucc.castSucc p.castSucc.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hp' : Derives Δ (ordered p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  exact GraphInsertEdges.edge_iff g.castSucc.castSucc f.castSucc.castSucc p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) he' hg' hp'

theorem intro_extension {m} {Γ : Context m} (p e g f d x y : Fin m)
    (hw : Derives Γ (witness g e p f d x y)) : Derives Γ (existsExtension f d x y) := by
  unfold existsExtension
  apply Derives.exI p
  apply Derives.exI e
  apply Derives.exI g
  simpa only [Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw

/-- 同一旧图和输入/输出的扩展见证唯一，供后续对象递归的功能性证明使用。 -/
theorem witness_unique {m} {Γ : Context m} (g e p h c q f d x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (witness g e p f d x y)) (hh : Derives Γ (witness h c q f d x y)) :
    Derives Γ ((Formula.equal p q).conj ((Formula.equal e c).conj (.equal g h))) := by
  have hpq := OrderedPairLogic.unique p q x y he (.conjL hg) (.conjL hh)
  have hec := InsertLogic.unique e c d x he (.conjL (.conjR hg)) (.conjL (.conjR hh))
  have hhfp := InsertLogic.subst_point h f q p (SourceLogic.eq_symm hpq) (.conjL (.conjR (.conjR hh)))
  have hgh := InsertLogic.unique g h f p he (.conjL (.conjR (.conjR hg))) hhfp
  exact .conjI hpq (.conjI hec hgh)
end PPAC.Migration.GraphInsertSyntax
