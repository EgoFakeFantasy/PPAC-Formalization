import PPAC.Migration.GraphFamilyFunction

/-! 任意内部相容函数图集合族的实际并图构造与唯一性。 -/
namespace PPAC.Migration.GraphFamilyExistence
open Source SourceAlgebra SourceLogic GraphSyntax InsertSyntax GraphDomainSyntax GraphFamilySyntax

theorem intro_union {m} {Γ : Context m} (g d f : Fin m)
    (hw : Derives Γ (witness g d f)) : Derives Γ (existsUnion f) := by
  unfold existsUnion
  apply Derives.exI g
  apply Derives.exI d
  simpa only [Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw

theorem exists_union {m} {Γ : Context m} (f : Fin m)
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation GraphDomainSyntax.matrix).rename Fin.elim0))
    (hf : Derives Γ (graphs f)) (hc : Derives Γ (compatible f)) : Derives Γ (existsUnion f) := by
  have hG := union_instance f hu
  let G := unionOf (Fin.last m) f.castSucc
  let Γg := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hG
  apply Derives.exE (p := G) hG
  have resultG : Derives Γg (existsUnion f.castSucc) := by
    have huG : Derives Γg G := .hyp (Or.inl rfl)
    have hUnionG : Derives Γg (Source.SetLanguage.union.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hu G
    have hsG : Derives Γg ((Source.SetLanguage.separation GraphDomainSyntax.matrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hs G
    have hfG : Derives Γg (graphs f.castSucc) := by
      simpa only [Formula.raise, graphs_rename] using under hf G
    have hcG : Derives Γg (compatible f.castSucc) := by
      simpa only [Formula.raise, compatible_rename] using under hc G
    have hD := GraphDomainExistence.exists_domain (Fin.last m) hUnionG hsG
    let D := domain (Fin.last (m+1)) (Fin.last m).castSucc
    let Γd := Context.add D (Context.image Formula.raise Γg)
    change Derives Γg (.ex D) at hD
    apply Derives.exE (p := D) hD
    have huD : Derives Γd (unionOf (Fin.last m).castSucc f.castSucc.castSucc) := by
      simpa only [Formula.raise, G, unionOf_rename] using under huG D
    have hfD : Derives Γd (graphs f.castSucc.castSucc) := by
      simpa only [Formula.raise, graphs_rename] using under hfG D
    have hcD : Derives Γd (compatible f.castSucc.castSucc) := by
      simpa only [Formula.raise, compatible_rename] using under hcG D
    have hdD : Derives Γd D := .hyp (Or.inl rfl)
    have hfunc := GraphFamilyFunction.function_on (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc huD hdD hfD hcD
    have hlaw := GraphFamilyEdges.all_edges (Fin.last m).castSucc f.castSucc.castSucc huD
    have hr := intro_union (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc
      (.conjI huD (.conjI hdD (.conjI hfunc hlaw)))
    simpa only [Formula.raise, existsUnion_rename] using hr
  simpa only [Formula.raise, existsUnion_rename] using resultG

theorem witness_unique {m} {Γ : Context m} (g d h e f : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (witness g d f)) (hh : Derives Γ (witness h e f)) :
    Derives Γ ((Formula.equal g h).conj (.equal d e)) := by
  have hgh := GraphDomainAlgebra.union_unique g h f he (.conjL hg) (.conjL hh)
  have hdH := GraphDomainAlgebra.subst_graph d g h hgh (.conjL (.conjR hg))
  exact .conjI hgh (GraphDomainAlgebra.unique d e h he hdH (.conjL (.conjR hh)))
end PPAC.Migration.GraphFamilyExistence
