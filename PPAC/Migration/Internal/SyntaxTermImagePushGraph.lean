import PPAC.Migration.Internal.SyntaxTermImagePushExistence

/-! 原Replacement实际构造唯一逐值变换后的完整项像表，保持同一源域。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePushGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxTermImagePushSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_push {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d))
    (hm : Derives Γ (SyntaxIndexMapSyntax.maps w R S c d C D)) : Derives Γ (existsPush w R S c d C D f a) := by
  have ht := SyntaxTermImagePushExistence.total_matrix hZ w R S c d C D f (id : Fin m → Fin m) a hw hf hm
  have he := SyntaxTermImageGraph.exists_image hZ (matrix w R S c d C D f) (id : Fin m → Fin m) w a C D hw
    (.conjL hf) (SyntaxIndexMapSyntax.target_contexts _ _ _ _ _ _ _ hm) ht
    (SyntaxTermImagePushExistence.typed_outputs w R S c d C D f (id : Fin m → Fin m) a)
  let G := (imageMap w.castSucc (Fin.last m) a.castSucc C.castSucc D.castSucc).conj
    (graph w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  have he1 : Derives Γ (.ex G) := of_eq (by simp only [G, matrix_graph, paramsUp, id_eq]) he
  apply Derives.exE (p := G) he1
  have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under hf G)
  have hm1 : Derives Δ (SyntaxIndexMapSyntax.maps w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc) := of_eq (SyntaxIndexMapSyntax.maps_rename w R S c d C D Fin.castSucc) (under hm G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hp : Derives Δ (pushed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc a.castSucc (Fin.last m)) := .conjI hf1 (.conjI hm1 (.conjI (.conjL hG) (.conjR hG)))
  have ho := intro_exists w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc a.castSucc (Fin.last m) hp
  exact of_eq (existsPush_rename w R S c d C D f a Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a g h : Fin m)
    (hg : Derives Γ (pushed w R S c d C D f a g)) (hh : Derives Γ (pushed w R S c d C D f a h)) : Derives Γ (.equal g h) :=
  RelationGraph.unique_graph hZ (matrix w R S c d C D f) (id : Fin m → Fin m) a g h
    (of_eq (matrix_graph w R S c d C D f id a g).symm (.conjR (.conjR (.conjR hg))))
    (of_eq (matrix_graph w R S c d C D f id a h).symm (.conjR (.conjR (.conjR hh))))

theorem guarded_edges {m} {Γ : Context m} (w R S c d C D f a g i q : Fin m)
    (hg : Derives Γ (pushed w R S c d C D f a g)) :
    Derives Γ ((edge g i q).iff ((Formula.mem i a).conj (value w R S c d C D f i q))) := by
  have hl := Derives.conjR (.conjR (.conjR (.conjR hg)))
  exact of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i hl))

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a g i q : Fin m)
    (hg : Derives Γ (pushed w R S c d C D f a g)) : Derives Γ ((edge g i q).iff (value w R S c d C D f i q)) := by
  have he := guarded_edges w R S c d C D f a g i q hg
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let V := value w R S c d C D f i q
    have hV : Derives (Context.add V Γ) V := .hyp (Or.inl rfl)
    have hi := SyntaxTermImagePushPoint.source_member (ZFContext.add hZ V) w R S c d C D f a i q (add (.conjL hg) V) hV
    exact .impE (add (.conjR he) V) (.conjI hi hV)

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S c d C D f a g i t q : Fin m)
    (hg : Derives Γ (pushed w R S c d C D f a g)) (ht : Derives Γ (edge f i t)) :
    Derives Γ ((edge g i q).iff (SyntaxRenameTermSyntax.renamed w R S c d C D t q)) := by
  have he := edge_iff hZ w R S c d C D f a g i q hg
  apply Derives.conjI
  · apply Derives.impI
    let E := edge g i q
    have hv : Derives (Context.add E Γ) (value w R S c d C D f i q) := .impE (add (.conjL he) E) (.hyp (Or.inl rfl))
    let B := (edge f.castSucc i.castSucc (Fin.last m)).conj
      (SyntaxRenameTermSyntax.renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) hv
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) :=
      of_eq (imageMap_rename w f a c d Fin.castSucc) (under (add (.conjL hg) E) B)
    have ht1 : Derives Δ (edge f.castSucc i.castSucc t.castSucc) :=
      of_eq (edge_rename f i t Fin.castSucc) (under (add ht E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have eq := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality
      (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf1) (.conjL hB) ht1
    have ho := SyntaxTermImagePushPoint.renamed_subst_input _ _ _ _ _ _ _ _ _ _ eq (.conjR hB)
    exact of_eq (SyntaxRenameTermSyntax.renamed_rename w R S c d C D t q Fin.castSucc).symm ho
  · apply Derives.impI
    let A := SyntaxRenameTermSyntax.renamed w R S c d C D t q
    exact .impE (add (.conjR he) A) (intro_value w R S c d C D f i q t (add ht A) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.SyntaxTermImagePushGraph
