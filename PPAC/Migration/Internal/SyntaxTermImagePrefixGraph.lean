import PPAC.Migration.Internal.SyntaxTermImagePrefixTotal

/-! 原Replacement实际构造唯一完整头槽扩展表，准确匹配全部候选、零位与旧后继位。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (imageMap w f a c d))
    (hz : Derives Γ (SyntaxTermSyntax.term w c d z)) (hA : Derives Γ (successor A a)) :
    Derives Γ (existsPrefix w f a c d z A) := by
  have ht := SyntaxTermImagePrefixTotal.total hZ f a z (id : Fin m → Fin m) w c d A hw hf hA
  have hANat := OmegaStructureAlgebra.successor_member w A a (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hf) hA
  have he := SyntaxTermImageGraph.exists_image hZ (matrix f a z) (id : Fin m → Fin m) w A c d hw hANat
    (.conjL (.conjR hf)) ht (SyntaxTermImagePrefixTotal.typed_outputs f a z id w c d A hf hz)
  let G := (imageMap w.castSucc (Fin.last m) A.castSucc c.castSucc d.castSucc).conj
    (graph f.castSucc a.castSucc z.castSucc A.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  have he1 : Derives Γ (.ex G) := of_eq (by simp only [G, matrix_graph, paramsUp, id_eq]) he
  apply Derives.exE (p := G) he1
  have hf1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (imageMap_rename w f a c d Fin.castSucc) (under hf G)
  have hz1 : Derives Δ (SyntaxTermSyntax.term w.castSucc c.castSucc d.castSucc z.castSucc) := of_eq (SyntaxTermSyntax.term_rename w c d z Fin.castSucc) (under hz G)
  have hA1 : Derives Δ (successor A.castSucc a.castSucc) := of_eq (successor_rename A a Fin.castSucc) (under hA G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hp : Derives Δ (prefixed w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc z.castSucc A.castSucc (Fin.last m)) :=
    .conjI hf1 (.conjI hz1 (.conjI hA1 (.conjI (.conjL hG) (.conjR hG))))
  exact of_eq (existsPrefix_rename w f a c d z A Fin.castSucc).symm
    (intro_exists _ _ _ _ _ _ _ _ hp)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A g h : Fin m)
    (hg : Derives Γ (prefixed w f a c d z A g)) (hh : Derives Γ (prefixed w f a c d z A h)) : Derives Γ (.equal g h) :=
  RelationGraph.unique_graph hZ (matrix f a z) (id : Fin m → Fin m) A g h
    (of_eq (matrix_graph f a z id A g).symm (.conjR (.conjR (.conjR (.conjR hg)))))
    (of_eq (matrix_graph f a z id A h).symm (.conjR (.conjR (.conjR (.conjR hh)))))

theorem guarded_edges {m} {Γ : Context m} (w f a c d z A g i q : Fin m)
    (hg : Derives Γ (prefixed w f a c d z A g)) :
    Derives Γ ((edge g i q).iff ((Formula.mem i A).conj (value f a z i q))) := by
  have hl := Derives.conjR (.conjR (.conjR (.conjR (.conjR hg))))
  exact of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i hl))

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A g i q : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (prefixed w f a c d z A g)) :
    Derives Γ ((edge g i q).iff (value f a z i q)) := by
  have he := guarded_edges w f a c d z A g i q hg
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let V := value f a z i q
    have hV : Derives (Context.add V Γ) V := .hyp (Or.inl rfl)
    have hi := SyntaxTermImagePrefixPoint.source_member (ZFContext.add hZ V) w f a z A i q
      (add hw V) (add (.conjL (.conjL hg)) V) (add (.conjL (.conjR (.conjR hg))) V) hV
    exact .impE (add (.conjR he) V) (.conjI hi hV)

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A g i q : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (prefixed w f a c d z A g)) (hi : Derives Γ (empty i)) :
    Derives Γ ((edge g i q).iff (Formula.equal q z)) := by
  have he := edge_iff hZ w f a c d z A g i q hw hg
  have hv := SyntaxTermImagePrefixPoint.zero_iff f a z i q hi
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hv) _) (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.impE (add (.conjR hv) _) (.hyp (Or.inl rfl)))

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c d z A g i q k : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (prefixed w f a c d z A g))
    (hk : Derives Γ (.mem k a)) (hi : Derives Γ (successor i k)) : Derives Γ ((edge g i q).iff (edge f k q)) := by
  have hkNat := StructuralListTraceOrder.member_member hZ w k a hw (.conjL (.conjL hg)) hk
  have he := edge_iff hZ w f a c d z A g i q hw hg
  have hv := SyntaxTermImagePrefixPoint.successor_iff hZ w f a z i q k hw hkNat hi
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hv) _) (.impE (add (.conjL he) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR he) _) (.impE (add (.conjR hv) _) (.conjI (add hk _) (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.SyntaxTermImagePrefixGraph
