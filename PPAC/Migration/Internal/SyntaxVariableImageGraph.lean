import PPAC.Migration.Internal.SyntaxVariableImageExistence

/-! 原Replacement实际构造唯一变量项码表；全部候选的准确边由原关系图定律给出。 -/
namespace PPAC.Migration.Internal.SyntaxVariableImageGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxVariableImageSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input bound w r a c d)) : Derives Γ (existsMap bound w r a c d) := by
  have ht := SyntaxVariableImageExistence.total_matrix hZ bound w r c d (id : Fin m → Fin m) a hw hi
  have he := SyntaxTermImageGraph.exists_image hZ (matrix bound w r c d) (id : Fin m → Fin m) w a c d hw
    (.conjL (.conjL (.conjR hi))) (.conjL hi) ht (SyntaxVariableImageExistence.typed_outputs bound w r c d (id : Fin m → Fin m) a)
  let G := (imageMap w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc).conj
    (graph bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m))
  let Δ := Context.add G (Context.image Formula.raise Γ)
  have he1 : Derives Γ (.ex G) := of_eq (by simp only [G, matrix_graph, paramsUp, id_eq]) he
  apply Derives.exE (p := G) he1
  have hi1 : Derives Δ (input bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (input_rename bound w r a c d Fin.castSucc) (under hi G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hp : Derives Δ (mapped bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)) := .conjI hi1 (.conjI (.conjL hG) (.conjR hG))
  exact of_eq (existsMap_rename bound w r a c d Fin.castSucc).symm (intro_exists bound _ _ _ _ _ _ hp)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d f g : Fin m)
    (hf : Derives Γ (mapped bound w r a c d f)) (hg : Derives Γ (mapped bound w r a c d g)) : Derives Γ (.equal f g) :=
  RelationGraph.unique_graph hZ (matrix bound w r c d) (id : Fin m → Fin m) a f g
    (of_eq (matrix_graph bound w r c d id a f).symm (.conjR (.conjR hf)))
    (of_eq (matrix_graph bound w r c d id a g).symm (.conjR (.conjR hg)))

theorem guarded_edges {m} {Γ : Context m} (bound : Bool) (w r a c d f i q : Fin m)
    (hf : Derives Γ (mapped bound w r a c d f)) :
    Derives Γ ((edge f i q).iff ((Formula.mem i a).conj (value bound w r c d i q))) := by
  have hl := Derives.conjR (.conjR (.conjR hf))
  exact of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i hl))

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d f i q : Fin m)
    (hf : Derives Γ (mapped bound w r a c d f)) : Derives Γ ((edge f i q).iff (value bound w r c d i q)) := by
  have he := guarded_edges bound w r a c d f i q hf
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let V := value bound w r c d i q
    have hV : Derives (Context.add V Γ) V := .hyp (Or.inl rfl)
    have hi := SyntaxVariableImagePoint.source_member (ZFContext.add hZ V) bound w r a c d i q (add (.conjL hf) V) hV
    exact .impE (add (.conjR he) V) (.conjI hi hV)
end PPAC.Migration.Internal.SyntaxVariableImageGraph
