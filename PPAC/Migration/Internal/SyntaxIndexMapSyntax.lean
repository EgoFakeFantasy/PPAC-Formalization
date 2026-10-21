import PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode

/-! 内部bound/free索引的完整非单射映射图；不以宿主函数替代实际集合图。 -/
namespace PPAC.Migration.Internal.SyntaxIndexMapSyntax
open Source SourceAlgebra SourceLogic SyntaxTermSyntax SequenceSyntax

def indexMap {m} (w r a b : Fin m) : Formula m := (contexts w a b).conj (sequence r a b)

def maps {m} (w r s a b c d : Fin m) : Formula m :=
  (indexMap w r a c).conj (indexMap w s b d)

def selectMap {m} (bound : Bool) (r s : Fin m) : Fin m := if bound then r else s

theorem indexMap_rename {m n} (w r a b : Fin m) (ρ : Fin m → Fin n) :
    (indexMap w r a b).rename ρ = indexMap (ρ w) (ρ r) (ρ a) (ρ b) := by
  simp only [indexMap, Formula.rename, contexts_rename, sequence_rename]

theorem maps_rename {m n} (w r s a b c d : Fin m) (ρ : Fin m → Fin n) :
    (maps w r s a b c d).rename ρ = maps (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [maps, Formula.rename, indexMap_rename]

theorem selectMap_map {m n} (bound : Bool) (r s : Fin m) (ρ : Fin m → Fin n) :
    ρ (selectMap bound r s) = selectMap bound (ρ r) (ρ s) := by cases bound <;> rfl

theorem source_contexts {m} {Γ : Context m} (w r s a b c d : Fin m) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (contexts w a b) := .conjI (.conjL (.conjL (.conjL hm))) (.conjL (.conjL (.conjR hm)))

theorem target_contexts {m} {Γ : Context m} (w r s a b c d : Fin m) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (contexts w c d) := .conjI (.conjR (.conjL (.conjL hm))) (.conjR (.conjL (.conjR hm)))

theorem selected {m} {Γ : Context m} (bound : Bool) (w r s a b c d : Fin m) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (indexMap w (selectMap bound r s) (limit bound a b) (limit bound c d)) := by
  cases bound
  · exact .conjR hm
  · exact .conjL hm

theorem edge_target {m} {Γ : Context m} (w r a b i j : Fin m)
    (hm : Derives Γ (indexMap w r a b)) (he : Derives Γ (GraphSyntax.edge r i j)) : Derives Γ (.mem j b) :=
  .impE (SequenceSyntax.bounded_at r b i j (.conjR (.conjR hm))) he

theorem edge_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a b i j : Fin m)
    (hm : Derives Γ (indexMap w r a b)) (he : Derives Γ (GraphSyntax.edge r i j)) : Derives Γ (.mem i a) :=
  GraphProperties.domain_of_edge r a i j (ZFContext.arithmetic hZ).base.extensionality (.conjL (.conjR hm)) he

theorem value_exists {m} {Γ : Context m} (w r a b i : Fin m)
    (hm : Derives Γ (indexMap w r a b)) (hi : Derives Γ (.mem i a)) : Derives Γ (SequenceSyntax.value r i b) :=
  SequenceLogic.value_at r a b i (.conjR hm) hi
end PPAC.Migration.Internal.SyntaxIndexMapSyntax
