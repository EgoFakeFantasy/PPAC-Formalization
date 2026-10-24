import PPAC.Migration.Internal.ProjectSourceTypeEvaluationSyntax

/-! 原ZF实际构造后继域、完整上下文集合值递归图及真边，覆盖每个内部原序数索引。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeEvaluationExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax ProjectSourceTypeEvaluationSyntax
open ProjectSourceTypeRecursionSyntax
open SyntaxAtomSyntax (two two_map)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n : Fin m)
    (hn : Derives Γ (ordinal n)) : Derives Γ (existsValue w c n) := by
  have hex := InsertExistence.exists_insert n n (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let S := successor (Fin.last m) n.castSucc
  let Ξ1 := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hex
  apply Derives.exE (p := S) hex
  have hZ1 : ZFContext.Evidence Ξ1 := ZFContext.under hZ S
  have hn1 : Derives Ξ1 (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn S
  have hS : Derives Ξ1 S := .hyp (Or.inl rfl)
  have hd := OrdinalSuccessor.ordinal (Fin.last m) n.castSucc (ZFContext.arithmetic hZ1).base.foundation hS hn1
  have hf := ProjectSourceTypeRecursors.exists_graph hZ1 w.castSucc c.castSucc (Fin.last m) hd
  let F := graph w.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
  let Ξ2 := Context.add F (Context.image Formula.raise Ξ1)
  change Derives Ξ1 (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hS2 : Derives Ξ2 (successor (Fin.last m).castSucc n.castSucc.castSucc) := by simpa only [S, Formula.raise, successor_rename] using under hS F
  have hF : Derives Ξ2 F := .hyp (Or.inl rfl)
  have hmem := InsertLogic.new_member _ _ _ hS2
  have hy := GraphProperties.output_exists _ _ _ (.conjL hF) hmem
  let Y := edge (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add Y (Context.image Formula.raise Ξ2)
  change Derives Ξ2 (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hS3 : Derives Δ (successor (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under hS2 Y
  have hF3 : Derives Δ (graph w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [F, Formula.raise, graph_rename] using under hF Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hv := intro_value _ _ _ _ _ _ hS3 hF3 hY
  have hout := intro_exists _ _ _ _ hv
  simpa only [Formula.raise, existsValue_rename] using hout

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsValue w c n) :=
  exists_value hZ w c n (NaturalOrderBasic.ordinal hZ w n hw hn)
end PPAC.Migration.Internal.ProjectSourceTypeEvaluationExistence
