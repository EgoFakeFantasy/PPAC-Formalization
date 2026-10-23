import PPAC.Migration.Internal.OriginalTreeQuotationUnique

/-! 原树quotation各外部有限模式具有实际唯一内部码纤维；外部模式索引不变成内部统一真值谓词。 -/
namespace PPAC.Migration.Internal.OriginalTreeQuotationFiber
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax OriginalTreeQuotationProperties
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tree_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree input w n)) : Derives Γ (treeUnique input w n) := by
  apply Derives.allI
  apply Derives.impI
  let N := tree input w.castSucc (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hn1 : Derives Δ (tree input w.castSucc n.castSucc) := of_eq (tree_rename input w n Fin.castSucc) (under hn N)
  exact OriginalTreeQuotationUnique.tree_unique (ZFContext.under hZ N) input w.castSucc (Fin.last m) n.castSucc hw1 (.hyp (Or.inl rfl)) hn1

theorem tree_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (treeFiber input w) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ input w hw
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (tree input w.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) he
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hu := tree_unique_output (ZFContext.under hZ N) input w.castSucc (Fin.last m) hw1 (.conjR hN)
  have ho : Derives Δ (treeFiber input w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [treeUnique, Formula.instantiate, Formula.rename, tree_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hN) hu)
  exact of_eq (treeFiber_rename input w Fin.castSucc).symm ho

theorem forest_unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : List Tree) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest input w n)) : Derives Γ (forestUnique input w n) := by
  apply Derives.allI
  apply Derives.impI
  let N := forest input w.castSucc (Fin.last m)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hn1 : Derives Δ (forest input w.castSucc n.castSucc) := of_eq (forest_rename input w n Fin.castSucc) (under hn N)
  exact OriginalTreeQuotationUnique.forest_unique (ZFContext.under hZ N) input w.castSucc (Fin.last m) n.castSucc hw1 (.hyp (Or.inl rfl)) hn1

theorem forest_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : List Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (forestFiber input w) := by
  have he := OriginalTreeQuotationExistence.forest_exists hZ input w hw
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (forest input w.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) he
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hu := forest_unique_output (ZFContext.under hZ N) input w.castSucc (Fin.last m) hw1 (.conjR hN)
  have ho : Derives Δ (forestFiber input w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [forestUnique, Formula.instantiate, Formula.rename, forest_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hN) hu)
  exact of_eq (forestFiber_rename input w Fin.castSucc).symm ho

end PPAC.Migration.Internal.OriginalTreeQuotationFiber
