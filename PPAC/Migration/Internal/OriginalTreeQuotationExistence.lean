import PPAC.Migration.Internal.OriginalTreeQuotationProperties

/-! 每个原外部树/森林模式实际取得内部数值码；子码、标签与根码均经对象存在消去取得。 -/
namespace PPAC.Migration.Internal.OriginalTreeQuotationExistence
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax OriginalTreeQuotationProperties
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

mutual
theorem tree_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (treeExists input w) := by
  cases input with
  | node tag children =>
    have hp := forest_exists hZ children w hw
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (forest children w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply Derives.exE (p := P) hp
    have hZ1 := ZFContext.under hZ P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have ht := SyntaxNumerals.exists_numeral hZ1 tag w.castSucc hw1
    let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last (m+1)))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    apply Derives.exE (p := T) ht
    have hZ2 := ZFContext.under hZ1 T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
    have hP2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (forest children w.castSucc.castSucc (Fin.last m).castSucc)) :=
      of_eq (by simp only [P, Formula.raise, Formula.rename, forest_rename]) (under hP T)
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have hn := StructuralNodeExistence.exists_raw hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 (.conjL hT) (.conjL hP2)
    let N := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (StructuralNodeSyntax.raw w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)))
    let Ω := Context.add N (Context.image Formula.raise Ξ)
    apply Derives.exE (p := N) hn
    have hP3 : Derives Ω ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj (forest children w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc)) :=
      of_eq (by simp only [Formula.raise, Formula.rename, forest_rename]) (under hP2 N)
    have hT3 : Derives Ω ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj (SyntaxNumeralSyntax.numeral tag (Fin.last (m+1)).castSucc)) :=
      of_eq (by simp only [T, Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename]) (under hT N)
    have hN : Derives Ω N := .hyp (Or.inl rfl)
    have hQ := intro_tree tag children w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (.conjR hT3) (.conjR hP3) (.conjR hN)
    have ho := intro_tree_exists (.node tag children) w.castSucc.castSucc.castSucc (Fin.last (m+2)) (.conjL hN) hQ
    exact of_eq (by simp only [Formula.raise, treeExists_rename]) ho
termination_by sizeOf input

theorem forest_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : List Tree) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (forestExists input w) := by
  cases input with
  | nil => simpa only [forestExists, forest, SyntaxForestSyntax.existsForest, SyntaxForestSyntax.forest] using SyntaxForests.exists_forest hZ 0 w Fin.elim0 hw (Derives.eqRefl w)
  | cons head tail =>
    have hh := tree_exists hZ head w hw
    let H := (Formula.mem (Fin.last m) w.castSucc).conj (tree head w.castSucc (Fin.last m))
    let Δ := Context.add H (Context.image Formula.raise Γ)
    apply Derives.exE (p := H) hh
    have hZ1 := ZFContext.under hZ H
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have ht := forest_exists hZ1 tail w.castSucc hw1
    let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (forest tail w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add T (Context.image Formula.raise Δ)
    apply Derives.exE (p := T) ht
    have hZ2 := ZFContext.under hZ1 T
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
    have hH2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (tree head w.castSucc.castSucc (Fin.last m).castSucc)) :=
      of_eq (by simp only [H, Formula.raise, Formula.rename, tree_rename]) (under hH T)
    have hT : Derives Ξ T := .hyp (Or.inl rfl)
    have hn := StructuralConsCore.exists_cons hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hH2) (.conjL hT)
    let N := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))
    let Ω := Context.add N (Context.image Formula.raise Ξ)
    apply Derives.exE (p := N) hn
    have hH3 : Derives Ω ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj (tree head w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc)) :=
      of_eq (by simp only [Formula.raise, Formula.rename, tree_rename]) (under hH2 N)
    have hT3 : Derives Ω ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj (forest tail w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc)) :=
      of_eq (by simp only [T, Formula.raise, Formula.rename, forest_rename]) (under hT N)
    have hN : Derives Ω N := .hyp (Or.inl rfl)
    have hQ := intro_cons head tail w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (.conjR hH3) (.conjR hT3) (.conjR hN)
    have ho := intro_forest_exists (head :: tail) w.castSucc.castSucc.castSucc (Fin.last (m+2)) (.conjL hN) hQ
    exact of_eq (by simp only [Formula.raise, forestExists_rename]) ho
termination_by sizeOf input
end

end PPAC.Migration.Internal.OriginalTreeQuotationExistence
