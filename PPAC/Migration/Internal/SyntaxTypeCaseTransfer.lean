import PPAC.Migration.Internal.SyntaxTypeFieldsTransfer

/-! 七个逻辑/量词分支的历史无关类型双条件，所有内部字段见证保留。 -/
namespace PPAC.Migration.Internal.SyntaxTypeCaseTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxTypeRecursionSyntax SyntaxLogicalSyntax SyntaxTypeRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w c b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n)) :
    Derives Γ ((single tag advance w b f h n).iff (singleCase tag advance w c b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := single tag advance w b f h n
    let Ξ := Context.add P Γ
    let B := singleBody tag advance w b f h n
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply SyntaxLogicalSyntax.eliminate_single tag advance w b f h n _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) B
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc n.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg P) B
    have hc : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by
      simpa only [Formula.raise, contexts_rename] using under (Derives.conjL (.hyp (Or.inl rfl)) : Derives Ξ (contexts w b f)) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hd := SyntaxTypeFieldsTransfer.single_forward hZ1 tag advance
      w.castSucc c.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc
      hw1 (under (add hn P) B) hg1 hB
    have hout : Derives Δ (singleCase tag advance w.castSucc c.castSucc b.castSucc f.castSucc n.castSucc) := SyntaxTypeRecursiveSyntax.intro_single tag advance w.castSucc c.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc hc hd
    simpa only [Formula.raise, singleCase_rename] using hout
  · apply Derives.impI
    let P := singleCase tag advance w c b f n
    let Ξ := Context.add P Γ
    let B := singleCaseBody tag advance w c b f n
    let Δ := Context.add B (Context.image Formula.raise Ξ)
    apply SyntaxTypeRecursiveSyntax.eliminate_single tag advance w c b f n _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) B
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc n.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg P) B
    have hc : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by
      simpa only [Formula.raise, contexts_rename] using under (Derives.conjL (.hyp (Or.inl rfl)) : Derives Ξ (contexts w b f)) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hd := SyntaxTypeFieldsTransfer.single_backward hZ1 tag advance
      w.castSucc c.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc
      hw1 (under (add hn P) B) hg1 hB
    have hout : Derives Δ (single tag advance w.castSucc b.castSucc f.castSucc h.castSucc n.castSucc) := SyntaxLogicalSyntax.intro_single tag advance w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc hc hd
    simpa only [Formula.raise, single_rename] using hout

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w c b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n)) :
    Derives Γ ((binary kind w b f h n).iff (binaryCase kind w c b f n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := binary kind w b f h n
    let Ξ := Context.add P Γ
    let B := binaryBody kind w b f h n
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Ξ))
    apply SyntaxLogicalSyntax.eliminate_binary kind w b f h n _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under_two (ZFContext.add hZ P) B
    have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw P) B
    have hg1 : Derives Δ (graph w.castSucc.castSucc c.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := by
      simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two (add hg P) B
    have hc : Derives Δ (contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
      simpa only [Formula.raise, contexts_rename] using OrderedPairElimination.under_two (Derives.conjL (.hyp (Or.inl rfl)) : Derives Ξ (contexts w b f)) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hd := SyntaxTypeFieldsTransfer.binary_forward hZ1 kind
      w.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc
      hw1 (OrderedPairElimination.under_two (add hn P) B) hg1 hB
    have hout : Derives Δ (binaryCase kind w.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc) := SyntaxTypeRecursiveSyntax.intro_binary kind w.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hc hd
    simpa only [Formula.raise, binaryCase_rename] using hout
  · apply Derives.impI
    let P := binaryCase kind w c b f n
    let Ξ := Context.add P Γ
    let B := binaryCaseBody kind w c b f n
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Ξ))
    apply SyntaxTypeRecursiveSyntax.eliminate_binary kind w c b f n _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under_two (ZFContext.add hZ P) B
    have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw P) B
    have hg1 : Derives Δ (graph w.castSucc.castSucc c.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := by
      simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two (add hg P) B
    have hc : Derives Δ (contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
      simpa only [Formula.raise, contexts_rename] using OrderedPairElimination.under_two (Derives.conjL (.hyp (Or.inl rfl)) : Derives Ξ (contexts w b f)) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hd := SyntaxTypeFieldsTransfer.binary_backward hZ1 kind
      w.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc
      hw1 (OrderedPairElimination.under_two (add hn P) B) hg1 hB
    have hout : Derives Δ (binary kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := SyntaxLogicalSyntax.intro_binary kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hc hd
    simpa only [Formula.raise, binary_rename] using hout
end PPAC.Migration.Internal.SyntaxTypeCaseTransfer
