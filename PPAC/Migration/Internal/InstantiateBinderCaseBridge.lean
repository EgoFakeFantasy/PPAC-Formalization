import PPAC.Migration.Internal.InstantiateBinderAdvance

/-! 原两种量词局部分支与真实advanced程序的双条件；字段和后继见证均在对象层消去。 -/
namespace PPAC.Migration.Internal.InstantiateBinderCaseBridge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem to_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (he : Derives Γ (OriginalFormulaCaseSyntax.binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth P n q)) :
    Derives Γ (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q) := by
  let B := OriginalFormulaCaseSyntax.binderBody (SyntaxLogicalSyntax.quantifierTag universal) w mode depth P n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  let C := OriginalFormulaCaseSyntax.unaryBody (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc mode.castSucc (Fin.last m) P.castSucc n.castSucc q.castSucc
  let Ξ := Context.add C (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 C _ (.conjR hB)
  let ρ : Fin m → Fin ((m+1)+2) := fun i => old 2 i.castSucc
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Ξ (p.rename ρ) :=
    of_eq (by simp only [Formula.raise, rename_comp]; rfl) (HornBinderRules.under_body 2 (under hp B) C)
  have hZ2 : ZFContext.Evidence Ξ := HornBinderRules.zf_body 2 (ZFContext.under hZ B) C
  have hw2 : Derives Ξ (omega (ρ w)) := of_eq (omega_rename w ρ) (lift hw)
  have hi2 : Derives Ξ (InstantiateUniformInductionSyntax.allFramesIH (ρ w) (ρ n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n ρ) (lift hi)
  have hf2 : Derives Ξ (InstantiateOperationFrameSyntax.frame (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S ρ) (lift hf)
  have hn2 : Derives Ξ (FormulaCodeSyntax.formulaCode (ρ w) (ρ n) (ρ a) (ρ b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b ρ) (lift hn)
  have hg2 : Derives Ξ (FormulaTransformRecursionSyntax.graph (ρ w) (ρ h) (ρ n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n ρ) (lift hg)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hs : Derives Ξ (successor (old 2 (Fin.last m)) (ρ depth)) := of_eq (successor_rename (Fin.last m) depth.castSucc (old 2)) (HornBinderRules.under_body 2 (.conjL hB) C)
  have hr : Derives Ξ (OriginalTransformRowSyntax.run 3 (ρ w) (ρ mode) (old 2 (Fin.last m)) (ρ P) (slot 2 0) (slot 2 1)) :=
    of_eq (by rfl) (.conjR hC)
  have hSource := Derives.conjL (Derives.conjL hC)
  have hTarget := Derives.conjR (Derives.conjL hC)
  have ha := InstantiateBinderAdvance.forward_at_depth hZ2 universal (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S) (ρ h) (slot 2 0) (slot 2 1) (old 2 (Fin.last m)) hw2 hi2 hf2 hn2 hSource hg2 hs hr
  have hx := SyntaxConstructors.child_member hZ2 1 (SyntaxLogicalSyntax.quantifierTag universal) (ρ w) (fun _ => slot 2 0) (ρ n) 0 hw2 hSource
  have ho := FormulaTransformLogicalSyntax.intro_single (SyntaxLogicalSyntax.quantifierTag universal) true (ρ w) (ρ h) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ e) (ρ n) (ρ q) (slot 2 0) (slot 2 1) (.conjI hSource (.conjI hx (.conjI hTarget ha)))
  exact of_eq (by simp only [Formula.raise, FormulaTransformLogicalSyntax.single_rename]; rfl) ho

theorem from_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (he : Derives Γ (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q)) :
    Derives Γ (OriginalFormulaCaseSyntax.binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth P n q) := by
  let C := FormulaTransformLogicalSyntax.singleBody (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q
  let Ξ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ he
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Ξ (p.rename (old 2)) := HornBinderRules.under_body 2 hp C
  have hZ1 : ZFContext.Evidence Ξ := HornBinderRules.zf_body 2 hZ C
  have hw1 : Derives Ξ (omega ((old 2) w)) := of_eq (omega_rename w (old 2)) (lift hw)
  have hi1 : Derives Ξ (InstantiateUniformInductionSyntax.allFramesIH ((old 2) w) ((old 2) n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n (old 2)) (lift hi)
  have hf1 : Derives Ξ (InstantiateOperationFrameSyntax.frame ((old 2) w) ((old 2) mode) ((old 2) depth) ((old 2) P) ((old 2) a) ((old 2) b) ((old 2) c) ((old 2) e) ((old 2) R) ((old 2) S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S (old 2)) (lift hf)
  have hn1 : Derives Ξ (FormulaCodeSyntax.formulaCode ((old 2) w) ((old 2) n) ((old 2) a) ((old 2) b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b (old 2)) (lift hn)
  have hg1 : Derives Ξ (FormulaTransformRecursionSyntax.graph ((old 2) w) ((old 2) h) ((old 2) n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 2)) (lift hg)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hSource := Derives.conjL hC
  have hTarget := Derives.conjL (Derives.conjR (Derives.conjR hC))
  have hs := InstantiateBinderAdvance.to_step hZ1 universal (old 2 w) (old 2 n) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 e) (old 2 R) (old 2 S) (old 2 h) (slot 2 0) (slot 2 1) hw1 hi1 hf1 hn1 hSource hg1 (.conjR (.conjR (.conjR hC)))
  let B := OriginalBinderStepSyntax.body (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply Derives.exE (p := B) hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hSource2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w).castSucc (slot 2 0).castSucc (old 2 n).castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w) (slot 2 0) (old 2 n) Fin.castSucc) (under hSource B)
  have hTarget2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w).castSucc (slot 2 1).castSucc (old 2 q).castSucc) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w) (slot 2 1) (old 2 q) Fin.castSucc) (under hTarget B)
  have hUnary := OriginalFormulaCaseSyntax.intro_unary (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w).castSucc (old 2 mode).castSucc (Fin.last (m+2)) (old 2 P).castSucc (old 2 n).castSucc (old 2 q).castSucc (slot 2 0).castSucc (slot 2 1).castSucc (.conjI (.conjI hSource2 hTarget2) (.conjR hB))
  have ho := OriginalFormulaCaseSyntax.intro_binder (SyntaxLogicalSyntax.quantifierTag universal) (old 2 w).castSucc (old 2 mode).castSucc (old 2 depth).castSucc (old 2 P).castSucc (old 2 n).castSucc (old 2 q).castSucc (Fin.last (m+2)) (.conjL hB) hUnary
  exact of_eq (by simp only [Formula.raise, OriginalFormulaCaseSyntax.binderCase_rename]) ho

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h q : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    : Derives Γ ((OriginalFormulaCaseSyntax.binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth P n q).iff
      (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_program (ZFContext.add hZ _) universal w n mode depth P a b c e R S h q (add hw _) (add hi _) (add hf _) (add hn _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_program (ZFContext.add hZ _) universal w n mode depth P a b c e R S h q (add hw _) (add hi _) (add hf _) (add hn _) (add hg _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.InstantiateBinderCaseBridge
