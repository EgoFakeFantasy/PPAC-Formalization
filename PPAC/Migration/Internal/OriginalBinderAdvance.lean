import PPAC.Migration.Internal.OriginalBinderReadAtLift

/-! 独立深度后继子运行与真实advanced历史程序；所有绑定界和像表见证在对象存在量词中。 -/
namespace PPAC.Migration.Internal.OriginalBinderAdvance
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward_at_depth {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x X D : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hd : Derives Γ (successor D depth))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode D (OriginalOperationFrameSyntax.parameter three P S) x X)) :
    Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b a c X) := by
  have he := OriginalOperationFrameRules.environment hZ three w mode depth P a b c I J R S hw hf
  have hLists : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a c R S) :=
    .conjI (IndexTermImageCodeTyping.term_list true w I R a a c (.conjL he)) (IndexTermImageCodeTyping.term_list false w J S b a c (.conjR he))
  have hInput := IndexTermImageCodeTyping.input_of_converted true w I R a a c (.conjL he)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) a.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (OriginalBinderStepSyntax.successor_exists w a hw (.conjL (.conjL hInput)))
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hLists1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w.castSucc a.castSucc b.castSucc a.castSucc c.castSucc R.castSucc S.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a b a c R S Fin.castSucc) (under hLists B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hPair := SyntaxCodedMixedBinderExistence.exists_pair (ZFContext.under hZ B) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc a.castSucc c.castSucc (Fin.last m) (Fin.last m) hw1 (.conjI hLists1 (.conjI (.conjR hB) (.conjR hB)))
  let C := SyntaxCodedMixedBinderSyntax.lifted (old 2 w.castSucc) (old 2 R.castSucc) (old 2 S.castSucc) (old 2 a.castSucc) (old 2 b.castSucc) (old 2 a.castSucc) (old 2 c.castSucc) (old 2 (Fin.last m)) (old 2 (Fin.last m)) (slot 2 0) (slot 2 1)
  let Ξ := Context.add C (raisedContext 2 Δ)
  apply HornBinderRules.eliminate_many 2 C _ hPair
  let ρ : Fin m → Fin ((m+1)+2) := fun i => old 2 i.castSucc
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Ξ (p.rename ρ) :=
    of_eq (by simp only [Formula.raise, rename_comp]; rfl) (HornBinderRules.under_body 2 (under hp B) C)
  have hZ2 : ZFContext.Evidence Ξ := HornBinderRules.zf_body 2 (ZFContext.under hZ B) C
  have hw2 : Derives Ξ (omega (ρ w)) := of_eq (omega_rename w ρ) (lift hw)
  have hi2 : Derives Ξ (OriginalUniformInductionSyntax.allFramesIH three (ρ w) (ρ n)) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n ρ) (lift hi)
  have hf2 : Derives Ξ (OriginalOperationFrameSyntax.frame three (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S ρ) (lift hf)
  have hn2 : Derives Ξ (FormulaCodeSyntax.formulaCode (ρ w) (ρ n) (ρ a) (ρ b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b ρ) (lift hn)
  have hc2 : Derives Ξ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (ρ w) (ρ x) (ρ n)) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n ρ) (lift hc)
  have hg2 : Derives Ξ (FormulaTransformRecursionSyntax.graph (ρ w) (ρ h) (ρ n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n ρ) (lift hg)
  have hd2 : Derives Ξ (successor (ρ D) (ρ depth)) := of_eq (successor_rename D depth ρ) (lift hd)
  have hr2 : Derives Ξ (OriginalTransformRowSyntax.run 3 (ρ w) (ρ mode) (ρ D) (OriginalOperationFrameSyntax.parameter three (ρ P) (ρ S)) (ρ x) (ρ X)) :=
    of_eq (by simp only [OriginalTransformRowSyntax.run_rename, OriginalOperationFrameSyntax.parameter_map]) (lift hr)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hAt := OriginalBinderReadAtLift.read_at_lift_iff hZ2 three universal (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S) (ρ h) (ρ x) (ρ X) (old 2 (Fin.last m)) (old 2 (Fin.last m)) (slot 2 0) (slot 2 1) (ρ D) hw2 hi2 hf2 hn2 hc2 hg2 hd2 hC
  have hRead := Derives.impE (.conjL hAt) hr2
  have ho := FormulaTransformHistorySyntax.intro_advanced (ρ w) (ρ h) (ρ x) (ρ R) (ρ S) (ρ a) (ρ b) (ρ a) (ρ c) (ρ X) (old 2 (Fin.last m)) (old 2 (Fin.last m)) (slot 2 0) (slot 2 1) hC hRead
  exact of_eq (by simp only [Formula.raise, FormulaTransformHistorySyntax.advanced_rename]; rfl) ho

theorem from_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hs : Derives Γ (OriginalBinderStepSyntax.step w mode depth (OriginalOperationFrameSyntax.parameter three P S) x X)) :
    Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b a c X) := by
  let B := OriginalBinderStepSyntax.body w mode depth (OriginalOperationFrameSyntax.parameter three P S) x X
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename Fin.castSucc) := under hp B
  have hw2 : Derives Δ (omega (Fin.castSucc w)) := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hi2 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three (Fin.castSucc w) (Fin.castSucc n)) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n Fin.castSucc) (lift hi)
  have hf2 : Derives Δ (OriginalOperationFrameSyntax.frame three (Fin.castSucc w) (Fin.castSucc mode) (Fin.castSucc depth) (Fin.castSucc P) (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc c) (Fin.castSucc I) (Fin.castSucc J) (Fin.castSucc R) (Fin.castSucc S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S Fin.castSucc) (lift hf)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode (Fin.castSucc w) (Fin.castSucc n) (Fin.castSucc a) (Fin.castSucc b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b Fin.castSucc) (lift hn)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (Fin.castSucc w) (Fin.castSucc x) (Fin.castSucc n)) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n Fin.castSucc) (lift hc)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph (Fin.castSucc w) (Fin.castSucc h) (Fin.castSucc n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n Fin.castSucc) (lift hg)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr : Derives Δ (OriginalTransformRowSyntax.run 3 w.castSucc mode.castSucc (Fin.last m) (OriginalOperationFrameSyntax.parameter three P.castSucc S.castSucc) x.castSucc X.castSucc) :=
    of_eq (by simp only [OriginalOperationFrameSyntax.parameter_map]) (.conjR hB)
  have ha := forward_at_depth (ZFContext.under hZ B) three universal w.castSucc n.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc I.castSucc J.castSucc R.castSucc S.castSucc h.castSucc x.castSucc X.castSucc (Fin.last m) hw2 hi2 hf2 hn2 hc2 hg2 (.conjL hB) hr
  exact of_eq (FormulaTransformHistorySyntax.advanced_rename w h x R S a b a c X Fin.castSucc).symm ha

theorem to_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b a c X)) :
    Derives Γ (OriginalBinderStepSyntax.step w mode depth (OriginalOperationFrameSyntax.parameter three P S) x X) := by
  let C := FormulaTransformHistorySyntax.advancedBody w h x R S a b a c X
  let Ξ := Context.add C (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 C _ ha
  have hw1 : Derives Ξ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw C)
  have hf1 : Derives Ξ (OriginalOperationFrameSyntax.frame three (old 4 w) (old 4 mode) (old 4 depth) (old 4 P) (old 4 a) (old 4 b) (old 4 c) (old 4 I) (old 4 J) (old 4 R) (old 4 S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S (old 4)) (HornBinderRules.under_body 4 hf C)
  have hmeta := OriginalOperationFrameSyntax.metadata three (old 4 w) (old 4 mode) (old 4 depth) (old 4 P) (old 4 a) (old 4 b) (old 4 c) (old 4 I) (old 4 J) (old 4 R) (old 4 S) hf1
  let B := (Formula.mem (Fin.last (m+4)) (old 4 w).castSucc).conj (successor (Fin.last (m+4)) (old 4 depth).castSucc)
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply Derives.exE (p := B) (OriginalBinderStepSyntax.successor_exists (old 4 w) (old 4 depth) hw1 (.conjL hmeta))
  let ρ : Fin m → Fin ((m+4)+1) := fun i => (old 4 i).castSucc
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename ρ) :=
    of_eq (by simp only [Formula.raise, rename_comp]; rfl) (under (HornBinderRules.under_body 4 hp C) B)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (HornBinderRules.zf_body 4 hZ C) B
  have hw2 : Derives Δ (omega (ρ w)) := of_eq (omega_rename w ρ) (lift hw)
  have hi2 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three (ρ w) (ρ n)) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n ρ) (lift hi)
  have hf2 : Derives Δ (OriginalOperationFrameSyntax.frame three (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S ρ) (lift hf)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode (ρ w) (ρ n) (ρ a) (ρ b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b ρ) (lift hn)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (ρ w) (ρ x) (ρ n)) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n ρ) (lift hc)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph (ρ w) (ρ h) (ρ n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n ρ) (lift hg)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hl : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ a) (ρ c) (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc) :=
    of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 a) (old 4 c) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) Fin.castSucc) (under (.conjL hC) B)
  have hRead : Derives Δ (FormulaTransformHistorySyntax.read (ρ w) (ρ h) (ρ x) (slot 4 2).castSucc (slot 4 3).castSucc (slot 4 0).castSucc (ρ b) (slot 4 1).castSucc (ρ c) (ρ X)) :=
    of_eq (FormulaTransformHistorySyntax.read_rename (old 4 w) (old 4 h) (old 4 x) (slot 4 2) (slot 4 3) (slot 4 0) (old 4 b) (slot 4 1) (old 4 c) (old 4 X) Fin.castSucc) (under (.conjR hC) B)
  have he := OriginalBinderReadAtLift.read_at_lift_iff hZ2 three universal (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S) (ρ h) (ρ x) (ρ X) (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc (Fin.last (m+4)) hw2 hi2 hf2 hn2 hc2 hg2 (.conjR hB) hl
  have hRun := Derives.impE (.conjR he) hRead
  have ho := OriginalBinderStepSyntax.intro_step (ρ w) (ρ mode) (ρ depth) (OriginalOperationFrameSyntax.parameter three (ρ P) (ρ S)) (ρ x) (ρ X) (Fin.last (m+4)) (.conjR hB) hRun
  exact of_eq (by simp only [Formula.raise, OriginalBinderStepSyntax.step_rename, OriginalOperationFrameSyntax.parameter_map]; rfl) ho

theorem step_iff_advanced {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    : Derives Γ ((OriginalBinderStepSyntax.step w mode depth (OriginalOperationFrameSyntax.parameter three P S) x X).iff
      (FormulaTransformHistorySyntax.advanced w h x R S a b a c X)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact from_step (ZFContext.add hZ _) three universal w n mode depth P a b c I J R S h x X (add hw _) (add hi _) (add hf _) (add hn _) (add hc _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact to_step (ZFContext.add hZ _) three universal w n mode depth P a b c I J R S h x X (add hw _) (add hi _) (add hf _) (add hn _) (add hc _) (add hg _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalBinderAdvance
