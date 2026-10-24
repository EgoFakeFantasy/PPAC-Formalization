import PPAC.Migration.Internal.InstantiateBinderReadAtLift

/-! mode2真实advanced历史与深度后继子运行；源／目标后继界分别实际构造，所有像表EX消去。 -/
namespace PPAC.Migration.Internal.InstantiateBinderAdvance
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix
attribute [local irreducible] InstantiateOperationFrameSyntax.frame InstantiateUniformInductionSyntax.allFramesIH

theorem forward_at_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X D A C : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) (hd : Derives Γ (successor D depth))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode D P x X))
    (hA : Derives Γ (successor A a)) (hC : Derives Γ (successor C c)) :
    Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b c e X) := by
  have hLists := InstantiateOperationFrameSyntax.term_lists w mode depth P a b c e R S hf
  let B := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (SyntaxCodedMixedBinderExistence.exists_pair hZ w R S a b c e A C hw (.conjI hLists (.conjI hA hC)))
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw B)
  have hi2 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, InstantiateUniformInductionSyntax.allFramesIH_rename]) (OrderedPairElimination.under_two hi B)
  have hf2 : Derives Δ (InstantiateOperationFrameSyntax.frame w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, InstantiateOperationFrameSyntax.frame_rename]) (OrderedPairElimination.under_two hf B)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (OrderedPairElimination.under_two hn B)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (OrderedPairElimination.under_two hc B)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaTransformRecursionSyntax.graph_rename]) (OrderedPairElimination.under_two hg B)
  have hd2 : Derives Δ (successor D.castSucc.castSucc depth.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (OrderedPairElimination.under_two hd B)
  have hr2 : Derives Δ (OriginalTransformRowSyntax.run 3 w.castSucc.castSucc mode.castSucc.castSucc D.castSucc.castSucc P.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTransformRowSyntax.run_rename]) (OrderedPairElimination.under_two hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hAt := InstantiateBinderReadAtLift.read_at_lift_iff hZ2 universal w.castSucc.castSucc n.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) D.castSucc.castSucc hw2 hi2 hf2 hn2 hc2 hg2 hd2 hB
  have hRead := Derives.impE (.conjL hAt) hr2
  have ho := FormulaTransformHistorySyntax.intro_advanced w.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc X.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hB hRead
  exact of_eq (by simp only [FormulaTransformHistorySyntax.advanced_rename, old]) ho

theorem forward_at_depth {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X D : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) (hd : Derives Γ (successor D depth))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode D P x X)) : Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b c e X) := by
  have hm := InstantiateOperationFrameSyntax.term_lists w mode depth P a b c e R S hf
  have ha : Derives Γ (.mem a w) := .conjL (.conjL hm)
  have hcNat : Derives Γ (.mem c w) := .conjL (.conjL (.conjR (.conjL hm)))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) a.castSucc)
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (OriginalBinderStepSyntax.successor_exists w a hw ha)
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hc1 : Derives Ξ (.mem c.castSucc w.castSucc) := under hcNat E
  let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) c.castSucc.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE (p := F) (OriginalBinderStepSyntax.successor_exists w.castSucc c.castSucc hw1 hc1)
  have hZ2 := ZFContext.under (ZFContext.under hZ E) F
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw E) F)
  have hi2 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, InstantiateUniformInductionSyntax.allFramesIH_rename]) (under (under hi E) F)
  have hf2 : Derives Δ (InstantiateOperationFrameSyntax.frame w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, InstantiateOperationFrameSyntax.frame_rename]) (under (under hf E) F)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (under (under hn E) F)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under (under hc E) F)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaTransformRecursionSyntax.graph_rename]) (under (under hg E) F)
  have hd2 : Derives Δ (successor D.castSucc.castSucc depth.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under hd E) F)
  have hr2 : Derives Δ (OriginalTransformRowSyntax.run 3 w.castSucc.castSucc mode.castSucc.castSucc D.castSucc.castSucc P.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTransformRowSyntax.run_rename]) (under (under hr E) F)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hA : Derives Δ (successor (Fin.last m).castSucc a.castSucc.castSucc) := of_eq (successor_rename (Fin.last m) a.castSucc Fin.castSucc) (under (.conjR hE) F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have ho := forward_at_bounds hZ2 universal w.castSucc.castSucc n.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc h.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc D.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hf2 hn2 hc2 hg2 hd2 hr2 hA (.conjR hF)
  exact of_eq (by simp only [Formula.raise, FormulaTransformHistorySyntax.advanced_rename]) ho

theorem from_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hs : Derives Γ (OriginalBinderStepSyntax.step w mode depth P x X)) :
    Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b c e X) := by
  let B := OriginalBinderStepSyntax.body w mode depth P x X
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename Fin.castSucc) := under hp B
  have hw2 : Derives Δ (omega (Fin.castSucc w)) := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hi2 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH (Fin.castSucc w) (Fin.castSucc n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n Fin.castSucc) (lift hi)
  have hf2 : Derives Δ (InstantiateOperationFrameSyntax.frame (Fin.castSucc w) (Fin.castSucc mode) (Fin.castSucc depth) (Fin.castSucc P) (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc c) (Fin.castSucc e) (Fin.castSucc R) (Fin.castSucc S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S Fin.castSucc) (lift hf)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode (Fin.castSucc w) (Fin.castSucc n) (Fin.castSucc a) (Fin.castSucc b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b Fin.castSucc) (lift hn)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (Fin.castSucc w) (Fin.castSucc x) (Fin.castSucc n)) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n Fin.castSucc) (lift hc)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph (Fin.castSucc w) (Fin.castSucc h) (Fin.castSucc n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n Fin.castSucc) (lift hg)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr : Derives Δ (OriginalTransformRowSyntax.run 3 w.castSucc mode.castSucc (Fin.last m) P.castSucc x.castSucc X.castSucc) :=
    of_eq (by rfl) (.conjR hB)
  have ha := forward_at_depth (ZFContext.under hZ B) universal w.castSucc n.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc h.castSucc x.castSucc X.castSucc (Fin.last m) hw2 hi2 hf2 hn2 hc2 hg2 (.conjL hB) hr
  exact of_eq (FormulaTransformHistorySyntax.advanced_rename w h x R S a b c e X Fin.castSucc).symm ha

theorem to_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (FormulaTransformHistorySyntax.advanced w h x R S a b c e X)) :
    Derives Γ (OriginalBinderStepSyntax.step w mode depth P x X) := by
  let C := FormulaTransformHistorySyntax.advancedBody w h x R S a b c e X
  let Ξ := Context.add C (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 C _ ha
  have hw1 : Derives Ξ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw C)
  have hf1 : Derives Ξ (InstantiateOperationFrameSyntax.frame (old 4 w) (old 4 mode) (old 4 depth) (old 4 P) (old 4 a) (old 4 b) (old 4 c) (old 4 e) (old 4 R) (old 4 S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S (old 4)) (HornBinderRules.under_body 4 hf C)
  have hmeta := InstantiateOperationFrameSyntax.metadata (old 4 w) (old 4 mode) (old 4 depth) (old 4 P) (old 4 a) (old 4 b) (old 4 c) (old 4 e) (old 4 R) (old 4 S) hf1
  let B := (Formula.mem (Fin.last (m+4)) (old 4 w).castSucc).conj (successor (Fin.last (m+4)) (old 4 depth).castSucc)
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply Derives.exE (p := B) (OriginalBinderStepSyntax.successor_exists (old 4 w) (old 4 depth) hw1 (.conjL hmeta))
  let ρ : Fin m → Fin ((m+4)+1) := fun i => (old 4 i).castSucc
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename ρ) :=
    of_eq (by simp only [Formula.raise, rename_comp]; rfl) (under (HornBinderRules.under_body 4 hp C) B)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (HornBinderRules.zf_body 4 hZ C) B
  have hw2 : Derives Δ (omega (ρ w)) := of_eq (omega_rename w ρ) (lift hw)
  have hi2 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH (ρ w) (ρ n)) := of_eq (InstantiateUniformInductionSyntax.allFramesIH_rename w n ρ) (lift hi)
  have hf2 : Derives Δ (InstantiateOperationFrameSyntax.frame (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S)) := of_eq (InstantiateOperationFrameSyntax.frame_rename w mode depth P a b c e R S ρ) (lift hf)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode (ρ w) (ρ n) (ρ a) (ρ b)) := of_eq (FormulaCodeSyntax.formulaCode_rename w n a b ρ) (lift hn)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) (ρ w) (ρ x) (ρ n)) := of_eq (SyntaxLogicalSyntax.singleCode_rename (SyntaxLogicalSyntax.quantifierTag universal) w x n ρ) (lift hc)
  have hg2 : Derives Δ (FormulaTransformRecursionSyntax.graph (ρ w) (ρ h) (ρ n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n ρ) (lift hg)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hl : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ e) (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc) :=
    of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename (old 4 w) (old 4 R) (old 4 S) (old 4 a) (old 4 b) (old 4 c) (old 4 e) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) Fin.castSucc) (under (.conjL hC) B)
  have hRead : Derives Δ (FormulaTransformHistorySyntax.read (ρ w) (ρ h) (ρ x) (slot 4 2).castSucc (slot 4 3).castSucc (slot 4 0).castSucc (ρ b) (slot 4 1).castSucc (ρ e) (ρ X)) :=
    of_eq (FormulaTransformHistorySyntax.read_rename (old 4 w) (old 4 h) (old 4 x) (slot 4 2) (slot 4 3) (slot 4 0) (old 4 b) (slot 4 1) (old 4 e) (old 4 X) Fin.castSucc) (under (.conjR hC) B)
  have he := InstantiateBinderReadAtLift.read_at_lift_iff hZ2 universal (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S) (ρ h) (ρ x) (ρ X) (slot 4 0).castSucc (slot 4 1).castSucc (slot 4 2).castSucc (slot 4 3).castSucc (Fin.last (m+4)) hw2 hi2 hf2 hn2 hc2 hg2 (.conjR hB) hl
  have hRun := Derives.impE (.conjR he) hRead
  have ho := OriginalBinderStepSyntax.intro_step (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ x) (ρ X) (Fin.last (m+4)) (.conjR hB) hRun
  exact of_eq (by simp only [Formula.raise, OriginalBinderStepSyntax.step_rename]; rfl) ho

theorem step_iff_advanced {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (InstantiateUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    : Derives Γ ((OriginalBinderStepSyntax.step w mode depth P x X).iff
      (FormulaTransformHistorySyntax.advanced w h x R S a b c e X)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact from_step (ZFContext.add hZ _) universal w n mode depth P a b c e R S h x X (add hw _) (add hi _) (add hf _) (add hn _) (add hc _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact to_step (ZFContext.add hZ _) universal w n mode depth P a b c e R S h x X (add hw _) (add hi _) (add hf _) (add hn _) (add hc _) (add hg _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.InstantiateBinderAdvance
