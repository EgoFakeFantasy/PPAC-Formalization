import PPAC.Migration.Internal.OriginalUniformInductionSyntax

/-! 全变化参数对象归纳到当前环境及量词提升环境的实际实例化；归纳假设仍待全公式证明消去。 -/
namespace PPAC.Migration.Internal.OriginalUniformInductionRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem prefix_at_frame {m} {Γ : Context m} (three : Bool) (w n mode depth P a b c I J R S : Fin m)
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 2 0) (old 2 n)).conj (FormulaCodeSyntax.formulaCode (old 2 w) (slot 2 0) (old 2 a) (old 2 b))
  let Δ := Context.add G (raisedContext 2 Γ)
  have hi1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three (old 2 w) (old 2 n)) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n (old 2)) (HornBinderRules.under_body 2 hi G)
  have hf1 : Derives Δ (OriginalOperationFrameSyntax.frame three (old 2 w) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 I) (old 2 J) (old 2 R) (old 2 S)) := of_eq (OriginalOperationFrameSyntax.frame_rename three w mode depth P a b c I J R S (old 2)) (HornBinderRules.under_body 2 hf G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hc := OriginalUniformInductionSyntax.allFramesIH_at three (old 2 w) (old 2 n) (slot 2 0) hi1 (.conjL hG)
  have he := OriginalUniformInductionSyntax.correct_at three (old 2 w) (slot 2 0) (old 2 mode) (old 2 depth) (old 2 P) (old 2 a) (old 2 b) (old 2 c) (old 2 I) (old 2 J) (old 2 R) (old 2 S) (slot 2 1) hc hf1 (.conjR hG)
  exact of_eq (by simp only [old, OriginalOperationFrameSyntax.parameter_map]; rfl) he

theorem agreement_at_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S h : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (OrdinalSyntax.ordinal n)) (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) :
    Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth (OriginalOperationFrameSyntax.parameter three P S) h R S a b a c n) :=
  OriginalHistoryFromInduction.from_graph hZ w mode depth (OriginalOperationFrameSyntax.parameter three P S) h R S a b a c n hw hn hg
    (prefix_at_frame three w n mode depth P a b c I J R S hi hf)

theorem agreed_history_at_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.agreedHistory w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n) :=
  OriginalHistoryFromInduction.exists_agreed_history hZ w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n hw hn
    (prefix_at_frame three w n mode depth P a b c I J R S hi hf)

theorem binder_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S A C K H D : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hd : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H)) :
    Derives Γ ((Formula.equal A C).conj ((Formula.equal H S).conj
      (OriginalFormulaInductionSyntax.prefixIH w mode D (OriginalOperationFrameSyntax.parameter three P S) K S A b A c n))) := by
  let B := OriginalOperationFrameSyntax.liftBody three w mode depth P a b c I J R S A C K H D
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (OriginalOperationFrameRules.binder_step hZ three w mode depth P a b c I J R S A C K H D hw hf hd hl)
  have hi1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w.castSucc n.castSucc) := of_eq (OriginalUniformInductionSyntax.allFramesIH_rename three w n Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh := prefix_at_frame three w.castSucc n.castSucc mode.castSucc D.castSucc P.castSucc A.castSucc b.castSucc c.castSucc (Fin.last m) J.castSucc K.castSucc S.castSucc hi1 (.conjR (.conjR (.conjR hB)))
  have ho := Derives.conjI (Derives.conjL (Derives.conjR hB)) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR hB))) hh)
  exact of_eq (by simp only [Formula.raise, Formula.rename, OriginalFormulaInductionSyntax.prefixIH_rename, OriginalOperationFrameSyntax.parameter_map]) ho

end PPAC.Migration.Internal.OriginalUniformInductionRules
