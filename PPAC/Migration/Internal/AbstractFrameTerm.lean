import PPAC.Migration.Internal.AbstractOperationFrameBinder
import PPAC.Migration.Internal.OriginalTermScopeElimination
import PPAC.Migration.Internal.TermTransformProgramCorrectness

/-! 任意内部深度的真实兼容frame把原Run1接到独立纯项程序及原混合项操作。 -/
namespace PPAC.Migration.Internal.AbstractFrameTerm
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w mode depth P a b c e R S n q i : Fin m) (hw : Derives Γ (omega w))
    (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  have hr := AbstractVariableRun.run_iff hZ bound w mode depth P n i q hw
    (mode_number w mode depth P a b c e R S hF) (metadata w mode depth P a b c e R S hF) hv
  have hf := compatible_at bound w depth a b R S i n q (variables bound w mode depth P a b c e R S hF) hi hv
  have hp := TermTransformProgramVariable.at_variable hZ bound w R S n q i hw hv
  exact SyntaxTypeLocalTransfer.iff_trans hr (SyntaxTypeLocalTransfer.iff_trans hf (.conjI (.conjR hp) (.conjL hp)))

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  apply OriginalTermScopeElimination.eliminate w a b n _ ht
  intro bound
  let D := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) n
  let Δ := Context.add D (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have hf1 := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under hF D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hb : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)).conj
      (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc)) :=
    of_eq (by simp only [D, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hD
  have ho := at_variable hZ1 bound w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc n.castSucc q.castSucc (Fin.last m)
    hw1 hf1 (.conjL hb) (.conjR hb)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.run_rename]) ho

theorem coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff
      (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (program_iff hZ w mode depth P a b c e R S n q hw hF ht)
    (TermTransformProgramCorrectness.at_typed_term hZ w R S a b c e n q hw (term_lists w mode depth P a b c e R S hF) ht)

theorem guarded_coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff
      (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .impE (.conjL (coded_iff (ZFContext.add hZ E) w mode depth P a b c e R S n q (add hw E) (add hF E) (.conjL hE))) (.conjR hE)
  · apply Derives.impI
    let E := SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have ht := SyntaxCodedMixedTermTyping.source_type w R S a b c e n q hE
    exact .conjI ht (.impE (.conjR (coded_iff (ZFContext.add hZ E) w mode depth P a b c e R S n q (add hw E) (add hF E) ht)) hE)

end PPAC.Migration.Internal.AbstractFrameTerm
