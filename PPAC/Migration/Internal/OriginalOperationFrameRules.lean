import PPAC.Migration.Internal.OriginalOperationFrameSyntax

/-! 实际模式环境的旧接口适用性、原子程序对应及量词提升闭包；不假定一般混合项像表稳定。 -/
namespace PPAC.Migration.Internal.OriginalOperationFrameRules
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open OriginalOperationFrameSyntax

theorem free_converted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame three w mode depth P a b c I J R S)) :
    Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a c) := by
  have hb := IndexTermImageCodeTyping.input_of_converted true w I R a a c (bound_conversion three w mode depth P a b c I J R S hF)
  exact FreeSubstImageCode.same_code hZ w b a c S J hw (.conjL (.conjL hb)) (free_conversion three w mode depth P a b c I J R S hF)

theorem environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame three w mode depth P a b c I J R S)) :
    Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b a c) :=
  .conjI (bound_conversion three w mode depth P a b c I J R S hF) (free_converted hZ three w mode depth P a b c I J R S hw hF)

theorem from_weaken {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c I J R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P)) (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hs : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b c J))
    (hr : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (ht : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a c)) :
    Derives Γ (frame false w mode depth P a b c I J R S) :=
  intro_frame false w mode depth P a b c I J R S hm hd hi (OriginalFreeImageConversion.from_converted hZ w J S b a c hw ht) hr hs

theorem from_replace {m} {Γ : Context m} (w mode depth P a b c I J R S : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode)) (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth S))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hf : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c S J))
    (hr : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c)) :
    Derives Γ (frame true w mode depth P a b c I J R S) :=
  intro_frame true w mode depth P a b c I J R S hm hd hi hf hr (.eqRefl w)

theorem atomic_program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth P a b c I J R S h n q : Fin m) (hw : Derives Γ (omega w))
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) (hn : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (parameter three P S) n q).iff
      (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b a c h n q)) := by
  have hm := mode_number three w mode depth P a b c I J R S hF
  have hd := metadata three w mode depth P a b c I J R S hF
  have hi := identity three w mode depth P a b c I J R S hF
  have hr := bound_conversion three w mode depth P a b c I J R S hF
  have hs := free_converted hZ three w mode depth P a b c I J R S hw hF
  cases three with
  | false => exact OriginalAtomicProgram.weaken_program_iff hZ w mode depth P a b c I J R S h n q hw hm hd hi (guard_data false w mode depth P a b c I J R S hF) hr hs hn
  | true => exact OriginalAtomicProgram.replace_program_iff hZ w mode depth a b c S I R h n q hw hm hd hi hr (IndexTermImageCodeTyping.term_list false w J S b a c hs) hn

theorem binder_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth P a b c I J R S A C M K H D : Fin m) (hw : Derives Γ (omega w))
    (hF : Derives Γ (frame three w mode depth P a b c I J R S))
    (hd : Derives Γ (successor D depth))
    (ho : Derives Γ (SyntaxMapLiftSyntax.codedLift w a a I A C M))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H)) :
    Derives Γ ((Formula.equal A C).conj ((Formula.equal H S).conj (frame three w mode D P A b c M J K S))) := by
  have hh := FreeSubstProgramBinder.lifted_environment hZ w a b c S I J R A C M K H hw (environment hZ three w mode depth P a b c I J R S hw hF)
    (identity three w mode depth P a b c I J R S hF) (free_conversion three w mode depth P a b c I J R S hF) ho hl
  have hn := metadata three w mode depth P a b c I J R S hF
  have hD := OmegaStructureAlgebra.successor_member w D depth (ZFContext.arithmetic hZ).base.extensionality hw (.conjL hn) hd
  have ht := intro_frame three w mode D P A b c M J K S (mode_number three w mode depth P a b c I J R S hF)
    (.conjI hD (.conjR hn)) (.conjL (.conjR hh)) (free_conversion three w mode depth P a b c I J R S hF)
    (.conjL (.conjR (.conjR (.conjR hh)))) (guard_data three w mode depth P a b c I J R S hF)
  exact .conjI (.conjL hh) (.conjI (.conjL (.conjR (.conjR hh))) ht)

theorem binder_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth P a b c I J R S A C K H D : Fin m) (hw : Derives Γ (omega w))
    (hF : Derives Γ (frame three w mode depth P a b c I J R S))
    (hd : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H)) :
    Derives Γ (liftedFrame three w mode depth P a b c I J R S A C K H D) := by
  have hi := identity three w mode depth P a b c I J R S hF
  have hc := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b a c A C K H hl
  let B := SyntaxMapLiftSyntax.codedLift w.castSucc a.castSucc a.castSucc I.castSucc A.castSucc C.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxMapLift.exists_code hZ w a a I A C hw (SyntaxIdentityCode.map_code w a I hi) (.conjL (.conjR hc)) (.conjR (.conjR hc)))
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hf1 : Derives Δ (frame three w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc I.castSucc J.castSucc R.castSucc S.castSucc) := of_eq (frame_rename three w mode depth P a b c I J R S Fin.castSucc) (under hF B)
  have hd1 : Derives Δ (successor D.castSucc depth.castSucc) := of_eq (successor_rename D depth Fin.castSucc) (under hd B)
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc a.castSucc c.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b a c A C K H Fin.castSucc) (under hl B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := binder_at (ZFContext.under hZ B) three w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc I.castSucc J.castSucc R.castSucc S.castSucc A.castSucc C.castSucc (Fin.last m) K.castSucc H.castSucc D.castSucc hw1 hf1 hd1 hB hl1
  have ht := intro_liftedFrame three w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc I.castSucc J.castSucc R.castSucc S.castSucc A.castSucc C.castSucc K.castSucc H.castSucc D.castSucc (Fin.last m) hB he
  exact of_eq (liftedFrame_rename three w mode depth P a b c I J R S A C K H D Fin.castSucc).symm ht

end PPAC.Migration.Internal.OriginalOperationFrameRules
