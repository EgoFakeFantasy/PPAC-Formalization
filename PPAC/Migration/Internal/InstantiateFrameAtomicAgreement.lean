import PPAC.Migration.Internal.InstantiateFrameArguments
import PPAC.Migration.Internal.AtomicTermAgreementSyntax
import PPAC.Migration.Internal.MemberPairAgreementSyntax
import PPAC.Migration.Internal.ArgumentPairProgramFields

/-! 任意深度真实frame实际推出原子项及二元参数程序的一致性，所有见证在对象量词内取得。 -/
namespace PPAC.Migration.Internal.InstantiateFrameAtomicAgreement
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem terms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S)) :
    Derives Γ (AtomicTermAgreementSyntax.agreement w mode depth P R S a b c e) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw A)
  have hf2 : Derives Δ (frame w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, frame_rename]) (OrderedPairElimination.under_two hF A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have ho := InstantiateFrameTerm.program_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hf2 hA
  have hm := term_lists w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc hf2
  have hc := AtomicTermAgreementSyntax.checked_iff_run w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hm hA
  exact SyntaxTypeLocalTransfer.iff_trans ho (.conjI (.conjR hc) (.conjL hc))

theorem pair_at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q x y len : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (hLen : Derives Γ (SyntaxNumeralSyntax.numeral 2 len)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentPairProgramSyntax.returned w R S c e x y q)) := by
  have hList := ArgumentForestTyping.list_of_forest hZ 2 w len a b n (SyntaxAtomSyntax.two x y) hw hLen (.conjL (.conjL hT)) hN hT
  have ho := InstantiateFrameArguments.run_iff hZ w mode depth P a b c e R S n q len hw hF hList
  exact SyntaxTypeLocalTransfer.iff_trans ho (ArgumentPairProgramFields.mapped_iff hZ w R S len c e n q x y hw hLen hN)

theorem pair_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentPairProgramSyntax.returned w R S c e x y q)) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxNumerals.exists_numeral hZ 2 w hw)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hf1 := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under hF E)
  have hn1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) n.castSucc) := of_eq (by simp only [SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hN E)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc a.castSucc b.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under hT E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := pair_at_length (ZFContext.under hZ E) w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc n.castSucc q.castSucc x.castSucc y.castSucc (Fin.last m) hw1 hf1 hn1 ht1 (.conjR hE)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, ArgumentPairProgramSyntax.returned_rename]) ho

theorem pair_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b c e R S x y : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ (MemberPairAgreementSyntax.agreement w mode depth P R S c e x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxForestSyntax.forest 2 w.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc) (Fin.last m).castSucc
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw A)
  have hf2 : Derives Δ (frame w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, frame_rename]) (OrderedPairElimination.under_two hF A)
  have ht2 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (OrderedPairElimination.under_two hT A)
  exact pair_iff (ZFContext.under_two hZ A) w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc hw2 hf2 (.hyp (Or.inl rfl)) ht2

end PPAC.Migration.Internal.InstantiateFrameAtomicAgreement
