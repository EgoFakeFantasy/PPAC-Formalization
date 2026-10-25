import PPAC.Migration.Internal.PacketReaderEvalSyntax

/-! Genuine reader recursion equations on actual four-field states; all intermediate state-code witnesses are constructed and eliminated. -/
namespace PPAC.Migration.Internal.PacketReaderEval
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderEvalSyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a q n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) :
    Derives Γ ((eval w B z o L v s a q).iff (run w B z o n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := eval w B z o L v s a q
    let R := (PacketReaderStateSyntax.code w.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)).conj (run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hc1 := of_eq (PacketReaderStateSyntax.code_rename w L v s a n Fin.castSucc) (under (add hc H) R)
    have heq := PacketReaderStateCode.unique hZ1 _ _ _ _ _ _ _ hw1 (.conjL hR) hc1
    simpa only [Formula.raise,run_rename] using PacketReaderInitSeeded.run_source _ _ _ _ _ _ _ heq (.conjR hR)
  · apply Derives.impI
    exact intro_eval _ _ _ _ _ _ _ _ _ _ (add hc _) (.hyp (Or.inl rfl))

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a X y S c q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (ht : Derives Γ (PacketReaderInputSyntax.advance w B z o L v s a X y S c)) :
    Derives Γ ((eval w B z o L v s a q).iff (eval w B z o X y S c q)) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hTarget := PacketReaderInputStep.domain hZ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hzN ho ht
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (PacketReaderStateSyntax.code w.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderStateCode.exists_code hZ _ _ _ _ _ hw (.conjL ht))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hTarget1 := of_eq (PacketReaderStepSyntax.state_rename w X y S c Fin.castSucc) (under hTarget R)
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PacketReaderStateSyntax.code w.castSucc.castSucc X.castSucc.castSucc y.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) (PacketReaderStateCode.exists_code hZ1 _ _ _ _ _ hw1 hTarget1)
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 T
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
  have hc2 := of_eq (PacketReaderStateSyntax.code_rename w.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
  have ht2 : Derives Ξ (PacketReaderInputSyntax.advance w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc X.castSucc.castSucc y.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise,PacketReaderInputSyntax.advance_rename]) (under (under ht R) T)
  have hz2 : Derives Ξ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise,empty_rename]) (under (under hz R) T)
  have hStep := PacketReaderCodedSyntax.intro_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc2 (.conjR hT) ht2
  have hRun := PacketReaderRunStep.step_iff hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc hw2 (under (under hB R) T) hz2 (under (under ho R) T) hStep
  have hLeft := at_code hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc hw2 hc2
  have hRight := at_code hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc X.castSucc.castSucc y.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc q.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjR hT)
  simpa only [Formula.raise,Formula.rename,eval_rename] using StructuralListSuffixArithmetic.iff_trans (StructuralListSuffixArithmetic.iff_trans hLeft hRun) (Derives.conjI (.conjR hRight) (.conjL hRight))

theorem at_terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (ht : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a)) :
    Derives Γ ((eval w B z o L v s a q).iff (PacketReaderReturnSyntax.result w B z o L v s a q)) := by
  have hState : Derives Γ (PacketReaderStepSyntax.state w L v s a) := by
    apply Derives.disjE ht
    · exact .conjL (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .conjL (.hyp (Or.inl rfl))
      · exact .conjL (.hyp (Or.inl rfl))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (PacketReaderStateSyntax.code w.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderStateCode.exists_code hZ _ _ _ _ _ hw hState)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho R)
  have ht1 := of_eq (PacketReaderTerminalSyntax.raw_rename w B z o L v s a Fin.castSucc) (under ht R)
  have hLeft := at_code hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc q.castSucc (Fin.last m) hw1 (.conjR hR)
  have hRight := PacketReaderTerminalZero.at_terminal hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m) q.castSucc hw1 (under hB R) hz1 ho1 (.conjR hR) ht1
  simpa only [Formula.raise,Formula.rename,eval_rename,PacketReaderReturnSyntax.result_rename] using StructuralListSuffixArithmetic.iff_trans hLeft hRight

end PPAC.Migration.Internal.PacketReaderEval
