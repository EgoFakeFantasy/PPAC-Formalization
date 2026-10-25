import PPAC.Migration.Internal.PacketReaderReturnCodedSyntax

/-! Equality aligns all four actual source fields and actual source codes without changing original return guards. -/
namespace PPAC.Migration.Internal.PacketReaderReturnTransport
open Source SourceAlgebra SourceLogic PacketReaderReturnSyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem result_L {m} {Γ : Context m} (w B z o L v s a q K : Fin m) (he : Derives Γ (.equal L K))
    (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (result w B z o K v s a q) := by
  let P := result w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) v.castSucc s.castSucc a.castSucc q.castSucc
  have h0 : P.instantiate L = result w B z o L v s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate K = result w B z o K v s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem result_v {m} {Γ : Context m} (w B z o L v s a q V : Fin m) (he : Derives Γ (.equal v V))
    (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (result w B z o L V s a q) := by
  let P := result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m) s.castSucc a.castSucc q.castSucc
  have h0 : P.instantiate v = result w B z o L v s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate V = result w B z o L V s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem result_s {m} {Γ : Context m} (w B z o L v s a q S : Fin m) (he : Derives Γ (.equal s S))
    (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (result w B z o L v S a q) := by
  let P := result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc (Fin.last m) a.castSucc q.castSucc
  have h0 : P.instantiate s = result w B z o L v s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate S = result w B z o L v S a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem result_a {m} {Γ : Context m} (w B z o L v s a q A : Fin m) (he : Derives Γ (.equal a A))
    (hr : Derives Γ (result w B z o L v s a q)) : Derives Γ (result w B z o L v s A q) := by
  let P := result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc (Fin.last m) q.castSucc
  have h0 : P.instantiate a = result w B z o L v s a q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate A = result w B z o L v s A q := by simp only [P,Formula.instantiate,result_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem align_result {m} {Γ : Context m} (w B z o L v s a q K V S A : Fin m)
    (he : Derives Γ (PacketReaderStep.same L v s a K V S A)) (hr : Derives Γ (result w B z o L v s a q)) :
    Derives Γ (result w B z o K V S A q) := by
  have hL := result_L w B z o L v s a q K (.conjL he) hr
  have hV := result_v w B z o K v s a q V (.conjL (.conjR he)) hL
  have hS := result_s w B z o K V s a q S (.conjL (.conjR (.conjR he))) hV
  exact result_a w B z o K V S a q A (.conjR (.conjR (.conjR he))) hS

theorem coded_source {m} {Γ : Context m} (w B z o n r q : Fin m) (he : Derives Γ (.equal n r))
    (hr : Derives Γ (coded w B z o n q)) : Derives Γ (coded w B z o r q) := by
  let P := coded w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc
  have h0 : P.instantiate n = coded w B z o n q := by simp only [P,Formula.instantiate,coded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate r = coded w B z o r q := by simp only [P,Formula.instantiate,coded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

end PPAC.Migration.Internal.PacketReaderReturnTransport
