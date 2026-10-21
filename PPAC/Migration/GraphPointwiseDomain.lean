import PPAC.Migration.GraphPointwise

/-! 完整functionOn给出实际边定义域及定义域唯一性。 -/
namespace PPAC.Migration.GraphPointwiseDomain
open Source SourceAlgebra SourceLogic GraphSyntax GraphDomainSyntax

theorem domain_of_hasEdge {m} {Γ : Context m} (f d x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hx : Derives Γ (hasEdge f x)) : Derives Γ (.mem x d) := by
  let Y := edge f.castSucc x.castSucc (Fin.last m)
  let Γy := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have heY : Derives Γy (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Y
  have hfY : Derives Γy (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf Y
  exact GraphProperties.domain_of_edge f.castSucc d.castSucc x.castSucc (Fin.last m) heY hfY (.hyp (Or.inl rfl))

theorem from_function {m} {Γ : Context m} (f d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) : Derives Γ (domain d f) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives (Context.image Formula.raise Γ) (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  apply Derives.conjI
  · apply Derives.impI
    exact GraphProperties.output_exists f.castSucc d.castSucc (Fin.last m) (add hf' _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact domain_of_hasEdge f.castSucc d.castSucc (Fin.last m) (add he' _) (add hf' _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (f d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn f e)) : Derives Γ (.equal d e) :=
  GraphDomainAlgebra.unique d e f he (from_function f d he hf) (from_function f e he hg)
end PPAC.Migration.GraphPointwiseDomain
