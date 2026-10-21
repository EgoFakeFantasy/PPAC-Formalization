import PPAC.Migration.GraphDomainExistence

/-! 定义域与并集的外延唯一性及对象等词运输。 -/
namespace PPAC.Migration.GraphDomainAlgebra
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax InsertSyntax GraphDomainSyntax

theorem unique {m} {Γ : Context m} (d e g : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hd : Derives Γ (domain d g)) (hc : Derives Γ (domain e g)) : Derives Γ (.equal d e) := by
  apply Derives.impE (extensionality_instance d e he)
  apply Derives.allI
  have hd' : Derives (Context.image Formula.raise Γ) (domain d.castSucc g.castSucc) := by
    simpa only [Formula.raise, domain_rename] using Derives.rename Fin.castSucc hd
  have hc' : Derives (Context.image Formula.raise Γ) (domain e.castSucc g.castSucc) := by
    simpa only [Formula.raise, domain_rename] using Derives.rename Fin.castSucc hc
  have hdm := domain_at d.castSucc g.castSucc (Fin.last m) hd'
  have hcm := domain_at e.castSucc g.castSucc (Fin.last m) hc'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hcm _)) (.impE (.conjL (add hdm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hdm _)) (.impE (.conjL (add hcm _)) (.hyp (Or.inl rfl)))

theorem subst_graph {m} {Γ : Context m} (d g h : Fin m)
    (he : Derives Γ (.equal g h)) (hd : Derives Γ (domain d g)) : Derives Γ (domain d h) := by
  have hi : Derives Γ ((domain d.castSucc (Fin.last m)).instantiate g) := by
    simpa only [Formula.instantiate, domain_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
  have ho := Derives.eqSubst (domain d.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, domain_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem union_unique {m} {Γ : Context m} (g h f : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (unionOf g f)) (hh : Derives Γ (unionOf h f)) : Derives Γ (.equal g h) := by
  apply Derives.impE (extensionality_instance g h he)
  apply Derives.allI
  have hg' : Derives (Context.image Formula.raise Γ) (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hg
  have hh' : Derives (Context.image Formula.raise Γ) (unionOf h.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hh
  have hgm := union_at g.castSucc f.castSucc (Fin.last m) hg'
  have hhm := union_at h.castSucc f.castSucc (Fin.last m) hh'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hhm _)) (.impE (.conjL (add hgm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hgm _)) (.impE (.conjL (add hhm _)) (.hyp (Or.inl rfl)))
end PPAC.Migration.GraphDomainAlgebra
