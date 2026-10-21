import PPAC.Migration.GraphDomainBound

/-! 两次原Union与一个原Separation实例实际构造任意图定义域。 -/
namespace PPAC.Migration.GraphDomainExistence
open Source SourceAlgebra SourceLogic GraphSyntax InsertSyntax GraphDomainSyntax GraphDomainBound

theorem from_separated {m} {Γ : Context m} (d g u v : Fin m)
    (hu : Derives Γ (unionOf u g)) (hv : Derives Γ (unionOf v u))
    (hs : Derives Γ (separated d v g)) : Derives Γ (domain d g) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf u.castSucc g.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hv' : Derives (Context.image Formula.raise Γ) (unionOf v.castSucc u.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hv
  have hs' : Derives (Context.image Formula.raise Γ) (separated d.castSucc v.castSucc g.castSucc) := by
    simpa only [Formula.raise, separated_rename] using Derives.rename Fin.castSucc hs
  have hsm := separated_at d.castSucc v.castSucc g.castSucc (Fin.last m) hs'
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (.conjL (add hsm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let E := hasEdge g.castSucc (Fin.last m)
    have he : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
    have hb := input_bound g.castSucc u.castSucc v.castSucc (Fin.last m) (add hu' E) (add hv' E) he
    exact .impE (.conjR (add hsm E)) (.conjI hb he)

theorem exists_domain {m} {Γ : Context m} (g : Fin m)
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) : Derives Γ (domainExists g) := by
  have hU := union_instance g hu
  let U := unionOf (Fin.last m) g.castSucc
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hU
  apply Derives.exE (p := U) hU
  have resultU : Derives Γu (domainExists g.castSucc) := by
    have huU : Derives Γu U := .hyp (Or.inl rfl)
    have hUnionU : Derives Γu (Source.SetLanguage.union.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hu U
    have hsU : Derives Γu ((Source.SetLanguage.separation matrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hs U
    have hV := union_instance (Fin.last m) hUnionU
    let V := unionOf (Fin.last (m+1)) (Fin.last m).castSucc
    let Γv := Context.add V (Context.image Formula.raise Γu)
    change Derives Γu (.ex V) at hV
    apply Derives.exE (p := V) hV
    have resultV : Derives Γv (domainExists g.castSucc.castSucc) := by
      have huV : Derives Γv (unionOf (Fin.last m).castSucc g.castSucc.castSucc) := by
        simpa only [Formula.raise, U, unionOf_rename] using under huU V
      have hvV : Derives Γv V := .hyp (Or.inl rfl)
      have hsV : Derives Γv ((Source.SetLanguage.separation matrix).rename Fin.elim0) := by
        simpa only [Formula.raise, closed_rename] using under hsU V
      have hD := separate_domain (Fin.last (m+1)) g.castSucc.castSucc hsV
      let D := separated (Fin.last (m+2)) (Fin.last (m+1)).castSucc g.castSucc.castSucc.castSucc
      let Γd := Context.add D (Context.image Formula.raise Γv)
      change Derives Γv (.ex D) at hD
      apply Derives.exE (p := D) hD
      have resultD : Derives Γd (domainExists g.castSucc.castSucc.castSucc) := by
        have huD : Derives Γd (unionOf (Fin.last m).castSucc.castSucc g.castSucc.castSucc.castSucc) := by
          simpa only [Formula.raise, unionOf_rename] using under huV D
        have hvD : Derives Γd (unionOf (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc) := by
          simpa only [Formula.raise, V, unionOf_rename] using under hvV D
        have hsD : Derives Γd D := .hyp (Or.inl rfl)
        have hd := from_separated (Fin.last (m+2)) g.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc huD hvD hsD
        apply Derives.exI (Fin.last (m+2))
        simpa only [Formula.instantiate, domain_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd
      simpa only [Formula.raise, domainExists_rename] using resultD
    simpa only [Formula.raise, domainExists_rename] using resultV
  simpa only [Formula.raise, domainExists_rename] using resultU
end PPAC.Migration.GraphDomainExistence
