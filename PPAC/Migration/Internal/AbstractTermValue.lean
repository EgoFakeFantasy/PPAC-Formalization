import PPAC.Migration.Internal.AbstractTermValueSyntax

/-! 全部纯项的原mode1运行与独立内部数值关系；类型守卫位于结论内部。 -/
namespace PPAC.Migration.Internal.AbstractTermValue
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractTermValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_scope_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w mode depth P limit n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hb : Derives Γ (SyntaxTermSyntax.branch bound w limit n))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth P n q)) :
    Derives Γ (branch bound w limit depth n q) := by
  let B := SyntaxTermSyntax.branchWitness bound w limit n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch bound w limit n _ hb
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under hm B)
  have hd1 := of_eq (OriginalTermTraceSyntax.metadata_rename w depth P Fin.castSucc) (under hd B)
  have hr1 := of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth P n q Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hval := Derives.impE (.conjL (AbstractVariableRun.run_iff (ZFContext.under hZ B) bound w.castSucc mode.castSucc depth.castSucc P.castSucc n.castSucc (Fin.last m) q.castSucc hw1 hm1 hd1 (.conjR hB))) hr1
  have ho := intro_branch bound _ _ _ _ _ _ (.conjL hB) (.conjR hB) hval
  exact of_eq (branch_rename bound w limit depth n q Fin.castSucc).symm ho

theorem branch_to_run {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w mode depth P limit n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hb : Derives Γ (branch bound w limit depth n q)) :
    Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth P n q) := by
  let B := (Formula.mem (Fin.last m) limit.castSucc).conj
    ((SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc).conj
      (AbstractVariableValueSyntax.valueSpec bound w.castSucc depth.castSucc (Fin.last m) n.castSucc q.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under hm B)
  have hd1 := of_eq (OriginalTermTraceSyntax.metadata_rename w depth P Fin.castSucc) (under hd B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := AbstractVariableRun.run_iff (ZFContext.under hZ B) bound w.castSucc mode.castSucc depth.castSucc P.castSucc n.castSucc (Fin.last m) q.castSucc hw1 hm1 hd1 (.conjL (.conjR hB))
  exact of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth P n q Fin.castSucc).symm (.impE (.conjR he) (.conjR (.conjR hB)))

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P)) :
    Derives Γ (((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff (value w a b depth n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    apply Derives.conjI (.conjL (.conjL hE))
    apply Derives.disjE (.conjR (.conjL hE))
    · exact .disjL (from_scope_branch (ZFContext.add (ZFContext.add hZ E) _) true _ _ _ _ _ _ _
        (add (add hw E) _) (add (add hm E) _) (add (add hd E) _) (.hyp (Or.inl rfl)) (add (.conjR hE) _))
    · exact .disjR (from_scope_branch (ZFContext.add (ZFContext.add hZ E) _) false _ _ _ _ _ _ _
        (add (add hw E) _) (add (add hm E) _) (add (add hd E) _) (.hyp (Or.inl rfl)) (add (.conjR hE) _))
  · apply Derives.impI
    let E := value w a b depth n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hctx := Derives.conjL hE
    have hbranches := Derives.conjR hE
    apply Derives.disjE hbranches
    · let F := branch true w a depth n q
      let Δ0 := Context.add F (Context.add E Γ)
      have hF : Derives Δ0 F := .hyp (Or.inl rfl)
      have hrun := branch_to_run (ZFContext.add (ZFContext.add hZ E) F) true w mode depth P a n q
        (add (add hw E) F) (add (add hm E) F) (add (add hd E) F) hF
      have hscope : Derives Δ0 (SyntaxTermSyntax.branch true w a n) := by
        let B := (Formula.mem (Fin.last m) a.castSucc).conj
          ((SyntaxVariableSyntax.code true w.castSucc (Fin.last m) n.castSucc).conj
            (AbstractVariableValueSyntax.valueSpec true w.castSucc depth.castSucc (Fin.last m) n.castSucc q.castSucc))
        let Δ := Context.add B (Context.image Formula.raise Δ0)
        apply Derives.exE (p := B) hF
        have hB : Derives Δ B := .hyp (Or.inl rfl)
        have ho := SyntaxTermSyntax.intro_branch true _ _ _ _ (.conjL hB) (.conjL (.conjR hB))
        exact of_eq (SyntaxTermSyntax.branch_rename true w a n Fin.castSucc).symm ho
      exact .conjI (.conjI (add hctx F) (.disjL hscope)) hrun
    · let F := branch false w b depth n q
      let Δ0 := Context.add F (Context.add E Γ)
      have hF : Derives Δ0 F := .hyp (Or.inl rfl)
      have hrun := branch_to_run (ZFContext.add (ZFContext.add hZ E) F) false w mode depth P b n q
        (add (add hw E) F) (add (add hm E) F) (add (add hd E) F) hF
      have hscope : Derives Δ0 (SyntaxTermSyntax.branch false w b n) := by
        let B := (Formula.mem (Fin.last m) b.castSucc).conj
          ((SyntaxVariableSyntax.code false w.castSucc (Fin.last m) n.castSucc).conj
            (AbstractVariableValueSyntax.valueSpec false w.castSucc depth.castSucc (Fin.last m) n.castSucc q.castSucc))
        let Δ := Context.add B (Context.image Formula.raise Δ0)
        apply Derives.exE (p := B) hF
        have hB : Derives Δ B := .hyp (Or.inl rfl)
        have ho := SyntaxTermSyntax.intro_branch false _ _ _ _ (.conjL hB) (.conjL (.conjR hB))
        exact of_eq (SyntaxTermSyntax.branch_rename false w b n Fin.castSucc).symm ho
      exact .conjI (.conjI (add hctx F) (.disjR hscope)) hrun

theorem typed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P a b n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P)) (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (value w a b depth n q)) := by
  have he := guarded_iff hZ w mode depth P a b n q hw hm hd
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL he) _) (.conjI (add ht _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjR (.impE (add (.conjR he) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.AbstractTermValue
