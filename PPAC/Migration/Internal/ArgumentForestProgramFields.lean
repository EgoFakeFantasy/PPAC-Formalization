import PPAC.Migration.Internal.ArgumentForestTyping

/-! 原全内部字段像规格在实际有限森林处恰好是独立项程序逐参数运行。 -/
namespace PPAC.Migration.Internal.ArgumentForestProgramFields
open Source SourceAlgebra SourceLogic OmegaSyntax ArgumentForestProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxForestSyntax SyntaxNumeralSyntax

theorem runs_of_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w R S l n q : Fin m) (xs ys : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hn : Derives Γ (forest k w xs n)) (hq : Derives Γ (forest k w ys q))
    (hh : Derives Γ (ArgumentProgramFieldSyntax.fields w R S l n q)) : Derives Γ (runs k w R S xs ys) := by
  apply intro_runs
  intro j
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (numeral j.val (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ j.val w hw)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hl1 : Derives Δ (numeral k l.castSucc) := of_eq (numeral_rename k l Fin.castSucc) (under hl B)
  have hn1 : Derives Δ (forest k w.castSucc (fun t => (xs t).castSucc) n.castSucc) := of_eq (forest_rename k w xs n Fin.castSucc) (under hn B)
  have hq1 : Derives Δ (forest k w.castSucc (fun t => (ys t).castSucc) q.castSucc) := of_eq (forest_rename k w ys q Fin.castSucc) (under hq B)
  have hh1 : Derives Δ (ArgumentProgramFieldSyntax.fields w.castSucc R.castSucc S.castSucc l.castSucc n.castSucc q.castSucc) := of_eq (ArgumentProgramFieldSyntax.fields_rename w R S l n q Fin.castSucc) (under hh B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hIndex := SyntaxNumeralMembers.index_member hZ1 k j l.castSucc (Fin.last m) hl1 (.conjR hB)
  have hNField := Derives.impE (.conjR (SyntaxForestFieldValues.field_at hZ1 k w.castSucc (fun t => (xs t).castSucc) n.castSucc j (Fin.last m) (xs j).castSucc hw1 hn1 (.conjR hB))) (.eqRefl _)
  have hQField := Derives.impE (.conjR (SyntaxForestFieldValues.field_at hZ1 k w.castSucc (fun t => (ys t).castSucc) q.castSucc j (Fin.last m) (ys j).castSucc hw1 hq1 (.conjR hB))) (.eqRefl _)
  have ho := ArgumentProgramFieldSyntax.fields_at _ _ _ _ _ _ _ _ _ hh1 hIndex hNField hQField
  exact of_eq (TermTransformProgramSyntax.run_rename _ w R S (xs j) (ys j) Fin.castSucc).symm ho

theorem fields_of_runs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w R S l n q : Fin m) (xs ys : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hn : Derives Γ (forest k w xs n)) (hq : Derives Γ (forest k w ys q))
    (hh : Derives Γ (runs k w R S xs ys)) : Derives Γ (ArgumentProgramFieldSyntax.fields w R S l n q) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc.castSucc l.castSucc.castSucc.castSucc).conj
    ((StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ A
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise.raise := SyntaxAtomLogic.under_three h A
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hl3 : Derives Δ (numeral k l.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, numeral_rename]) (lift hl)
  have hn3 : Derives Δ (forest k w.castSucc.castSucc.castSucc (fun t => (xs t).castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, forest_rename]) (lift hn)
  have hq3 : Derives Δ (forest k w.castSucc.castSucc.castSucc (fun t => (ys t).castSucc.castSucc.castSucc) q.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, forest_rename]) (lift hq)
  have hh3 : Derives Δ (runs k w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (fun t => (xs t).castSucc.castSucc.castSucc) (fun t => (ys t).castSucc.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, runs_rename]) (lift hh)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hb := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ3 k _ _ hl3)) (.conjL hA)
  have hi : Derives Δ ((SyntaxPositionSyntax.below k (Fin.last m).castSucc.castSucc).imp
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))) := by
    apply SyntaxPositionSyntax.below_imp
    intro j
    apply Derives.impI
    let J := numeral j.val (Fin.last m).castSucc.castSucc
    have hJ : Derives (Context.add J Δ) J := .hyp (Or.inl rfl)
    have heN := Derives.impE (.conjL (SyntaxForestFieldValues.field_at (ZFContext.add hZ3 J) k _ (fun t => (xs t).castSucc.castSucc.castSucc) _ j _ _ (add hw3 J) (add hn3 J) hJ)) (add (.conjL (.conjR hA)) J)
    have heQ := Derives.impE (.conjL (SyntaxForestFieldValues.field_at (ZFContext.add hZ3 J) k _ (fun t => (ys t).castSucc.castSucc.castSucc) _ j _ _ (add hw3 J) (add hq3 J) hJ)) (add (.conjR (.conjR hA)) J)
    have hRun := add (run_at k _ _ _ _ _ hh3 j) J
    exact run_output_subst _ _ _ _ _ _ (eq_symm heQ) (run_input_subst _ _ _ _ _ _ (eq_symm heN) hRun)
  exact .impE hi hb

theorem fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w R S l n q : Fin m) (xs ys : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hn : Derives Γ (forest k w xs n)) (hq : Derives Γ (forest k w ys q)) :
    Derives Γ ((ArgumentProgramFieldSyntax.fields w R S l n q).iff (runs k w R S xs ys)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact runs_of_fields (ZFContext.add hZ _) k w R S l n q xs ys (add hw _) (add hl _) (add hn _) (add hq _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact fields_of_runs (ZFContext.add hZ _) k w R S l n q xs ys (add hw _) (add hl _) (add hn _) (add hq _) (.hyp (Or.inl rfl))

theorem mapped_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w R S l c d n q : Fin m) (xs ys : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hl : Derives Γ (numeral k l)) (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hn : Derives Γ (forest k w xs n)) (hq : Derives Γ (forest k w ys q)) :
    Derives Γ ((ArgumentProgramFieldSyntax.mapped w R S l c d n q).iff
      ((typedInputs k w c d ys).conj (runs k w R S xs ys))) :=
  FormulaCodeCongruence.conj_congr (ArgumentForestTyping.list_iff hZ k w l c d q ys hw hl hc hq)
    (fields_iff hZ k w R S l n q xs ys hw hl hn hq)

end PPAC.Migration.Internal.ArgumentForestProgramFields
