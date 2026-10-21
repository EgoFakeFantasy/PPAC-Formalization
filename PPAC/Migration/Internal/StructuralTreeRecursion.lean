import PPAC.Migration.Internal.StructuralTreeCanonical

/-! 无标志参数的树递归双条件；字段有效性量化所有内部字段码。 -/
namespace PPAC.Migration.Internal.StructuralTreeRecursion
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralTreeValiditySyntax
open StructuralTreeRecursiveSyntax (acceptedChildren acceptedChildren_rename branch branchBody branch_rename)
open StructuralTreeOperatorSyntax (shape shape_rename)
open StructuralListLengthSyntax (under_four zf_under_four)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem valid_children_of_accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n tag p l f : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hs : Derives Γ (shape w n tag p l f)) (ha : Derives Γ (acceptedChildren w z e f)) : Derives Γ (validChildren w f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ E
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := OrderedPairElimination.under_two hq E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift he
  have hs2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc tag.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, shape_rename] using lift hs
  have ha2 : Derives Δ (acceptedChildren w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, acceptedChildren_rename] using lift ha
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hb := StructuralTreeOperatorLogic.shape_edge_bound hZ2 _ _ _ _ _ _ _ _ hw2 hs2 hE
  have hn := StructuralNodeProperties.range hZ2 _ _ _ _ hw2 (.conjR (.conjL hs2))
  have hy := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 hn hb
  exact intro_valid _ _ _ _ hy hz2 he2 (StructuralTreeRecursiveSyntax.accepted_at _ _ _ _ _ _ ha2 hE)

theorem accepted_children_of_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e f : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hv : Derives Γ (validChildren w f)) : Derives Γ (acceptedChildren w z e f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ E
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := OrderedPairElimination.under_two hq E
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift he
  have hv2 : Derives Δ (validChildren w.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, validChildren_rename] using lift hv
  exact StructuralTreeCanonical.valid_to_accepts hZ2 _ _ _ _ hz2 he2 (validChildren_at _ _ _ _ hv2 (.hyp (Or.inl rfl)))

theorem recursive_of_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hb : Derives Γ (branch w z e n)) : Derives Γ (recursive w n) := by
  let B := branchBody w z e n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply StructuralTreeRecursiveSyntax.eliminate_branch w z e n _ hb
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw B
  have hz4 : Derives Δ (empty z.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using under_four hz B
  have he4 : Derives Δ (successor e.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under_four he B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv := valid_children_of_accepted hZ4 _ _ _ _ _ _ _ _ hw4 hz4 he4 (.conjL hB) (.conjR hB)
  have hout := intro_recursive _ _ _ _ _ _ (.conjI (.conjL hB) hv)
  simpa only [Formula.raise, recursive_rename] using hout

theorem branch_of_recursive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hr : Derives Γ (recursive w n)) : Derives Γ (branch w z e n) := by
  let B := dataBody w n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_recursive w n _ hr
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ B
  have hz4 : Derives Δ (empty z.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using under_four hz B
  have he4 : Derives Δ (successor e.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under_four he B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := accepted_children_of_valid hZ4 _ _ _ _ hz4 he4 (.conjR hB)
  have hout := StructuralTreeRecursiveSyntax.intro_branch _ _ _ _ _ _ _ _ (.conjL hB) ha
  simpa only [Formula.raise, branch_rename] using hout

theorem valid_iff_recursive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((valid w n).iff (recursive w n)) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hn U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have ho := NaturalOrderBasic.ordinal hZ2 _ _ hw2 hn2
  have hout : Derives Δ ((valid w.castSucc.castSucc n.castSucc.castSucc).iff (recursive w.castSucc.castSucc n.castSucc.castSucc)) := by
    apply Derives.conjI
    · apply Derives.impI
      have hV : Derives (Context.add (valid w.castSucc.castSucc n.castSucc.castSucc) Δ) (valid w.castSucc.castSucc n.castSucc.castSucc) := .hyp (Or.inl rfl)
      have ha := StructuralTreeCanonical.valid_to_accepts (ZFContext.add hZ2 _) _ _ _ _ (add (.conjL hU) _) (add (.conjR hU) _) hV
      have hb := StructuralTreeCheck.accepts_branch (ZFContext.add hZ2 _) _ _ _ _ (add (.conjL hU) _) (add (.conjR hU) _) (add ho _) ha
      exact recursive_of_branch (ZFContext.add hZ2 _) _ _ _ _ (add hw2 _) (add (.conjL hU) _) (add (.conjR hU) _) hb
    · apply Derives.impI
      have hR : Derives (Context.add (recursive w.castSucc.castSucc n.castSucc.castSucc) Δ) (recursive w.castSucc.castSucc n.castSucc.castSucc) := .hyp (Or.inl rfl)
      have hb := branch_of_recursive (ZFContext.add hZ2 _) _ _ _ _ (add (.conjL hU) _) (add (.conjR hU) _) hR
      have ha := StructuralTreeCheck.branch_accepts (ZFContext.add hZ2 _) _ _ _ _ (add hw2 _) (add ho _) hb
      exact intro_valid _ _ _ _ (add hn2 _) (add (.conjL hU) _) (add (.conjR hU) _) ha
  simpa only [Formula.raise, Formula.rename, valid_rename, recursive_rename] using hout

theorem valid_to_recursive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (recursive w n) :=
  .impE (.conjL (valid_iff_recursive hZ w n hw (.conjL hv))) hv
end PPAC.Migration.Internal.StructuralTreeRecursion
