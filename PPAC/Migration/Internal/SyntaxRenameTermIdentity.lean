import PPAC.Migration.Internal.SyntaxRenameTermKnown

/-! 实际对角索引图上的项重命名恒等律，不假定图由宿主identity函数给出。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermIdentity
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def diagonal {m} (r : Fin m) : Formula m := .all (.all
  ((edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (.equal (Fin.last m).castSucc (Fin.last (m+1)))))

theorem diagonal_rename {m k} (r : Fin m) (ρ : Fin m → Fin k) :
    (diagonal r).rename ρ = diagonal (ρ r) := by
  simp only [diagonal, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem diagonal_at {m} {Γ : Context m} (r i j : Fin m) (hh : Derives Γ (diagonal r))
    (he : Derives Γ (edge r i j)) : Derives Γ (.equal i j) := by
  have hi := Derives.allE j (Derives.allE i hh)
  have h : Derives Γ ((edge r i j).imp (.equal i j)) := by
    simpa only [diagonal, Formula.instantiate, Formula.rename, edge_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE h he

theorem branch_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a n q : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (diagonal r)) (hh : Derives Γ (branch bound w r a n q)) :
    Derives Γ (.equal n q) := by
  let B := branchBody bound w r a n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_branch bound w r a n q _ hh
  have hZ2 := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hd2 : Derives Δ (diagonal r.castSucc.castSucc) := by
    simpa only [Formula.raise, diagonal_rename] using OrderedPairElimination.under_two hd B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hij := diagonal_at _ _ _ hd2 (.conjL (.conjR hB))
  have hn := code_index_subst bound _ _ _ _ hij (.conjL (.conjR (.conjR hB)))
  exact SyntaxVariables.unique hZ2 bound _ _ _ _ hw2 hn (.conjR (.conjR (.conjR hB)))

theorem identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (diagonal r)) (hs : Derives Γ (diagonal s))
    (hh : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (.equal n q) := by
  apply Derives.disjE (.conjR hh)
  · exact branch_identity (ZFContext.add hZ _) true w r a n q (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact branch_identity (ZFContext.add hZ _) false w s b n q (add hw _) (add hs _) (.hyp (Or.inl rfl))

theorem output_subst {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hh : Derives Γ (renamed w r s a b c d n q)) :
    Derives Γ (renamed w r s a b c d n v) := by
  let P := renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have hi : Derives Γ (P.instantiate q) := by
    simpa only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hh
  have ho := Derives.eqSubst P he hi
  simpa only [P, Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem reflexive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hr : Derives Γ (diagonal r)) (hs : Derives Γ (diagonal s))
    (hn : Derives Γ (SyntaxTermSyntax.term w a b n)) : Derives Γ (renamed w r s a b c d n n) := by
  have he := SyntaxRenameTermExistence.for_term hZ w r s a b c d n hw hm hn
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hr1 : Derives Δ (diagonal r.castSucc) := by simpa only [Formula.raise, diagonal_rename] using under hr Q
  have hs1 : Derives Δ (diagonal s.castSucc) := by simpa only [Formula.raise, diagonal_rename] using under hs Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hEq := identity (ZFContext.under hZ Q) _ _ _ _ _ _ _ _ _ hw1 hr1 hs1 (.conjR hQ)
  have ho := output_subst _ _ _ _ _ _ _ _ _ _ (eq_symm hEq) (.conjR hQ)
  simpa only [Formula.raise, renamed_rename] using ho
end PPAC.Migration.Internal.SyntaxRenameTermIdentity
