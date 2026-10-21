import PPAC.Migration.Internal.SyntaxIndexMapSyntax

/-! 纯语言项的内部重命名关系；两个实际索引经对象存在量词给出，bound/free不混合。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTermSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxVariableSyntax SyntaxTermSyntax SyntaxIndexMapSyntax

def branchBody {m} (bound : Bool) (w r a n q : Fin m) : Formula (m+2) :=
  (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    ((edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      ((code bound w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc).conj
        (code bound w.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc)))

def branch {m} (bound : Bool) (w r a n q : Fin m) : Formula m := .ex (.ex (branchBody bound w r a n q))

def renamed {m} (w r s a b c d n q : Fin m) : Formula m := (maps w r s a b c d).conj
  ((branch true w r a n q).disj (branch false w s b n q))

def existsBranch {m} (bound : Bool) (w r a n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (branch bound w.castSucc r.castSucc a.castSucc n.castSucc (Fin.last m)))

def existsRenamed {m} (w r s a b c d n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)))

def fiber {m} (w r s a b c d n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj
    ((renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
      (term w.castSucc c.castSucc d.castSucc (Fin.last m)))).conj
    (.all ((renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
      c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem branch_rename {m k} (bound : Bool) (w r a n q : Fin m) (ρ : Fin m → Fin k) :
    (branch bound w r a n q).rename ρ = branch bound (ρ w) (ρ r) (ρ a) (ρ n) (ρ q) := by
  simp only [branch, branchBody, Formula.rename, edge_rename, code_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem renamed_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (renamed w r s a b c d n q).rename ρ = renamed (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [renamed, Formula.rename, maps_rename, branch_rename]

theorem existsBranch_rename {m k} (bound : Bool) (w r a n : Fin m) (ρ : Fin m → Fin k) :
    (existsBranch bound w r a n).rename ρ = existsBranch bound (ρ w) (ρ r) (ρ a) (ρ n) := by
  simp only [existsBranch, Formula.rename, branch_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsRenamed_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (existsRenamed w r s a b c d n).rename ρ = existsRenamed (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [existsRenamed, Formula.rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w r s a b c d n).rename ρ = fiber (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, renamed_rename, term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_branch {m} {Γ : Context m} (bound : Bool) (w r a n q i j : Fin m)
    (hi : Derives Γ (.mem i a)) (he : Derives Γ (edge r i j))
    (hn : Derives Γ (code bound w i n)) (hq : Derives Γ (code bound w j q)) :
    Derives Γ (branch bound w r a n q) := by
  apply Derives.exI i
  apply Derives.exI j
  simp only [branchBody, Formula.instantiate, Formula.rename, edge_rename, code_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hi (.conjI he (.conjI hn hq))

theorem eliminate_branch {m} {Γ : Context m} (bound : Bool) (w r a n q : Fin m) (P : Formula m)
    (he : Derives Γ (branch bound w r a n q))
    (hc : Derives (Context.add (branchBody bound w r a n q) (Context.image Formula.raise (Context.image Formula.raise Γ)))
      P.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨u, hu, hh⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨u, Or.inr hu, hh⟩

theorem intro_renamed {m} {Γ : Context m} (bound : Bool) (w r s a b c d n q : Fin m)
    (hm : Derives Γ (maps w r s a b c d))
    (hb : Derives Γ (branch bound w (selectMap bound r s) (limit bound a b) n q)) :
    Derives Γ (renamed w r s a b c d n q) := by
  cases bound
  · exact .conjI hm (.disjR hb)
  · exact .conjI hm (.disjL hb)

theorem code_index_subst {m} {Γ : Context m} (bound : Bool) (w i j n : Fin m)
    (he : Derives Γ (.equal i j)) (hc : Derives Γ (code bound w i n)) : Derives Γ (code bound w j n) := by
  have hi : Derives Γ ((code bound w.castSucc (Fin.last m) n.castSucc).instantiate i) := by
    simpa only [Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (code bound w.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxRenameTermSyntax
