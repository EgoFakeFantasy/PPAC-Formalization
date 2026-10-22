import PPAC.Migration.Internal.SyntaxMapCodeDecode

/-! 映射自然码的真实binder提升：实际原图和实际提升图均由对象存在量词保留。 -/
namespace PPAC.Migration.Internal.SyntaxMapLiftSyntax
open Source SourceAlgebra SourceLogic SyntaxMapCodeSyntax SyntaxIndexLiftSyntax

def body {m} (w a c k u v l : Fin m) : Formula (m+2) :=
  (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc).conj
    ((lifted w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).conj
        (encoded w.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc v.castSucc.castSucc l.castSucc.castSucc))

def codedLift {m} (w a c k u v l : Fin m) : Formula m := .ex (.ex (body w a c k u v l))

def existsLiftCode {m} (w a c k u v : Fin m) : Formula m := .ex
  (codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc (Fin.last m))

def fiber {m} (w a c k u v : Fin m) : Formula m := .ex
  ((codedLift w.castSucc a.castSucc c.castSucc k.castSucc u.castSucc v.castSucc (Fin.last m)).conj
    (.all ((codedLift w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def outputAt {m} (w r a c u v l : Fin m) : Formula m := .ex
  ((lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)).conj
    (encoded w.castSucc (Fin.last m) u.castSucc v.castSucc l.castSucc))

theorem codedLift_rename {m n} (w a c k u v l : Fin m) (ρ : Fin m → Fin n) :
    (codedLift w a c k u v l).rename ρ = codedLift (ρ w) (ρ a) (ρ c) (ρ k) (ρ u) (ρ v) (ρ l) := by
  simp only [codedLift, body, Formula.rename, encoded_rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsLiftCode_rename {m n} (w a c k u v : Fin m) (ρ : Fin m → Fin n) :
    (existsLiftCode w a c k u v).rename ρ = existsLiftCode (ρ w) (ρ a) (ρ c) (ρ k) (ρ u) (ρ v) := by
  simp only [existsLiftCode, Formula.rename, codedLift_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m n} (w a c k u v : Fin m) (ρ : Fin m → Fin n) :
    (fiber w a c k u v).rename ρ = fiber (ρ w) (ρ a) (ρ c) (ρ k) (ρ u) (ρ v) := by
  simp only [fiber, Formula.rename, codedLift_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem outputAt_rename {m n} (w r a c u v l : Fin m) (ρ : Fin m → Fin n) :
    (outputAt w r a c u v l).rename ρ = outputAt (ρ w) (ρ r) (ρ a) (ρ c) (ρ u) (ρ v) (ρ l) := by
  simp only [outputAt, Formula.rename, lifted_rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_lift {m} {Γ : Context m} (w r g a c k u v l : Fin m)
    (hk : Derives Γ (encoded w r a c k)) (hg : Derives Γ (lifted w r a c u v g))
    (hl : Derives Γ (encoded w g u v l)) : Derives Γ (codedLift w a c k u v l) := by
  apply Derives.exI r
  apply Derives.exI g
  simp only [body, Formula.instantiate, Formula.rename, encoded_rename, lifted_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hk (.conjI hg hl)

theorem eliminate_lift {m} {Γ : Context m} (w a c k u v l : Fin m) (Q : Formula m)
    (he : Derives Γ (codedLift w a c k u v l))
    (hc : Derives (Context.add (body w a c k u v l) (Context.image Formula.raise (Context.image Formula.raise Γ))) Q.raise.raise) :
    Derives Γ Q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨q, hq, hh⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨q, Or.inr hq, hh⟩

theorem source_graph_subst {m} {Γ : Context m} (w r s a c u v g : Fin m)
    (he : Derives Γ (.equal r s)) (hr : Derives Γ (lifted w r a c u v g)) : Derives Γ (lifted w s a c u v g) := by
  let P := lifted w.castSucc (Fin.last m) a.castSucc c.castSucc u.castSucc v.castSucc g.castSucc
  have hi : Derives Γ (P.instantiate r) := by simpa only [P, Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst P he hi
  simpa only [P, Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxMapLiftSyntax
