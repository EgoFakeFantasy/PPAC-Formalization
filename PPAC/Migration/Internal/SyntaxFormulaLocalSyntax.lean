import PPAC.Migration.Internal.ObjectSyntaxContextCarrier

/-! 原子四分支及七种原逻辑构造的完整局部判据；查询保持真实内部上下文。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaLocalSyntax
open Source SourceAlgebra SourceLogic SyntaxTermSyntax SyntaxAtomSyntax SyntaxLogicalSyntax

def localType {m} (w b f h n : Fin m) : Formula m :=
  (atomic w b f n).disj ((negation w b f h n).disj
    ((binary 0 w b f h n).disj ((binary 1 w b f h n).disj
      ((binary 2 w b f h n).disj ((binary 3 w b f h n).disj
        ((quantified true w b f h n).disj (quantified false w b f h n)))))))

theorem localType_rename {m k} (w b f h n : Fin m) (r : Fin m → Fin k) :
    (localType w b f h n).rename r = localType (r w) (r b) (r f) (r h) (r n) := by
  simp only [localType, negation, quantified, Formula.rename, atomic_rename, single_rename, binary_rename]

theorem subst_bound {m} {Γ : Context m} (w b k f h n : Fin m)
    (he : Derives Γ (.equal b k)) (ht : Derives Γ (localType w b f h n)) : Derives Γ (localType w k f h n) := by
  have hi : Derives Γ ((localType w.castSucc (Fin.last m) f.castSucc h.castSucc n.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, localType_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (localType w.castSucc (Fin.last m) f.castSucc h.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, localType_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem subst_free {m} {Γ : Context m} (w b f k h n : Fin m)
    (he : Derives Γ (.equal f k)) (ht : Derives Γ (localType w b f h n)) : Derives Γ (localType w b k h n) := by
  have hi : Derives Γ ((localType w.castSucc b.castSucc (Fin.last m) h.castSucc n.castSucc).instantiate f) := by
    simpa only [Formula.instantiate, localType_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  have ho := Derives.eqSubst (localType w.castSucc b.castSucc (Fin.last m) h.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, localType_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem intro_atomic {m} {Γ : Context m} (w b f h n : Fin m) (ha : Derives Γ (atomic w b f n)) :
    Derives Γ (localType w b f h n) := (.disjL ha)

theorem intro_negation {m} {Γ : Context m} (w b f h n : Fin m) (ha : Derives Γ (negation w b f h n)) :
    Derives Γ (localType w b f h n) := (.disjR (.disjL ha))

theorem intro_binary {m} {Γ : Context m} (kind : Fin 4) (w b f h n : Fin m) (ha : Derives Γ (binary kind w b f h n)) :
    Derives Γ (localType w b f h n) := by
  exact Fin.cases (fun hb => (.disjR (.disjR (.disjL hb))))
    (Fin.cases (fun hb => (.disjR (.disjR (.disjR (.disjL hb)))))
      (Fin.cases (fun hb => (.disjR (.disjR (.disjR (.disjR (.disjL hb))))))
        (Fin.cases (fun hb => (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hb))))))) (fun i => Fin.elim0 i)))) kind ha

theorem intro_quantified {m} {Γ : Context m} (universal : Bool) (w b f h n : Fin m)
    (ha : Derives Γ (quantified universal w b f h n)) : Derives Γ (localType w b f h n) := by
  cases universal with
  | false => exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR ha)))))))
  | true => exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL ha)))))))
end PPAC.Migration.Internal.SyntaxFormulaLocalSyntax
