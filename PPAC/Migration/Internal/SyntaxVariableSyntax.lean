import PPAC.Migration.Internal.SyntaxConstructors

/-! 原bvar/fvar编码为标签0/1的单字段节点，唯一字段必须是内部索引scalar叶。 -/
namespace PPAC.Migration.Internal.SyntaxVariableSyntax
open Source SourceAlgebra SourceLogic SyntaxNodeSyntax

def tag (bound : Bool) : Nat := if bound then 0 else 1

def codeBody {m} (bound : Bool) (w i n : Fin m) : Formula (m+1) :=
  (scalar w.castSucc i.castSucc (Fin.last m)).conj
    (constructor 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc)

def code {m} (bound : Bool) (w i n : Fin m) : Formula m := .ex (codeBody bound w i n)

def existsCode {m} (bound : Bool) (w i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc i.castSucc (Fin.last m)))

def fiber {m} (bound : Bool) (w i : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc i.castSucc (Fin.last m))).conj
    (.all ((code bound w.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem code_rename {m l} (bound : Bool) (w i n : Fin m) (s : Fin m → Fin l) : (code bound w i n).rename s = code bound (s w) (s i) (s n) := by
  simp only [code, codeBody, Formula.rename, scalar_rename, constructor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m l} (bound : Bool) (w i : Fin m) (s : Fin m → Fin l) : (existsCode bound w i).rename s = existsCode bound (s w) (s i) := by
  simp only [existsCode, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (bound : Bool) (w i : Fin m) (s : Fin m → Fin l) : (fiber bound w i).rename s = fiber bound (s w) (s i) := by
  simp only [fiber, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (bound : Bool) (w i n s : Fin m)
    (hs : Derives Γ (scalar w i s)) (hn : Derives Γ (constructor 1 (tag bound) w (fun _ => s) n)) : Derives Γ (code bound w i n) := by
  apply Derives.exI s
  simp only [codeBody, Formula.instantiate, Formula.rename, scalar_rename, constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hn

theorem eliminate_code {m} {Γ : Context m} (bound : Bool) (w i n : Fin m) (q : Formula m) (hn : Derives Γ (code bound w i n))
    (hc : Derives (Context.add (codeBody bound w i n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hn hc

theorem unary_subst {m} {Γ : Context m} (label : Nat) (w a b n : Fin m) (he : Derives Γ (.equal a b))
    (hn : Derives Γ (constructor 1 label w (fun _ => a) n)) : Derives Γ (constructor 1 label w (fun _ => b) n) := by
  have hi : Derives Γ ((constructor 1 label w.castSucc (fun _ => Fin.last m) n.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (constructor 1 label w.castSucc (fun _ => Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxVariableSyntax
