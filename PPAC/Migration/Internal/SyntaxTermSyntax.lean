import PPAC.Migration.Internal.SyntaxVariableDecode

/-! 无函数符号纯签名的项作用域：内部bound/free长度和真实变量索引见证。 -/
namespace PPAC.Migration.Internal.SyntaxTermSyntax
open Source SourceAlgebra SourceLogic SyntaxVariableSyntax SyntaxVariableDecodeSyntax

def limit {m} (bound : Bool) (b f : Fin m) : Fin m := if bound then b else f

def contexts {m} (w b f : Fin m) : Formula m := (Formula.mem b w).conj (.mem f w)

def scope {m} (bound : Bool) (w b f i : Fin m) : Formula m := (contexts w b f).conj (.mem i (limit bound b f))

def branchWitness {m} (bound : Bool) (w l n : Fin m) : Formula (m+1) :=
  (Formula.mem (Fin.last m) l.castSucc).conj (code bound w.castSucc (Fin.last m) n.castSucc)

def branch {m} (bound : Bool) (w l n : Fin m) : Formula m := .ex (branchWitness bound w l n)

def term {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj ((branch true w b n).disj (branch false w f n))

def decodedWitness {m} (bound : Bool) (w l n : Fin m) : Formula (m+1) :=
  (branchWitness bound w l n).conj (uniqueIndex bound w.castSucc n.castSucc (Fin.last m))

def decodedBranch {m} (bound : Bool) (w l n : Fin m) : Formula m := .ex (decodedWitness bound w l n)

def decoded {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj ((decodedBranch true w b n).disj (decodedBranch false w f n))

def existsAt {m} (bound : Bool) (w b f i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    ((code bound w.castSucc i.castSucc (Fin.last m)).conj (term w.castSucc b.castSucc f.castSucc (Fin.last m))))

theorem limit_map {m k} (bound : Bool) (b f : Fin m) (s : Fin m → Fin k) : s (limit bound b f) = limit bound (s b) (s f) := by
  cases bound <;> rfl

theorem contexts_rename {m k} (w b f : Fin m) (s : Fin m → Fin k) : (contexts w b f).rename s = contexts (s w) (s b) (s f) := rfl

theorem scope_rename {m k} (bound : Bool) (w b f i : Fin m) (s : Fin m → Fin k) : (scope bound w b f i).rename s = scope bound (s w) (s b) (s f) (s i) := by
  simp only [scope, Formula.rename, contexts_rename, limit_map]

theorem branch_rename {m k} (bound : Bool) (w l n : Fin m) (s : Fin m → Fin k) : (branch bound w l n).rename s = branch bound (s w) (s l) (s n) := by
  simp only [branch, branchWitness, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem term_rename {m k} (w b f n : Fin m) (s : Fin m → Fin k) : (term w b f n).rename s = term (s w) (s b) (s f) (s n) := by
  simp only [term, Formula.rename, contexts_rename, branch_rename]

theorem decodedBranch_rename {m k} (bound : Bool) (w l n : Fin m) (s : Fin m → Fin k) : (decodedBranch bound w l n).rename s = decodedBranch bound (s w) (s l) (s n) := by
  simp only [decodedBranch, decodedWitness, branchWitness, Formula.rename, code_rename, uniqueIndex_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decoded_rename {m k} (w b f n : Fin m) (s : Fin m → Fin k) : (decoded w b f n).rename s = decoded (s w) (s b) (s f) (s n) := by
  simp only [decoded, Formula.rename, contexts_rename, decodedBranch_rename]

theorem existsAt_rename {m k} (bound : Bool) (w b f i : Fin m) (s : Fin m → Fin k) : (existsAt bound w b f i).rename s = existsAt bound (s w) (s b) (s f) (s i) := by
  simp only [existsAt, Formula.rename, code_rename, term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_branch {m} {Γ : Context m} (bound : Bool) (w l n i : Fin m) (hi : Derives Γ (.mem i l))
    (hc : Derives Γ (code bound w i n)) : Derives Γ (branch bound w l n) := by
  apply Derives.exI i
  simp only [branchWitness, Formula.instantiate, Formula.rename, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hi hc

theorem eliminate_branch {m} {Γ : Context m} (bound : Bool) (w l n : Fin m) (q : Formula m) (hb : Derives Γ (branch bound w l n))
    (hc : Derives (Context.add (branchWitness bound w l n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hb hc

theorem intro_term {m} {Γ : Context m} (bound : Bool) (w b f n i : Fin m) (hs : Derives Γ (scope bound w b f i))
    (hc : Derives Γ (code bound w i n)) : Derives Γ (term w b f n) := by
  cases bound with
  | false => exact .conjI (.conjL hs) (.disjR (intro_branch false w f n i (.conjR hs) hc))
  | true => exact .conjI (.conjL hs) (.disjL (intro_branch true w b n i (.conjR hs) hc))

theorem intro_decoded_branch {m} {Γ : Context m} (bound : Bool) (w l n i : Fin m) (hi : Derives Γ (.mem i l))
    (hc : Derives Γ (code bound w i n)) (hu : Derives Γ (uniqueIndex bound w n i)) : Derives Γ (decodedBranch bound w l n) := by
  apply Derives.exI i
  simp only [decodedWitness, branchWitness, Formula.instantiate, Formula.rename, code_rename, uniqueIndex_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hi hc) hu
end PPAC.Migration.Internal.SyntaxTermSyntax
