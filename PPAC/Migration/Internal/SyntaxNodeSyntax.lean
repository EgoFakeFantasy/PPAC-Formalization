import PPAC.Migration.Internal.SyntaxForestLength

/-! 精确有限字段树节点与有限标签构造器的纯对象公式；内部标量是任意自然标签的零字段节点。 -/
namespace PPAC.Migration.Internal.SyntaxNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNumeralSyntax StructuralNodeSyntax

def nodeBody {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) : Formula (m+1) :=
  (Formula.mem tag.castSucc w.castSucc).conj
    ((forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (raw w.castSucc tag.castSucc (Fin.last m) n.castSucc))

def node {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) : Formula m := .ex (nodeBody k w tag xs n)

def existsNode {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (node k w.castSucc tag.castSucc (fun i => (xs i).castSucc) (Fin.last m)))

def constructorBody {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) : Formula (m+1) :=
  (numeral tag (Fin.last m)).conj (node k w.castSucc (Fin.last m) (fun i => (xs i).castSucc) n.castSucc)

def constructor {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) : Formula m := .ex (constructorBody k tag w xs n)

def existsConstructor {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)))

def constructorFiber {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))).conj
    (.all ((constructor k tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def nodeFiber {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (node k w.castSucc tag.castSucc (fun i => (xs i).castSucc) (Fin.last m))).conj
    (.all ((node k w.castSucc.castSucc tag.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def scalar {m} (w i n : Fin m) : Formula m := node 0 w i Fin.elim0 n

theorem node_rename {m l} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (s : Fin m → Fin l) :
    (node k w tag xs n).rename s = node k (s w) (s tag) (fun i => s (xs i)) (s n) := by
  simp only [node, nodeBody, Formula.rename, forest_rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsNode_rename {m l} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin l) :
    (existsNode k w tag xs).rename s = existsNode k (s w) (s tag) (fun i => s (xs i)) := by
  simp only [existsNode, Formula.rename, node_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem constructor_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (s : Fin m → Fin l) :
    (constructor k tag w xs n).rename s = constructor k tag (s w) (fun i => s (xs i)) (s n) := by
  simp only [constructor, constructorBody, Formula.rename, numeral_rename, node_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsConstructor_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin l) :
    (existsConstructor k tag w xs).rename s = existsConstructor k tag (s w) (fun i => s (xs i)) := by
  simp only [existsConstructor, Formula.rename, constructor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem constructorFiber_rename {m l} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin l) :
    (constructorFiber k tag w xs).rename s = constructorFiber k tag (s w) (fun i => s (xs i)) := by
  simp only [constructorFiber, Formula.rename, constructor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem nodeFiber_rename {m l} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (s : Fin m → Fin l) :
    (nodeFiber k w tag xs).rename s = nodeFiber k (s w) (s tag) (fun i => s (xs i)) := by
  simp only [nodeFiber, Formula.rename, node_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem scalar_rename {m l} (w i n : Fin m) (s : Fin m → Fin l) : (scalar w i n).rename s = scalar (s w) (s i) (s n) := by
  simp only [scalar, node, nodeBody, forest, Formula.rename, StructuralListSyntax.nilCode_rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_node {m} {Γ : Context m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n p : Fin m)
    (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (forest k w xs p)) (hn : Derives Γ (raw w tag p n)) : Derives Γ (node k w tag xs n) := by
  apply Derives.exI p
  simp only [nodeBody, Formula.instantiate, Formula.rename, forest_rename, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht (.conjI hp hn)

theorem eliminate_node {m} {Γ : Context m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (q : Formula m)
    (hn : Derives Γ (node k w tag xs n))
    (hc : Derives (Context.add (nodeBody k w tag xs n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hn hc

theorem intro_constructor {m} {Γ : Context m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n t : Fin m)
    (ht : Derives Γ (numeral tag t)) (hn : Derives Γ (node k w t xs n)) : Derives Γ (constructor k tag w xs n) := by
  apply Derives.exI t
  simp only [constructorBody, Formula.instantiate, Formula.rename, numeral_rename, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hn

theorem eliminate_constructor {m} {Γ : Context m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (q : Formula m)
    (hn : Derives Γ (constructor k tag w xs n))
    (hc : Derives (Context.add (constructorBody k tag w xs n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hn hc

theorem tag_subst {m} {Γ : Context m} (k : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (he : Derives Γ (.equal a b)) (hn : Derives Γ (node k w a xs n)) : Derives Γ (node k w b xs n) := by
  have hi : Derives Γ ((node k w.castSucc (Fin.last m) (fun i => (xs i).castSucc) n.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (node k w.castSucc (Fin.last m) (fun i => (xs i).castSucc) n.castSucc) he hi
  simpa only [Formula.instantiate, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxNodeSyntax
