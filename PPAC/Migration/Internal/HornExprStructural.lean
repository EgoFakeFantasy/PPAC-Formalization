import PPAC.Migration.Internal.HornExprValue

/-! 上游真实Expr的原节点、Nil和Cons表达式与原数值结构在全部内部候选上对应。 -/
namespace PPAC.Migration.Internal.HornExprStructural
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem raw_graph {m n} {Γ : Context m} (e f : Expr n) (w a b y : Fin m) (env : Fin n → Fin m)
    (ha : Derives Γ (graph e w env a)) (hb : Derives Γ (graph f w env b))
    (hy : Derives Γ (StructuralNodeSyntax.raw w a b y)) : Derives Γ (graph (.succ (.pair e f)) w env y) := by
  let P := StructuralNodeSyntax.rawWitness w a b y
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hy
  have ha1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) a.castSucc) := of_eq (graph_rename e w a env Fin.castSucc) (under ha P)
  have hb1 : Derives Δ (graph f w.castSucc (fun i => (env i).castSucc) b.castSucc) := of_eq (graph_rename f w b env Fin.castSucc) (under hb P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (graph_rename (.succ (.pair e f)) w y env Fin.castSucc).symm
    (intro_succ (.pair e f) _ _ _ _ (intro_pair e f _ _ _ _ _ ha1 hb1 (.conjL hP)) (.conjR hP))

theorem raw_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e f : Expr n) (w a b y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (ha : Derives Γ (graph e w env a)) (hb : Derives Γ (graph f w env b)) :
    Derives Γ ((graph (.succ (.pair e f)) w env y).iff (StructuralNodeSyntax.raw w a b y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (.succ (.pair e f)) w env y
    have he := StructuralNodeExistence.exists_raw (ZFContext.add hZ E) w a b (add hw E)
      (HornExprRange.range (ZFContext.add hZ E) e w a env (add hw E) (add hn E) (add ha E))
      (HornExprRange.range (ZFContext.add hZ E) f w b env (add hw E) (add hn E) (add hb E))
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralNodeSyntax.raw w.castSucc a.castSucc b.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := R) he
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp E) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (lift hn)
    have ha1 := of_eq (graph_rename e w a env Fin.castSucc) (lift ha)
    have hb1 := of_eq (graph_rename f w b env Fin.castSucc) (lift hb)
    have hy1 : Derives Δ (graph (.succ (.pair e f)) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq
      (graph_rename (.succ (.pair e f)) w y env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have heq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) R) (.succ (.pair e f)) w.castSucc y.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hy1
      (raw_graph e f _ _ _ _ _ ha1 hb1 (.conjR hR))
    exact of_eq (StructuralNodeSyntax.raw_rename w a b y Fin.castSucc).symm
      (StructuralNodeSyntax.output_subst _ _ _ _ _ (eq_symm heq) (.conjR hR))
  · apply Derives.impI
    exact raw_graph e f _ _ _ _ _ (add ha _) (add hb _) (.hyp (Or.inl rfl))

theorem nil_graph {m n} {Γ : Context m} (w y : Fin m) (env : Fin n → Fin m)
    (hy : Derives Γ (StructuralListSyntax.nilCode w y)) : Derives Γ (graph (Expr.list []) w env y) := by
  let Z := StructuralListSyntax.nilWitness w y
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) hy
  have hZ : Derives Δ Z := .hyp (Or.inl rfl)
  exact of_eq (graph_rename (Expr.list []) w y env Fin.castSucc).symm
    (raw_graph (.literal 0) (.literal 0) w.castSucc (Fin.last m) (Fin.last m) y.castSucc (fun i => (env i).castSucc) (.conjL hZ) (.conjL hZ) (.conjR hZ))

theorem cons_graph {m n} {Γ : Context m} (e f : Expr n) (w h t y : Fin m) (env : Fin n → Fin m)
    (hh : Derives Γ (graph e w env h)) (ht : Derives Γ (graph f w env t))
    (hy : Derives Γ (StructuralListSyntax.consCode w h t y)) :
    Derives Γ (graph (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w env y) := by
  let C := StructuralListSyntax.consUnits w h t y
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 C _ hy
  have hh2 : Derives Δ (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) h.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (SyntaxRenameBinders.under_2 hh C)
  have ht2 : Derives Δ (graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) t.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (SyntaxRenameBinders.under_2 ht C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he2 : Derives Δ (graph (.literal 1) w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))) := SyntaxNumeralSyntax.intro_succ 0 _ _ (.conjL hC) (.conjL (.conjR hC))
  let P := StructuralListSyntax.consAtWitness w.castSucc.castSucc (Fin.last (m+1)) h.castSucc.castSucc t.castSucc.castSucc y.castSucc.castSucc
  let Ξ := Context.add P (Context.image Formula.raise Δ)
  apply Derives.exE (p := P) (.conjR (.conjR hC))
  have hh3 : Derives Ξ (graph e w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) h.castSucc.castSucc.castSucc) := of_eq (graph_rename e w.castSucc.castSucc h.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under hh2 P)
  have ht3 : Derives Ξ (graph f w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) t.castSucc.castSucc.castSucc) := of_eq (graph_rename f w.castSucc.castSucc t.castSucc.castSucc (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under ht2 P)
  have he3 : Derives Ξ (graph (.literal 1) w.castSucc.castSucc.castSucc (fun i => (env i).castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc) := of_eq (graph_rename (.literal 1) w.castSucc.castSucc (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) Fin.castSucc) (under he2 P)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have ho := raw_graph (.literal 1) (.pair e f) _ _ _ _ _ he3 (intro_pair e f _ _ _ _ _ hh3 ht3 (.conjL hP)) (.conjR hP)
  exact of_eq (by simp only [Formula.raise, graph_rename]) ho

theorem cons_output_subst {m} {Γ : Context m} (w h t y z : Fin m) (he : Derives Γ (.equal y z))
    (hy : Derives Γ (StructuralListSyntax.consCode w h t y)) : Derives Γ (StructuralListSyntax.consCode w h t z) := by
  let P := StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate y = StructuralListSyntax.consCode w h t y := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = StructuralListSyntax.consCode w h t z := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

theorem cons_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e f : Expr n) (w h t y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hh : Derives Γ (graph e w env h)) (ht : Derives Γ (graph f w env t)) :
    Derives Γ ((graph (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w env y).iff (StructuralListSyntax.consCode w h t y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w env y
    have he := StructuralConsCore.exists_cons (ZFContext.add hZ E) w h t (add hw E)
      (HornExprRange.range (ZFContext.add hZ E) e w h env (add hw E) (add hn E) (add hh E))
      (HornExprRange.range (ZFContext.add hZ E) f w t env (add hw E) (add hn E) (add ht E))
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := R) he
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp E) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (lift hn)
    have hh1 := of_eq (graph_rename e w h env Fin.castSucc) (lift hh)
    have ht1 := of_eq (graph_rename f w t env Fin.castSucc) (lift ht)
    have hy1 : Derives Δ (graph (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq
      (graph_rename _ w y env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have heq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) R) (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w.castSucc y.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hy1
      (cons_graph e f _ _ _ _ _ hh1 ht1 (.conjR hR))
    exact of_eq (StructuralListSyntax.consCode_rename w h t y Fin.castSucc).symm (cons_output_subst _ _ _ _ _ (eq_symm heq) (.conjR hR))
  · apply Derives.impI
    exact cons_graph e f _ _ _ _ _ (add hh _) (add ht _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornExprStructural
