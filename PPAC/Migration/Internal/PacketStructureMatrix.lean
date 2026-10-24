import PPAC.Migration.Internal.PacketStructureExpr

/-! Complete original four matrices normalize at actual structural witnesses, including every ordered premise. -/
namespace PPAC.Migration.Internal.PacketStructureMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketStructureSyntax PacketStructureRuleData
open PacketStructureExpr
open YesMetaZFC.Automation
open ObjectHorn (Expr)

def treeFields : Fin 3 → Expr 7 := Fin.cases (ObjectPacket.rawNode (.var 0) (.var 1)) (Fin.cases (.var 2) (Fin.cases (.var 3) (fun i => Fin.elim0 i)))

theorem tree_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r n : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hr : Derives Γ (StructuralNodeSyntax.raw w (env 0) (env 1) n))
    : Derives Γ ((HornRuleSyntax.matrix treeRule w r V env).iff (treeAt w V r n env)) := by
  have hv (i : Fin 7) := var_graph w env hn i
  have hraw := HornExprStructural.raw_graph (.var (0 : Fin 7)) (.var 1) w (env 0) (env 1) n env (hv 0) (hv 1) hr
  have hh := row_at hZ 3 3 treeFields w r env (Fin.cases ((n)) (Fin.cases ((env 2)) (Fin.cases ((env 3)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases ((hraw)) (Fin.cases ((hv 2)) (Fin.cases ((hv 3)) (fun i => Fin.elim0 i))) i)
  have hp0 := premise_at hZ 4 4 (Fin.cases (.var 1) (Fin.cases (.var 4) (Fin.cases (.var 2) (Fin.cases (.var 5) (fun i => Fin.elim0 i))))) w V env (Fin.cases ((env 1)) (Fin.cases ((env 4)) (Fin.cases ((env 2)) (Fin.cases ((env 5)) (fun i => Fin.elim0 i))))) hw hn (fun i => Fin.cases ((hv 1)) (Fin.cases ((hv 4)) (Fin.cases ((hv 2)) (Fin.cases ((hv 5)) (fun i => Fin.elim0 i)))) i)
  have hp1 := premise_at hZ 3 2 (Fin.cases (.var 4) (Fin.cases (.var 5) (Fin.cases (.var 6) (fun i => Fin.elim0 i)))) w V env (Fin.cases ((env 4)) (Fin.cases ((env 5)) (Fin.cases ((env 6)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases ((hv 4)) (Fin.cases ((hv 5)) (Fin.cases ((hv 6)) (fun i => Fin.elim0 i))) i)
  have hp2 := premise_at hZ 3 2 (Fin.cases (.var 0) (Fin.cases (.var 6) (Fin.cases (.var 3) (fun i => Fin.elim0 i)))) w V env (Fin.cases ((env 0)) (Fin.cases ((env 6)) (Fin.cases ((env 3)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases ((hv 0)) (Fin.cases ((hv 6)) (Fin.cases ((hv 3)) (fun i => Fin.elim0 i))) i)
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix treeRule w r V env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR (.conjR hM)
    exact (.conjI (.impE (add (.conjL hh) M) (.conjL hM)) (.conjI (.impE (add (.conjL hp0) M) (.conjL hP)) (.conjI (.impE (add (.conjL hp1) M) (.conjL (.conjR hP))) (.impE (add (.conjL hp2) M) (.conjL (.conjR (.conjR hP)))))))
  · apply Derives.impI
    let M := treeAt w V r n env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR hM
    exact .conjI (.impE (add (.conjR hh) M) (.conjL hM)) (.conjI HornRuleSyntax.truth_proved (.conjI (.impE (add (.conjR hp0) M) (.conjL hP)) (.conjI (.impE (add (.conjR hp1) M) (.conjL (.conjR hP))) (.conjI (.impE (add (.conjR hp2) M) (.conjR (.conjR hP))) HornRuleSyntax.truth_proved))))

def nilFields : Fin 4 → Expr 1 := Fin.cases (Expr.list []) (Fin.cases (.literal 0) (Fin.cases (.var 0) (Fin.cases (.var 0) (fun i => Fin.elim0 i))))

theorem nil_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r z e : Fin m) (env : Fin 1 → Fin m)
    (V : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z))
    : Derives Γ ((HornRuleSyntax.matrix nilRule w r V env).iff (nilAt w r z e env)) := by
  have hv (i : Fin 1) := var_graph w env hn i
  have hNil := HornExprStructural.nil_graph w e env (StructuralNil.at_unit hZ w z e hw hz he)
  have hh := row_at hZ 4 4 nilFields w r env (Fin.cases ((e)) (Fin.cases ((z)) (Fin.cases ((env 0)) (Fin.cases ((env 0)) (fun i => Fin.elim0 i))))) hw hn (fun i => Fin.cases ((hNil)) (Fin.cases ((hz)) (Fin.cases ((hv 0)) (Fin.cases ((hv 0)) (fun i => Fin.elim0 i)))) i)
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix nilRule w r V env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    exact (.impE (add (.conjL hh) M) (.conjL hM))
  · apply Derives.impI
    let M := nilAt w r z e env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjR hh) M) hM) (.conjI HornRuleSyntax.truth_proved HornRuleSyntax.truth_proved)

def consFields : Fin 4 → Expr 6 := Fin.cases (ObjectPacket.cons (.var 0) (.var 1)) (Fin.cases (.succ (.var 2)) (Fin.cases (.var 3) (Fin.cases (.var 4) (fun i => Fin.elim0 i))))

theorem cons_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r n s : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n))
    (hs : Derives Γ (successor s (env 2)))
    : Derives Γ ((HornRuleSyntax.matrix consRule w r V env).iff (consAt w V r n s env)) := by
  have hv (i : Fin 6) := var_graph w env hn i
  have hCons := HornExprStructural.cons_graph (.var (0 : Fin 6)) (.var 1) w (env 0) (env 1) n env (hv 0) (hv 1) hc
  have hSucc := intro_succ (.var (2 : Fin 6)) w s (env 2) env (hv 2) hs
  have hh := row_at hZ 4 4 consFields w r env (Fin.cases ((n)) (Fin.cases ((s)) (Fin.cases ((env 3)) (Fin.cases ((env 4)) (fun i => Fin.elim0 i))))) hw hn (fun i => Fin.cases ((hCons)) (Fin.cases ((hSucc)) (Fin.cases ((hv 3)) (Fin.cases ((hv 4)) (fun i => Fin.elim0 i)))) i)
  have hp0 := premise_at hZ 4 4 (Fin.cases (.var 1) (Fin.cases (.var 2) (Fin.cases (.var 3) (Fin.cases (.var 5) (fun i => Fin.elim0 i))))) w V env (Fin.cases ((env 1)) (Fin.cases ((env 2)) (Fin.cases ((env 3)) (Fin.cases ((env 5)) (fun i => Fin.elim0 i))))) hw hn (fun i => Fin.cases ((hv 1)) (Fin.cases ((hv 2)) (Fin.cases ((hv 3)) (Fin.cases ((hv 5)) (fun i => Fin.elim0 i)))) i)
  have hp1 := premise_at hZ 3 3 (Fin.cases (.var 0) (Fin.cases (.var 5) (Fin.cases (.var 4) (fun i => Fin.elim0 i)))) w V env (Fin.cases ((env 0)) (Fin.cases ((env 5)) (Fin.cases ((env 4)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases ((hv 0)) (Fin.cases ((hv 5)) (Fin.cases ((hv 4)) (fun i => Fin.elim0 i))) i)
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix consRule w r V env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR (.conjR hM)
    exact (.conjI (.impE (add (.conjL hh) M) (.conjL hM)) (.conjI (.impE (add (.conjL hp0) M) (.conjL hP)) (.impE (add (.conjL hp1) M) (.conjL (.conjR hP)))))
  · apply Derives.impI
    let M := consAt w V r n s env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR hM
    exact .conjI (.impE (add (.conjR hh) M) (.conjL hM)) (.conjI HornRuleSyntax.truth_proved (.conjI (.impE (add (.conjR hp0) M) (.conjL hP)) (.conjI (.impE (add (.conjR hp1) M) (.conjR hP)) HornRuleSyntax.truth_proved)))

def packetFields : Fin 2 → Expr 3 := Fin.cases (.var 1) (Fin.cases (.var 0) (fun i => Fin.elim0 i))

theorem packet_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r e : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e))
    : Derives Γ ((HornRuleSyntax.matrix packetRule w r V env).iff (packetAt w V r e env)) := by
  have hv (i : Fin 3) := var_graph w env hn i
  have hh := row_at hZ 2 5 packetFields w r env (Fin.cases ((env 1)) (Fin.cases ((env 0)) (fun i => Fin.elim0 i))) hw hn (fun i => Fin.cases ((hv 1)) (Fin.cases ((hv 0)) (fun i => Fin.elim0 i)) i)
  have hp0 := premise_at hZ 3 1 (Fin.cases (.literal 1) (Fin.cases (.var 2) (Fin.cases (.var 1) (fun i => Fin.elim0 i)))) w V env (Fin.cases (e) (Fin.cases ((env 2)) (Fin.cases ((env 1)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases (he) (Fin.cases ((hv 2)) (Fin.cases ((hv 1)) (fun i => Fin.elim0 i))) i)
  have hp1 := premise_at hZ 3 3 (Fin.cases (.var 0) (Fin.cases (.literal 1) (Fin.cases (.var 2) (fun i => Fin.elim0 i)))) w V env (Fin.cases ((env 0)) (Fin.cases (e) (Fin.cases ((env 2)) (fun i => Fin.elim0 i)))) hw hn (fun i => Fin.cases ((hv 0)) (Fin.cases (he) (Fin.cases ((hv 2)) (fun i => Fin.elim0 i))) i)
  apply Derives.conjI
  · apply Derives.impI
    let M := HornRuleSyntax.matrix packetRule w r V env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR (.conjR hM)
    exact (.conjI (.impE (add (.conjL hh) M) (.conjL hM)) (.conjI (.impE (add (.conjL hp0) M) (.conjL hP)) (.impE (add (.conjL hp1) M) (.conjL (.conjR hP)))))
  · apply Derives.impI
    let M := packetAt w V r e env
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    have hP := Derives.conjR hM
    exact .conjI (.impE (add (.conjR hh) M) (.conjL hM)) (.conjI HornRuleSyntax.truth_proved (.conjI (.impE (add (.conjR hp0) M) (.conjL hP)) (.conjI (.impE (add (.conjR hp1) M) (.conjR hP)) HornRuleSyntax.truth_proved)))

end PPAC.Migration.Internal.PacketStructureMatrix
