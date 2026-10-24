import PPAC.Migration.Internal.PacketStructureSearchHead

/-! All original seven, one, six and three assignment bounds follow from actual canonical premises. -/
namespace PPAC.Migration.Internal.PacketStructureSearchBounds
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprBounds PacketStructureSyntax PacketStructureLocalSyntax PacketStructureApplicationSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem tree_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hl : Derives Γ (treeLocal w V r env)) : Derives Γ (environmentBound 7 r env) := by
  have hrN := PacketStructureSearchHead.root_natural hZ .tree w V r env hw hl
  have h0 := PacketStructureSearchHead.variable_bound hZ .tree (0 : Fin 7) (by change (0 : Fin 7) ∈ ([0,1,2,3] : List (Fin 7)); decide) w V r env hw hl
  have h1 := PacketStructureSearchHead.variable_bound hZ .tree (1 : Fin 7) (by change (1 : Fin 7) ∈ ([0,1,2,3] : List (Fin 7)); decide) w V r env hw hl
  have h2 := PacketStructureSearchHead.variable_bound hZ .tree (2 : Fin 7) (by change (2 : Fin 7) ∈ ([0,1,2,3] : List (Fin 7)); decide) w V r env hw hl
  have h3 := PacketStructureSearchHead.variable_bound hZ .tree (3 : Fin 7) (by change (3 : Fin 7) ∈ ([0,1,2,3] : List (Fin 7)); decide) w V r env hw hl
  let L := PacketStructureLocalSyntax.treeBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hZk := HornBinderRules.zf_body 1 hZ L
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old 1)) (HornBinderRules.under_body 1 hv L)
  have hrNk : Derives Δ (.mem (old 1 r) (old 1 w)) := HornBinderRules.under_body 1 hrN L
  have h0k := of_eq (below_rename (env 0) r (old 1)) (HornBinderRules.under_body 1 h0 L)
  have h1k := of_eq (below_rename (env 1) r (old 1)) (HornBinderRules.under_body 1 h1 L)
  have h2k := of_eq (below_rename (env 2) r (old 1)) (HornBinderRules.under_body 1 h2 L)
  have h3k := of_eq (below_rename (env 3) r (old 1)) (HornBinderRules.under_body 1 h3 L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR hL
  have ht0 := Derives.conjL (.conjR (.conjR hA))
  have ht1 := Derives.conjR (.conjR (.conjR hA))
  have h63 := PacketStructureSearchArithmetic.token_tail hZk (old 1 w) (old 1 V) (old 1 (env 0)) (old 1 (env 6)) (old 1 (env 3)) hwk hvk ht1
  have h6k := NaturalOrderBasic.transitive hZk (old 1 w) (old 1 (env 6)) (old 1 (env 3)) (old 1 r) hwk hrNk h63 h3k
  have h46 := PacketStructureSearchArithmetic.token_input hZk (old 1 w) (old 1 V) (old 1 (env 4)) (old 1 (env 5)) (old 1 (env 6)) hwk hvk ht0
  have h56 := PacketStructureSearchArithmetic.token_tail hZk (old 1 w) (old 1 V) (old 1 (env 4)) (old 1 (env 5)) (old 1 (env 6)) hwk hvk ht0
  have h4k := NaturalOrderBasic.transitive hZk (old 1 w) (old 1 (env 4)) (old 1 (env 6)) (old 1 r) hwk hrNk h46 h6k
  have h5k := NaturalOrderBasic.transitive hZk (old 1 w) (old 1 (env 5)) (old 1 (env 6)) (old 1 r) hwk hrNk h56 h6k
  have hb : Derives Δ (environmentBound 7 (old 1 r) (fun i => old 1 (env i))) := by
    apply intro_environmentBound (old 1 r) (fun i => old 1 (env i))
    intro i
    exact Fin.cases h0k (fun j1 => Fin.cases h1k (fun j2 => Fin.cases h2k (fun j3 => Fin.cases h3k (fun j4 => Fin.cases h4k (fun j5 => Fin.cases h5k (fun j6 => Fin.cases h6k (fun j0 => Fin.elim0 j0) j6) j5) j4) j3) j2) j1) i
  exact of_eq (environmentBound_rename 7 r env (old 1)).symm hb

theorem cons_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hl : Derives Γ (consLocal w V r env)) : Derives Γ (environmentBound 6 r env) := by
  have hrN := PacketStructureSearchHead.root_natural hZ .cons w V r env hw hl
  have h0 := PacketStructureSearchHead.variable_bound hZ .cons (0 : Fin 6) (by change (0 : Fin 6) ∈ ([0,1,2,3,4] : List (Fin 6)); decide) w V r env hw hl
  have h1 := PacketStructureSearchHead.variable_bound hZ .cons (1 : Fin 6) (by change (1 : Fin 6) ∈ ([0,1,2,3,4] : List (Fin 6)); decide) w V r env hw hl
  have h2 := PacketStructureSearchHead.variable_bound hZ .cons (2 : Fin 6) (by change (2 : Fin 6) ∈ ([0,1,2,3,4] : List (Fin 6)); decide) w V r env hw hl
  have h3 := PacketStructureSearchHead.variable_bound hZ .cons (3 : Fin 6) (by change (3 : Fin 6) ∈ ([0,1,2,3,4] : List (Fin 6)); decide) w V r env hw hl
  have h4 := PacketStructureSearchHead.variable_bound hZ .cons (4 : Fin 6) (by change (4 : Fin 6) ∈ ([0,1,2,3,4] : List (Fin 6)); decide) w V r env hw hl
  let L := PacketStructureLocalSyntax.consBody w V r env
  let Δ := Context.add L (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 L _ hl
  have hZk := HornBinderRules.zf_body 2 hZ L
  have hwk := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw L)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old 2)) (HornBinderRules.under_body 2 hv L)
  have hrNk : Derives Δ (.mem (old 2 r) (old 2 w)) := HornBinderRules.under_body 2 hrN L
  have h0k := of_eq (below_rename (env 0) r (old 2)) (HornBinderRules.under_body 2 h0 L)
  have h1k := of_eq (below_rename (env 1) r (old 2)) (HornBinderRules.under_body 2 h1 L)
  have h2k := of_eq (below_rename (env 2) r (old 2)) (HornBinderRules.under_body 2 h2 L)
  have h3k := of_eq (below_rename (env 3) r (old 2)) (HornBinderRules.under_body 2 h3 L)
  have h4k := of_eq (below_rename (env 4) r (old 2)) (HornBinderRules.under_body 2 h4 L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR (.conjR hL)
  have ht := Derives.conjR (.conjR hA)
  have h54 := PacketStructureSearchArithmetic.tree_tail hZk (old 2 w) (old 2 V) (old 2 (env 0)) (old 2 (env 5)) (old 2 (env 4)) hwk hvk ht
  have h5k := NaturalOrderBasic.transitive hZk (old 2 w) (old 2 (env 5)) (old 2 (env 4)) (old 2 r) hwk hrNk h54 h4k
  have hb : Derives Δ (environmentBound 6 (old 2 r) (fun i => old 2 (env i))) := by
    apply intro_environmentBound (old 2 r) (fun i => old 2 (env i))
    intro i
    exact Fin.cases h0k (fun j1 => Fin.cases h1k (fun j2 => Fin.cases h2k (fun j3 => Fin.cases h3k (fun j4 => Fin.cases h4k (fun j5 => Fin.cases h5k (fun j0 => Fin.elim0 j0) j5) j4) j3) j2) j1) i
  exact of_eq (environmentBound_rename 6 r env (old 2)).symm hb

theorem packet_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hl : Derives Γ (packetLocal w V r env)) : Derives Γ (environmentBound 3 r env) := by
  have hrN := PacketStructureSearchHead.root_natural hZ .packet w V r env hw hl
  have h0 := PacketStructureSearchHead.variable_bound hZ .packet (0 : Fin 3) (by change (0 : Fin 3) ∈ ([1,0] : List (Fin 3)); decide) w V r env hw hl
  have h1 := PacketStructureSearchHead.variable_bound hZ .packet (1 : Fin 3) (by change (1 : Fin 3) ∈ ([1,0] : List (Fin 3)); decide) w V r env hw hl
  let L := PacketStructureLocalSyntax.packetBody w V r env
  let Δ := Context.add L (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 L _ hl
  have hZk := HornBinderRules.zf_body 1 hZ L
  have hwk := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw L)
  have hvk := of_eq (PacketTraceCore.value_rename w V (old 1)) (HornBinderRules.under_body 1 hv L)
  have hrNk : Derives Δ (.mem (old 1 r) (old 1 w)) := HornBinderRules.under_body 1 hrN L
  have h0k := of_eq (below_rename (env 0) r (old 1)) (HornBinderRules.under_body 1 h0 L)
  have h1k := of_eq (below_rename (env 1) r (old 1)) (HornBinderRules.under_body 1 h1 L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR hL
  have hp := Derives.conjL (.conjR hA)
  have h21 := PacketStructureSearchArithmetic.affine_tail hZk (old 1 w) (old 1 V) (slot 1 0) (old 1 (env 2)) (old 1 (env 1)) hwk hvk hp
  have h2k := NaturalOrderBasic.transitive hZk (old 1 w) (old 1 (env 2)) (old 1 (env 1)) (old 1 r) hwk hrNk h21 h1k
  have hb : Derives Δ (environmentBound 3 (old 1 r) (fun i => old 1 (env i))) := by
    apply intro_environmentBound (old 1 r) (fun i => old 1 (env i))
    intro i
    exact Fin.cases h0k (fun j1 => Fin.cases h1k (fun j2 => Fin.cases h2k (fun j0 => Fin.elim0 j0) j2) j1) i
  exact of_eq (environmentBound_rename 3 r env (old 1)).symm hb

theorem nil_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (nilLocal w V r env)) : Derives Γ (environmentBound 1 r env) := by
  have h0 := PacketStructureSearchHead.variable_bound hZ .nil (0 : Fin 1) (by change (0 : Fin 1) ∈ ([0,0] : List (Fin 1)); decide) w V r env hw hl
  apply intro_environmentBound r env
  intro i
  exact Fin.cases h0 (fun j => Fin.elim0 j) i

theorem local_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hl : Derives Γ (localCase b w V r env)) : Derives Γ (environmentBound (rule b).arity r env) := by
  cases b
  · exact tree_bounds hZ w V r env hw hv hl
  · exact nil_bounds hZ w V r env hw hl
  · exact cons_bounds hZ w V r env hw hv hl
  · exact packet_bounds hZ w V r env hw hv hl

end PPAC.Migration.Internal.PacketStructureSearchBounds
