import PPAC.Migration.Internal.LogicalAbstractNode
import PPAC.Migration.Internal.LogicalStaticPatterns
import PPAC.Migration.Internal.LogicalInstantiateNode

/-! 原27逻辑模式完整纯关系析取及独立数学规格的对象双条件；原共享Bool桥仍另需证明。 -/
namespace PPAC.Migration.Internal.LogicalAllPatterns
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation

def originalTable : List ObjectLogicalAxiom.Shape := [
  ObjectLogicalAxiom.rule0, ObjectLogicalAxiom.rule1, ObjectLogicalAxiom.rule2, ObjectLogicalAxiom.rule3, ObjectLogicalAxiom.rule4, ObjectLogicalAxiom.rule5, ObjectLogicalAxiom.rule6, ObjectLogicalAxiom.rule7, ObjectLogicalAxiom.rule8, ObjectLogicalAxiom.rule9, ObjectLogicalAxiom.rule10, ObjectLogicalAxiom.rule11, ObjectLogicalAxiom.rule12, ObjectLogicalAxiom.rule13, ObjectLogicalAxiom.rule14, ObjectLogicalAxiom.rule15, ObjectLogicalAxiom.rule16, ObjectLogicalAxiom.rule17, ObjectLogicalAxiom.rule18, ObjectLogicalAxiom.rule19, ObjectLogicalAxiom.rule20, ObjectLogicalAxiom.rule21, ObjectLogicalAxiom.rule22, ObjectLogicalAxiom.rule23, ObjectLogicalAxiom.rule24, ObjectLogicalAxiom.rule25, ObjectLogicalAxiom.rule26]

theorem original_table_exact : originalTable = ObjectLogicalAxiom.shapes := rfl

theorem original_table_length : originalTable.length = 27 := by decide

def patternNodes {m} (w row : Fin m) : List (Formula m) := [
  LogicalStaticNodeSyntax.node 3 false (ObjectLogicalAxiom.rule0.head) w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule1.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule2.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule3.head) w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule4.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule5.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule6.head) w row,
  LogicalStaticNodeSyntax.node 0 false (ObjectLogicalAxiom.rule7.head) w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule8.head) w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule9.head) w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule10.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule11.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule12.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule13.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule14.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule15.head) w row,
  LogicalStaticNodeSyntax.node 3 false (ObjectLogicalAxiom.rule16.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule17.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule18.head) w row,
  LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule19.head) w row,
  LogicalInstantiateNodeSyntax.node4 true w row,
  LogicalAbstractNodeSyntax.node21 w row,
  LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule22.head) w row,
  LogicalInstantiateNodeSyntax.node4 false w row,
  LogicalAbstractNodeSyntax.node24 w row,
  LogicalInstantiateNodeSyntax.node6 w row,
  LogicalStaticNodeSyntax.node 1 true (ObjectLogicalAxiom.rule26.head) w row]

def patternSpecifications {m} (w z row : Fin m) : List (Formula m) := [
  LogicalStaticNodeSyntax.normalized 3 false (@LogicalRule0Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule1Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule2Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule3Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule4Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule5Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule6Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 0 false (@LogicalRule7Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule8Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule9Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule10Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule11Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule12Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule13Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule14Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule15Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 3 false (@LogicalRule16Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule17Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule18Head.normalized) w z row,
  LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule19Head.normalized) w z row,
  LogicalInstantiateNodeSyntax.normalized4 true w z row,
  LogicalAbstractNodeSyntax.normalized21 w z row,
  LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule22Head.normalized) w z row,
  LogicalInstantiateNodeSyntax.normalized4 false w z row,
  LogicalAbstractNodeSyntax.normalized24 w z row,
  LogicalInstantiateNodeSyntax.normalized6 w z row,
  LogicalStaticNodeSyntax.normalized 1 true (@LogicalRule26Head.normalized) w z row]

def disjoin {m} : List (Formula m) → Formula m
  | .nil => .bot
  | .cons p ps => p.disj (disjoin ps)

def node {m} (w row : Fin m) : Formula m := disjoin (patternNodes w row)

def specification {m} (w z row : Fin m) : Formula m := disjoin (patternSpecifications w z row)

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (specification w z row)) := by
  have h0 := LogicalStaticNode.normalized_node_iff hZ 3 false (ObjectLogicalAxiom.rule0.head) (@LogicalRule0Head.normalized) LogicalStaticPatterns.rule0_head_variables (@LogicalRule0Head.head_iff) w z row hw hz
  have h1 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule1.head) (@LogicalRule1Head.normalized) LogicalStaticPatterns.rule1_head_variables (@LogicalRule1Head.head_iff) w z row hw hz
  have h2 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule2.head) (@LogicalRule2Head.normalized) LogicalStaticPatterns.rule2_head_variables (@LogicalRule2Head.head_iff) w z row hw hz
  have h3 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule3.head) (@LogicalRule3Head.normalized) LogicalStaticPatterns.rule3_head_variables (@LogicalRule3Head.head_iff) w z row hw hz
  have h4 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule4.head) (@LogicalRule4Head.normalized) LogicalStaticPatterns.rule4_head_variables (@LogicalRule4Head.head_iff) w z row hw hz
  have h5 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule5.head) (@LogicalRule5Head.normalized) LogicalStaticPatterns.rule5_head_variables (@LogicalRule5Head.head_iff) w z row hw hz
  have h6 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule6.head) (@LogicalRule6Head.normalized) LogicalStaticPatterns.rule6_head_variables (@LogicalRule6Head.head_iff) w z row hw hz
  have h7 := LogicalStaticNode.normalized_node_iff hZ 0 false (ObjectLogicalAxiom.rule7.head) (@LogicalRule7Head.normalized) LogicalStaticPatterns.rule7_head_variables (@LogicalRule7Head.head_iff) w z row hw hz
  have h8 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule8.head) (@LogicalRule8Head.normalized) LogicalStaticPatterns.rule8_head_variables (@LogicalRule8Head.head_iff) w z row hw hz
  have h9 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule9.head) (@LogicalRule9Head.normalized) LogicalStaticPatterns.rule9_head_variables (@LogicalRule9Head.head_iff) w z row hw hz
  have h10 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule10.head) (@LogicalRule10Head.normalized) LogicalStaticPatterns.rule10_head_variables (@LogicalRule10Head.head_iff) w z row hw hz
  have h11 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule11.head) (@LogicalRule11Head.normalized) LogicalStaticPatterns.rule11_head_variables (@LogicalRule11Head.head_iff) w z row hw hz
  have h12 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule12.head) (@LogicalRule12Head.normalized) LogicalStaticPatterns.rule12_head_variables (@LogicalRule12Head.head_iff) w z row hw hz
  have h13 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule13.head) (@LogicalRule13Head.normalized) LogicalStaticPatterns.rule13_head_variables (@LogicalRule13Head.head_iff) w z row hw hz
  have h14 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule14.head) (@LogicalRule14Head.normalized) LogicalStaticPatterns.rule14_head_variables (@LogicalRule14Head.head_iff) w z row hw hz
  have h15 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule15.head) (@LogicalRule15Head.normalized) LogicalStaticPatterns.rule15_head_variables (@LogicalRule15Head.head_iff) w z row hw hz
  have h16 := LogicalStaticNode.normalized_node_iff hZ 3 false (ObjectLogicalAxiom.rule16.head) (@LogicalRule16Head.normalized) LogicalStaticPatterns.rule16_head_variables (@LogicalRule16Head.head_iff) w z row hw hz
  have h17 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule17.head) (@LogicalRule17Head.normalized) LogicalStaticPatterns.rule17_head_variables (@LogicalRule17Head.head_iff) w z row hw hz
  have h18 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule18.head) (@LogicalRule18Head.normalized) LogicalStaticPatterns.rule18_head_variables (@LogicalRule18Head.head_iff) w z row hw hz
  have h19 := LogicalStaticNode.normalized_node_iff hZ 2 false (ObjectLogicalAxiom.rule19.head) (@LogicalRule19Head.normalized) LogicalStaticPatterns.rule19_head_variables (@LogicalRule19Head.head_iff) w z row hw hz
  have h20 := LogicalInstantiateNode.normalized_node4_iff hZ true w z row hw hz
  have h21 := LogicalAbstractNode.normalized_node21_iff hZ w z row hw hz
  have h22 := LogicalStaticNode.normalized_node_iff hZ 1 false (ObjectLogicalAxiom.rule22.head) (@LogicalRule22Head.normalized) LogicalStaticPatterns.rule22_head_variables (@LogicalRule22Head.head_iff) w z row hw hz
  have h23 := LogicalInstantiateNode.normalized_node4_iff hZ false w z row hw hz
  have h24 := LogicalAbstractNode.normalized_node24_iff hZ w z row hw hz
  have h25 := LogicalInstantiateNode.normalized_node6_iff hZ w z row hw hz
  have h26 := LogicalStaticNode.normalized_node_iff hZ 1 true (ObjectLogicalAxiom.rule26.head) (@LogicalRule26Head.normalized) LogicalStaticPatterns.rule26_head_variables (@LogicalRule26Head.head_iff) w z row hw hz
  exact (SyntaxTypeLocalTransfer.disj_congr h0 (SyntaxTypeLocalTransfer.disj_congr h1 (SyntaxTypeLocalTransfer.disj_congr h2 (SyntaxTypeLocalTransfer.disj_congr h3 (SyntaxTypeLocalTransfer.disj_congr h4 (SyntaxTypeLocalTransfer.disj_congr h5 (SyntaxTypeLocalTransfer.disj_congr h6 (SyntaxTypeLocalTransfer.disj_congr h7 (SyntaxTypeLocalTransfer.disj_congr h8 (SyntaxTypeLocalTransfer.disj_congr h9 (SyntaxTypeLocalTransfer.disj_congr h10 (SyntaxTypeLocalTransfer.disj_congr h11 (SyntaxTypeLocalTransfer.disj_congr h12 (SyntaxTypeLocalTransfer.disj_congr h13 (SyntaxTypeLocalTransfer.disj_congr h14 (SyntaxTypeLocalTransfer.disj_congr h15 (SyntaxTypeLocalTransfer.disj_congr h16 (SyntaxTypeLocalTransfer.disj_congr h17 (SyntaxTypeLocalTransfer.disj_congr h18 (SyntaxTypeLocalTransfer.disj_congr h19 (SyntaxTypeLocalTransfer.disj_congr h20 (SyntaxTypeLocalTransfer.disj_congr h21 (SyntaxTypeLocalTransfer.disj_congr h22 (SyntaxTypeLocalTransfer.disj_congr h23 (SyntaxTypeLocalTransfer.disj_congr h24 (SyntaxTypeLocalTransfer.disj_congr h25 (SyntaxTypeLocalTransfer.disj_congr h26 (SyntaxTypeLocalTransfer.iff_refl Formula.bot))))))))))))))))))))))))))))

end PPAC.Migration.Internal.LogicalAllPatterns
