import PPAC.Migration.Internal.ObjectPacketDescent

/-! Exact finite token metadata from the pinned ten-rule Packet table. -/
namespace PPAC.Migration.Internal.PacketTokenRuleData
open YesMetaZFC.Automation
open ObjectHorn

def smallRule : Rule := ObjectPacket.tokenSmall

def largeRule : Rule := ObjectPacket.tokenLarge

theorem actual_rules : rulesFor ObjectPacket.rules 2 = [smallRule,largeRule] := rfl

theorem small_arity : smallRule.arity = 3 := rfl

theorem small_head : smallRule.head = ObjectPacket.node (n := 3) 2 [.var 0,.var 1,.var 2] := rfl

theorem small_guards : smallRule.guards = [(Expr.var (0 : Fin 3),.literal 128)] := rfl

theorem small_premises : smallRule.premises = [ObjectPacket.node (n := 3) 1 [.var 0,.var 1,.var 2]] := rfl

theorem large_arity : largeRule.arity = 6 := rfl

theorem large_head : largeRule.head = ObjectPacket.node (n := 6) 2 [.var 0,.var 1,.var 2] := rfl

theorem large_guards : largeRule.guards = [(Expr.literal (arity := 6) 0,.var (4 : Fin 6)),(.var (3 : Fin 6),.literal 128)] := rfl

theorem large_premises : largeRule.premises =
    [ObjectPacket.node (n := 6) 0 [.var 3,.var 4,.var 0] , ObjectPacket.node 2 [.var 4,.var 1,.var 5] ,
      ObjectPacket.node 1 [ObjectPacket.Expr.addConst 128 (.var 3),.var 5,.var 2]] := rfl

end PPAC.Migration.Internal.PacketTokenRuleData
