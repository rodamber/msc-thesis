from lark import Lark

parser = Lark(open('outsystems.lark'))

test = "FormatText(FormatDecimal(IntegerToDecimal(AuditList.List.Current.AUDIT.Duration)/1000-60*Trunc(AuditList.List.Current.AUDIT.Duration/60000),3,\".\",\" \"),6,6,True,\"0\")"
print(parser.parse(test).pretty())
