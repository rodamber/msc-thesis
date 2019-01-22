import jsonlines

data_conversion_funs = [
    'BooleanToInteger', 'BooleanToText', 'DateTimeToDate', 'DateTimeToText',
    'DateTimeToTime', 'DateToDateTime', 'DateToText', 'DecimalToBoolean',
    'DecimalToInteger', 'DecimalToIntegerValidate', 'DecimalToLongInteger',
    'DecimalToLongIntegerValidate', 'DecimalToText', 'LongIntegerToInteger',
    'LongIntegerToIntegerValidate', 'LongIntegerToIdentifier',
    'LongIntegerToText', 'IdentifierToInteger', 'IdentifierToLongInteger',
    'IdentifierToText', 'IntegerToBoolean', 'IntegerToDecimal',
    'IntegerToIdentifier', 'IntegerToText', 'NullDate', 'NullIdentifier',
    'NullObject', 'NullBinary', 'NullTextIdentifier', 'TextToDate',
    'TextToDateTime', 'TextToDateTimeValidate', 'TextToDateValidate',
    'TextToDecimal', 'TextToDecimalValidate', 'TextToIdentifier',
    'TextToInteger', 'TextToLongInteger', 'TextToIntegerValidate',
    'TextToLongIntegerValidate', 'TextToTime', 'TextToTimeValidate',
    'TimeToText', 'ToObject'
]
date_and_time_funs = [
    'AddDays', 'AddHours', 'AddMinutes', 'AddMonths', 'AddSeconds', 'AddYears',
    'BuildDateTime', 'CurrDate', 'CurrDateTime', 'CurrTime', 'Day',
    'DayOfWeek', 'DiffDays', 'DiffHours', 'DiffMinutes', 'DiffSeconds', 'Hour',
    'Minute', 'Month', 'NewDate', 'NewDateTime', 'NewTime', 'Second', 'Year'
]
email_funs = [
    'EmailAddressCreate', 'EmailAddressesConcatenate', 'EmailAddressValidate'
]
environments_funs = [
    'GetApplicationServerType', 'GetCurrentLocale', 'GetDatabaseProvider',
    'GetUserAgent', 'GetOwnerEspaceIdentifier', 'GetEntryEspaceName',
    'GetEntryEspaceId', 'GetObsoleteTenantId'
]
format_funs = [
    'FormatDecimal', 'FormatPercent', 'FormatPhoneNumber', 'FormatText',
    'FormatDateTime'
]
math_funs = [
    'Abs',
    'Mod',
    'Power',
    'Round',
    'Sqrt',
    'Trunc',
]
misc_funs = [
    'GeneratePassword', 'If', 'IsLoadingScreen', 'CurrentThemeIsMobile'
]
numeric_funs = ['Max', 'Min', 'Sign']
roles_funs = ['CheckRole', 'GetUserId']
text_funs = [
    'Chr', 'Concat', 'EncodeHtml', 'EncodeJavaScript', 'EncodeSql',
    'EncodeUrl', 'Index', 'Length', 'NewLine', 'Replace', 'Substr', 'ToLower',
    'ToUpper', 'Trim', 'TrimEnd', 'TrimStart'
]
url_funs = [
    'AddPersonalAreaToURLPath', 'GetBookmarkableURL', 'GetPersonalAreaName',
    'GetOwnerURLPath', 'GetExceptionURL'
]

builtin_funs = set(data_conversion_funs + date_and_time_funs + email_funs +
                   environments_funs + format_funs + math_funs + misc_funs +
                   numeric_funs + roles_funs + text_funs + url_funs)
builtin_types = set([
    'BinaryData', 'Boolean', 'Currency', 'Date', 'Time', 'DateTime', 'Integer',
    'LongInteger', 'Decimal', 'Email', 'PhoneNumber', 'Text', 'Identifier'
])


class Expr:
    "Represents an outsystems expression."

    def __init__(self, expr_key, funs, oml_key, refs, text, type_):
        self.expr_key = expr_key
        self.funs = funs
        self.oml_key = oml_key
        self.refs = refs
        self.text = text
        self.type = type_


def expressions(filename='../data/exprs.jsonl'):
    with jsonlines.open(filename) as reader:
        for obj in reader:
            yield Expr(obj['exprKey'], obj['functions'], obj['omlKey'],
                       obj['refs'], obj['text'], obj['type'])
