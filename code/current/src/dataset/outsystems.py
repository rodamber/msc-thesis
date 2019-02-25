import jsonlines
from enum import Enum

DataConversionFuns = Enum('DataConversionFuns', [
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
])
DateAndTimeFuns = Enum('DateAndTimeFuns', [
    'AddDays', 'AddHours', 'AddMinutes', 'AddMonths', 'AddSeconds', 'AddYears',
    'BuildDateTime', 'CurrDate', 'CurrDateTime', 'CurrTime', 'Day',
    'DayOfWeek', 'DiffDays', 'DiffHours', 'DiffMinutes', 'DiffSeconds', 'Hour',
    'Minute', 'Month', 'NewDate', 'NewDateTime', 'NewTime', 'Second', 'Year'
])
EmailFuns = Enum('EmailFuns', [
    'EmailAddressCreate', 'EmailAddressesConcatenate', 'EmailAddressValidate'
])
EnvironmentsFuns = Enum('EnvironmentsFuns', [
    'GetApplicationServerType', 'GetCurrentLocale', 'GetDatabaseProvider',
    'GetUserAgent', 'GetOwnerEspaceIdentifier', 'GetEntryEspaceName',
    'GetEntryEspaceId', 'GetObsoleteTenantId'
])
FormatFuns = Enum('FormatFuns', [
    'FormatDecimal', 'FormatPercent', 'FormatPhoneNumber', 'FormatText',
    'FormatDateTime'
])
MathFuns = Enum('MathFuns', [
    'Abs',
    'Mod',
    'Power',
    'Round',
    'Sqrt',
    'Trunc',
])
MiscFuns = Enum(
    'MiscFuns',
    ['GeneratePassword', 'If', 'IsLoadingScreen', 'CurrentThemeIsMobile'])
NumericFuns = Enum('NumericFuns', ['Max', 'Min', 'Sign'])
RolesFuns = Enum('RolesFuns', ['CheckRole', 'GetUserId'])
TextFuns = Enum('TextFuns', [
    'Chr', 'Concat', 'EncodeHtml', 'EncodeJavaScript', 'EncodeSql',
    'EncodeUrl', 'Index', 'Length', 'NewLine', 'Replace', 'Substr', 'ToLower',
    'ToUpper', 'Trim', 'TrimEnd', 'TrimStart'
])
UrlFuns = Enum('UrlFuns', [
    'AddPersonalAreaToURLPath', 'GetBookmarkableURL', 'GetPersonalAreaName',
    'GetOwnerURLPath', 'GetExceptionURL'
])

# BuiltinFuns = set(data_conversion_funs + date_and_time_funs + email_funs +
#                    environments_funs + format_funs + math_funs + misc_funs +
#                    numeric_funs + roles_funs + text_funs + url_funs)
# builtin_types = set([
#     'BinaryData', 'Boolean', 'Currency', 'Date', 'Time', 'DateTime', 'Integer',
#     'LongInteger', 'Decimal', 'Email', 'PhoneNumber', 'Text', 'Identifier'
# ])


class Expr:
    "Represents an outsystems expression."

    def __init__(self, funs, text, type_):
        self.funs = funs
        self.text = text
        self.type = type_


def expressions(filename='../../dataset/exprs-3-6.jsonl'):
    with jsonlines.open(filename) as reader:
        for obj in reader:
            yield Expr(obj['functions'], obj['text'], obj['type'])
