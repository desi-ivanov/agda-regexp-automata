# -*- coding: utf-8 -*-
import re

from pygments.lexer import Lexer, RegexLexer, bygroups, do_insertions, \
    default, include, inherit
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation, Generic
from pygments import unistring as uni

__all__ = ['DHaskellLexer', 'DAgdaLexer']


line_re = re.compile('.*?\n')


class DHaskellLexer(RegexLexer):
    name = 'Haskell'
    aliases = ['haskell', 'hs']
    filenames = ['*.hs']
    mimetypes = ['text/x-haskell']

    flags = re.MULTILINE | re.UNICODE

    reserved = ('case', 'class', 'data', 'default', 'deriving', 'do', 'else',
                'family', 'if', 'infix[lr]?', 'instance',
                'let', 'newtype', 'of', 'then', 'type', 'where', '_')
    ascii = ('NUL', 'SOH', '[SE]TX', 'EOT', 'ENQ', 'ACK',
             'BEL', 'BS', 'HT', 'LF', 'VT', 'FF', 'CR', 'S[OI]', 'DLE',
             'DC[1-4]', 'NAK', 'SYN', 'ETB', 'CAN',
             'EM', 'SUB', 'ESC', '[FGRU]S', 'SP', 'DEL')

    tokens = {
        'root': [
            # Whitespace:
            (r'\s+', Text),
            # (r'--\s*|.*$', Comment.Doc),
            (r'--(?![!#$%&*+./<=>?@^|_~:\\]).*?$', Comment.Single),
            (r'\{-', Comment.Multiline, 'comment'),
            # Lexemes:
            #  Identifiers
            (r'\bimport\b', Keyword.Reserved, 'import'),
            (r'\bmodule\b', Keyword.Reserved, 'module'),
            (r'\berror\b', Name.Exception),
            (r'\b(%s)(?!\')\b' % '|'.join(reserved), Keyword.Reserved),
            (r"'[^\\]'", String.Char),  # this has to come before the TH quote
            (r'^[_' + uni.Ll + r'][\w\']*', Name.Function),
            (r"'?[_" + uni.Ll + r"][\w']*", Name),
            (r"('')?[" + uni.Lu + r"][\w\']*", Keyword.Type),
            (r"(')[" + uni.Lu + r"][\w\']*", Keyword.Type),
            (r"(')\[[^\]]*\]", Keyword.Type),  # tuples and lists get special treatment in GHC
            (r"(')\([^)]*\)", Keyword.Type),  # ..
            (r"(')[:!#$%&*+.\\/<=>?@^|~-]+", Keyword.Type),  # promoted type operators
            #  Operators
            (r'\\(?![:!#$%&*+.\\/<=>?@^|~-]+)', Name.Function),  # lambda operator
            (r'(<-|::|->|=>|=)(?![:!#$%&*+.\\/<=>?@^|~-]+)', Operator.Word),  # specials
            (r':[:!#$%&*+.\\/<=>?@^|~-]*', Keyword.Type),  # Constructor operators
            (r'[:!#$%&*+.\\/<=>?@^|~-]+', Operator),  # Other operators
            #  Numbers
            (r'0[xX]_*[\da-fA-F](_*[\da-fA-F])*_*[pP][+-]?\d(_*\d)*', Number.Float),
            (r'0[xX]_*[\da-fA-F](_*[\da-fA-F])*\.[\da-fA-F](_*[\da-fA-F])*'
             r'(_*[pP][+-]?\d(_*\d)*)?', Number.Float),
            (r'\d(_*\d)*_*[eE][+-]?\d(_*\d)*', Number.Float),
            (r'\d(_*\d)*\.\d(_*\d)*(_*[eE][+-]?\d(_*\d)*)?', Number.Float),
            (r'0[bB]_*[01](_*[01])*', Number.Bin),
            (r'0[oO]_*[0-7](_*[0-7])*', Number.Oct),
            (r'0[xX]_*[\da-fA-F](_*[\da-fA-F])*', Number.Hex),
            (r'\d(_*\d)*', Number.Integer),
            #  Character/String Literals
            (r"'", String.Char, 'character'),
            (r'"', String, 'string'),
            #  Special
            (r'\[\]', Keyword.Type),
            (r'\(\)', Name.Builtin),
            (r'[][(),;`{}]', Punctuation),
        ],
        'import': [
            # Import statements
            (r'\s+', Text),
            (r'"', String, 'string'),
            # after "funclist" state
            (r'\)', Punctuation, '#pop'),
            (r'qualified\b', Keyword),
            # import X as Y
            (r'([' + uni.Lu + r'][\w.]*)(\s+)(as)(\s+)([' + uni.Lu + r'][\w.]*)',
             bygroups(Name.Namespace, Text, Keyword, Text, Name), '#pop'),
            # import X hiding (functions)
            (r'([' + uni.Lu + r'][\w.]*)(\s+)(hiding)(\s+)(\()',
             bygroups(Name.Namespace, Text, Keyword, Text, Punctuation), 'funclist'),
            # import X (functions)
            (r'([' + uni.Lu + r'][\w.]*)(\s+)(\()',
             bygroups(Name.Namespace, Text, Punctuation), 'funclist'),
            # import X
            (r'[\w.]+', Name.Namespace, '#pop'),
        ],
        'module': [
            (r'\s+', Text),
            (r'([' + uni.Lu + r'][\w.]*)(\s+)(\()',
             bygroups(Name.Namespace, Text, Punctuation), 'funclist'),
            (r'[' + uni.Lu + r'][\w.]*', Name.Namespace, '#pop'),
        ],
        'funclist': [
            (r'\s+', Text),
            (r'[' + uni.Lu + r']\w*', Keyword.Type),
            (r'(_[\w\']+|[' + uni.Ll + r'][\w\']*)', Name.Function),
            (r'--(?![!#$%&*+./<=>?@^|_~:\\]).*?$', Comment.Single),
            (r'\{-', Comment.Multiline, 'comment'),
            (r',', Punctuation),
            (r'[:!#$%&*+.\\/<=>?@^|~-]+', Operator),
            # (HACK, but it makes sense to push two instances, believe me)
            (r'\(', Punctuation, ('funclist', 'funclist')),
            (r'\)', Punctuation, '#pop:2'),
        ],
        # NOTE: the next four states are shared in the AgdaLexer; make sure
        # any change is compatible with Agda as well or copy over and change
        'comment': [
            # Multiline Comments
            (r'[^-{}]+', Comment.Multiline),
            (r'\{-', Comment.Multiline, '#push'),
            (r'-\}', Comment.Multiline, '#pop'),
            (r'[-{}]', Comment.Multiline),
        ],
        'character': [
            # Allows multi-chars, incorrectly.
            (r"[^\\']'", String.Char, '#pop'),
            (r"\\", String.Escape, 'escape'),
            ("'", String.Char, '#pop'),
        ],
        'string': [
            (r'[^\\"]+', String),
            (r"\\", String.Escape, 'escape'),
            ('"', String, '#pop'),
        ],
        'escape': [
            (r'[abfnrtv"\'&\\]', String.Escape, '#pop'),
            (r'\^[][' + uni.Lu + r'@^_]', String.Escape, '#pop'),
            ('|'.join(ascii), String.Escape, '#pop'),
            (r'o[0-7]+', String.Escape, '#pop'),
            (r'x[\da-fA-F]+', String.Escape, '#pop'),
            (r'\d+', String.Escape, '#pop'),
            (r'\s+\\', String.Escape, '#pop'),
        ],
    }


class DAgdaLexer(RegexLexer):

    name = 'DAgda'
    aliases = ['Dagda']
    filenames = ['*.agda']
    mimetypes = ['text/x-agda']

    reserved = ['abstract', 'codata', 'coinductive', 'constructor', 'data',
                'field', 'forall', 'hiding', 'inductive', 'infix',
                'infixl', 'infixr', 'instance', 'let', 'mutual', 'open',
                'pattern', 'postulate', 'primitive', 'private',
                'quote', 'quoteGoal', 'quoteTerm',
                'record', 'renaming', 'rewrite', 'syntax', 'tactic',
                'unquote', 'unquoteDecl', 'using', 'where', 'with']

    tokens = {
        'root': [
            # Declaration
            (r'^(\s*)([^\s(){}]+)(\s*)(:)(\s*)',
             bygroups(Text, Name.Function, Text, Operator.Word, Text)),
            # Comments
            (r'--(?![!#$%&*+./<=>?@^|_~:\\]).*?$', Comment.Single),
            (r'\{-', Comment.Multiline, 'comment'),
            # Holes
            (r'\{!', Comment.Directive, 'hole'),
            # Lexemes:
            #  Identifiers
            (r'\b(%s)(?!\')\b' % '|'.join(reserved), Keyword.Reserved),
            (r'(import|module)(\s+)', bygroups(Keyword.Reserved, Text), 'module'),
            (u'\\b(Set|Prop)[\u2080-\u2089]*\\b', Keyword.Type),
            #  Special Symbols
            (r'(\(|\)|\{|\})', Operator),
            (u'(\\.{1,3}|\\||\u03BB|\u2200|\u2192|:|=|->)', Operator.Word),
            #  Numbers
            (r'\d+[eE][+-]?\d+', Number.Float),
            (r'\d+\.\d+([eE][+-]?\d+)?', Number.Float),
            (r'0[xX][\da-fA-F]+', Number.Hex),
            (r'\d+', Number.Integer),
            # Strings
            (r"'", String.Char, 'character'),
            (r'"', String, 'string'),
            (r'[^\s(){}]+', Text),
            (r'\s+?', Text),  # Whitespace
        ],
        'hole': [
            # Holes
            (r'[^!{}]+', Comment.Directive),
            (r'\{!', Comment.Directive, '#push'),
            (r'!\}', Comment.Directive, '#pop'),
            (r'[!{}]', Comment.Directive),
        ],
        'module': [
            (r'\{-', Comment.Multiline, 'comment'),
            (r'[a-zA-Z][\w.]*', Name, '#pop'),
            (r'[\W0-9_]+', Text)
        ],
        'comment': DHaskellLexer.tokens['comment'],
        'character': DHaskellLexer.tokens['character'],
        'string': DHaskellLexer.tokens['string'],
        'escape': DHaskellLexer.tokens['escape']
    }
