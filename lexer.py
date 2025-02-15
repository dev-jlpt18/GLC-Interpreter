# ------------------------------------------------------------
# lexer.py
# Analizador lexicografico para el lenguaje GCL
# Carnet: 15-10345 y 19-10211
# ------------------------------------------------------------
import sys
if ".." not in sys.path: sys.path.insert(0,"..")
import ply.lex as lex
import ply.yacc as yacc

# Lista con los token de las palabras reservadas para GCL
reserved = {
   'declare' : 'TkDeclare',
   'if' : 'TkIf',
   'fi' : 'TkFi',
   'do' : 'TkDo',
   'od' : 'TkOd',
   'for' : 'TkFor',
   'rof' : 'TkRof',
   'int' : 'TkInt',
   'bool' : 'TkBool',
   'array' : 'TkArray',
   'skip' : 'TkSkip',
   'print' : 'TkPrint',
   'ERROR' : 'TkError',
   'false' : 'TkFalse',
   'true'  : 'TkTrue',
   'in'    : 'TkIn',
   'to'    : 'TkTo'
}

# Lista de los nombres de los tokens. Siempre es requerido
tokens = tuple(reserved.values()) + (
   'TkId',
   'TkNum',
   'TkString',
   'TkOBlock',
   'TkCBlock',
   'TkSoForth',
   'TkComma',
   'TkOpenPar',
   'TkClosePar',
   'TkAsig',
   'TkSemicolon',
   'TkArrow',
   'TkGuard',
   'TkPlus',
   'TkMinus',
   'TkMult',
   'TkOr',
   'TkAnd',
   'TkNot',
   'TkLess',
   'TkLeq',
   'TkGeq',
   'TkGreater',
   'TkEqual',
   'TkNEqual',
   'TkOBracket',
   'TkCBracket',
   'TkTwoPoints',
   'TkConcat',
   'TkComent'
) 

# Reglas de las expresiones regulares para cada token

t_TkString = r'\"(\\\"|\\\\|\\n|[^\\\n])*?\"'
t_TkOBlock = r'[|]\['
t_TkCBlock = r'\][|]'
t_TkSoForth = r'\.\.'
t_TkComma = r','
t_TkOpenPar = r'\('
t_TkClosePar = r'\)'
t_TkAsig = r':='
t_TkSemicolon = r';'
t_TkArrow = r'-->'
t_TkGuard = r'\[\]'
t_TkPlus = r'\+'
t_TkMinus = r'-'
t_TkMult = r'\*'
t_TkOr = r'\\/'
t_TkAnd = r'/\\'
t_TkNot = r'\!'
t_TkLess = r'<'
t_TkLeq = r'<='
t_TkGeq = r'>='
t_TkGreater = r'>'
t_TkEqual = r'=='
t_TkNEqual = r'\!='
t_TkOBracket = r'\['
t_TkCBracket = r'\]'
t_TkTwoPoints = r'\:'
t_TkConcat = r'[.]'

# Expresiones regulares que poseeen alguna acción extra

def t_TkId(t):
    r'([a-zA-Z] | _)[a-zA-Z0-9]*(_[a-zA-Z0-9]+)*[_]*' # Identifica si es una variable o una palabra reservada
    t.type = reserved.get(t.value,'TkId')
    return t

def t_TkNum(t):
    r'[0-9][0-9]*[a-zA-Z0-9_]*' # Identifica si es un numero
    try:
        t.value = int(t.value) # En caso de serlo conviertelo a tipo int
        return t
    except:
        t_error(t)         # En caso contrario sitia el tipo del token como ERROR


def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")   # Cuenta las filas del archivo a leer

def t_TkComent(t):
    r'//.*'     # Ignora las oraciones que empiezan con //
    pass

# Manejador de errores
def t_error(t):
    print (f"Error: Unexpected character \"{t.value[0]}\" in row {t.lineno}, column {t.lexpos+1}")
    error.sum()
    t.lexer.skip(1)

# Ignora el tabulador  
t_ignore = ' \t'

# Crear clase que permita contar los errores encontrados
class Error_Counter: 
    def __init__(self, error = 0): 
         self._error = error 
      
    # metodo getter
    def get_value(self): 
        return self._error
    # metodo para aumentar en 1
    def sum(self): 
        self._error = self.get_value() +1
 
# Construye el lexer

lexer = lex.lex(optimize=1, lextab= "compilador")

# Abre el archivo

error = Error_Counter()
'''
try:
    f = open(sys.argv[1], "r")   
    assert f.name.endswith('.gcl') # Verifica que sea un .gcl
    content = f.readlines()
    f.close()
    # Primer analisis, se buscan posibles errores
    for x in content:
        lexer.input(x) # Crear tokens
        while True:
            tok = lexer.token() # Tomar un token
            if not tok: 
                break      # Se acabo la linea

    # En caso de no tener error procedemos a imprimir cada token

    if error.get_value() == 0:
        lexer.lineno = 1
        for x in content:
            lexer.input(x) # Crear tokens
            while True:
                tok = lexer.token() # Tomar un token
                if not tok: 
                    break      # Se acabo la linea
                else:
                    traduccion_lexer.append(tok.type)
                    traduccion_lexer.append(tok.value)
                    if tok.type == 'TkId':
                        print(f"{tok.type}(\"{tok.value}\") {tok.lineno} {tok.lexpos+1}")
                    elif tok.type == 'TkNum' or tok.type == 'TkString':
                        print(f"{tok.type}({tok.value}) {tok.lineno} {tok.lexpos+1}")
                    else:
                        print(f"{tok.type} {tok.lineno} {tok.lexpos+1}")  
except:
    # Caso donde no se consiguio el archivo o no lo indico
    print("Archivo no encontrado o no es de extensión .gcl, indique un archivo para analizar")
'''