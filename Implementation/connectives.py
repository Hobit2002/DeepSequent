# Connective
class Connective:
    
    def __eq__(self, __value: object) -> bool:
        return hash(str(self)) == hash(str(__value))
    
# Quantifiers
class Quantifier(Connective):

    def __init__(self,*args,successor = None) -> None:
        self.variables = list(args)
        self.successor = successor

    def addSuccessor(self,successor) -> None:
        self.successor = successor
    
    def __str__(self) -> str:
        # Start with quantifier name
        str_rep = f"{self.__class__.__name__}:"
        # Then list variables bounded by it
        for variable in self.variables:
            str_rep += f"{str(variable)},"
        # Finally add formula successing the quantifier
        str_rep += f":{str(self.successor)}"
        return str_rep
    
    def copy(self) -> Connective:
        return Quantifier(*self.variables,successor = self.successor)
    
    def getBoundedLiterals(self) -> list:
        return self.variables + self.successor.getBoundedLiterals()

class Existential(Quantifier):
    pass

class Universal(Quantifier):
    pass

# Logical gates
class Gate(Connective):

    pass

class Not(Gate):

    def __init__(self,arg) -> None:
        self.operand = arg

    def __str__(self) -> str:
        return f"-({str(self.operand)})"
    
    def copy(self) -> Gate:
        return BinaryGate(self.operand)
        
    def getBoundedLiterals(self) -> list:
        return [] if isinstance(self.operand,Literal) else self.operand.getBoundedLiterals()
        
class BinaryGate(Gate):
    
    def __init__(self,*args) -> None:
        self.operands = list(args)

    def addSuccessor(self,successor) -> None:
        self.operands.append(successor)

    def __str__(self) -> str:
        # Get the gate name
        str_rep = f"{self.__class__.__name__}( "
        # List operands of the gate inside the brackets
        for operand in self.operands:
            str_rep += f"{str(operand)};"
        # Closee the brackets and return the string
        return str_rep[:-1] + " )"
    
    def copy(self) -> Gate:
        return BinaryGate(*self.operands)
    
    def getBoundedLiterals(self) -> list:
        to_return = []
        for operand in self.operands:
            if not isinstance(operand,Literal):to_return += operand.getBoundedLiterals()
        return to_return

class And(BinaryGate):
    pass

class Or(BinaryGate):
    pass

class Xor(BinaryGate):
    pass

# Literal
class Literal():
    
    used_tokens = []

    @staticmethod
    def get_new(skolemn = False):
        # Get last of used tokens and add 'n' to its end
        new_token = Literal.used_tokens[-1] + "n"
        # Add the value among used tokens
        Literal.used_tokens.append(new_token)
        # Create a new literal
        return Literal(new_token,skolemn)

    def __init__(self,token,skolemn = False) -> None:
        # Remove all useless characters from token string
        token = token.replace(",","").replace(")","").replace("-","")
        if "(" in token: token = token[token.index("(")+1:]
        # Set token value
        self.value = token
        # Add token to used tokens
        if token not in Literal.used_tokens: Literal.used_tokens.append(token)
        # Set token skolemn identity
        self.skolemn = skolemn

    def __eq__(self, __value: object) -> bool:
        return hash(str(self)) == hash(str(__value))
        
    def __str__(self) -> str:
        return self.value

    def __hash__(self) -> int:
        return hash(self.value)
