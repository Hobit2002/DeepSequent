from connectives import *
from rules import State

def parse(file_dir):
# Open file with formula and read it 
    file = open(file_dir)
    line = file.readline()

    # Check the format
    if line[:5] != "#QCIR": raise ValueError("Given file seems not to containt formula in QCIR format")
    line = file.readline()

    # Start looping through the lines of the file
    mode = "prenex"
    formula = And() # Initialize the formula
    bottom_formula = formula # Create a variable pointing to the formula which should be expanded
    formula_dict = {}
    while line != "":
        tokens = line.split()
        # Parse quantifiers in the following way:
        # 1. get list of their literals
        # 2. create new formula
        # 3. set this formula as a successor of the current bottom formula
        # 4. redirect bottom formula to this new formula
        if mode == "prenex":
            if "exists" in tokens[0]:
                new_formula = Existential(*[Literal(token) for token in tokens])
                bottom_formula.addSuccessor(new_formula)
                bottom_formula = new_formula
            elif "forall" in tokens[0]:
                new_formula = Universal(*[Literal(token) for token in tokens])
                bottom_formula.addSuccessor(new_formula)
                bottom_formula = new_formula
            # Once the output line is reached, switch to post-prenex mode and store identifier of the topmost formula
            elif "output" in tokens[0]:
                stop_literal = Literal(tokens[0])
                mode = "post-prenex"
        else:
            variable = Literal(tokens[0])
            gate = tokens[2]
            successors = []
            # Parse connective operands
            for token in tokens[2:]:
                if "()" in token:continue
                # If the operand variable is a placeholder for another formula, use that formula
                if Literal(token) in formula_dict.keys():
                    new_successor = formula_dict[Literal(token)]
                    Literal.used_tokens.remove(Literal(token).value)
                # Otherwise use just the variable name
                else:
                    new_successor = Literal(token)
                # If the operand is negated, put the created literal object into a negation
                if "-" in token:
                    new_successor = Not(new_successor)
                successors.append(new_successor)
            # Check connectives and create the appropriate one
            if "exists" in tokens[0]:
                new_formula = Existential(*successors[:-1],successor=successors[-1])
            elif "forall" in tokens[0]:
                new_formula = Universal(*successors[:-1],successor=successors[-1])
            elif "and" in gate:
                new_formula = And(*successors)
            elif "xor" in gate:
                new_formula = Xor(*successors)
            elif "or" in gate:
                new_formula = Or(*successors)
            # If the variable matches the output one, create a proof tree with recently created formula as its root
            if variable == stop_literal:
                bottom_formula.addSuccessor(new_formula)
                Literal.used_tokens.remove(stop_literal.value)
                return State(Not(formula.operands[0]),Or())
            # Otherwise save the variable as a placeholder for its formula
            else:
                formula_dict[variable] = new_formula
        line = file.readline()
    else:
        raise ValueError("Output variable was not introduced")


    
