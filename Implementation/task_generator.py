from rules import State, Action
from connectives import *
import numpy as np

def generate_formula(complexity):
    # Prepare variables
    Literal.used_tokens = []
    possible_connectives = [And,Or,Xor]
    vertical_complexity = complexity
    horizontal_complexity = (2,4)
    # Generate top level
    top_tokens = {Literal(str(i)) if np.random.randint(2) else Not(Literal(str(i))) for i in range(0,np.random.randint(*horizontal_complexity))}
    formula = np.random.choice(possible_connectives, p=[0.47,0.47,0.06])(*top_tokens)
    if np.random.randint(0,2): 
        formula = np.random.choice([And(formula,Not(formula),formula,Not(formula)),Or(formula,And()), Not(And(formula,Not(formula)))])
    # Generate deeper level
    level = 1
    while vertical_complexity - level:
        tokens_to_replace = {t for t in top_tokens if np.random.randint(3)}
        top_tokens -= tokens_to_replace
        choose_replacements = set(np.random.choice(list(top_tokens),min([len(top_tokens),3]))) | {And,Or,Xor}
        replace_dict = {}
        new_tokens = {Literal(str(i)) if np.random.randint(2) else Not(Literal(str(i))) for i in range(level*horizontal_complexity[1],(level+1)*horizontal_complexity[1])}
        for tr in tokens_to_replace:
            replacement = np.random.choice(list(choose_replacements))
            if isinstance(replacement,type):
                replacement = replacement(*list(np.random.choice(list(new_tokens | top_tokens), np.random.randint(*horizontal_complexity))))
                
            replace_dict[tr] = replacement
        top_tokens |= new_tokens
        Action.recursive_replacement(formula, replace_dict, True)
        level += 1
    return State(Not(formula),Or())
