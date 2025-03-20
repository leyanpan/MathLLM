#!/usr/bin/env python3

import subprocess
from pathlib import Path
from pantograph.server import Server
import requests
from pantograph.expr import (
    parse_expr,
    Expr,
    Variable,
    Goal,
    GoalState,
    Tactic,
    TacticHave,
    TacticLet,
    TacticCalc,
    TacticExpr,
    TacticDraft,
)

def get_project_and_lean_path():
    cwd = Path(__file__).parent.resolve() / 'MathlibProject'
    p = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd)
    return cwd, p





if __name__ == '__main__':
    project_path, lean_path = get_project_and_lean_path()
    print(f"$PWD: {project_path}")
    print(f"$LEAN_PATH: {lean_path}")
    server = Server(imports=['Mathlib'], project_path=project_path, lean_path=lean_path, timeout=300)  # initialize server

    print("Server start successful")

    with open("examples/sketch.lean", "r") as file:   # load sketch
        sketch = file.read()

    # Strip all Lean comments before loading
    # First strip multi-line comments (/-...-/)
    import re
    sketch_stripped = re.sub(r'/\-[\s\S]*?\-/', '', sketch)
    # Then strip single-line comments (--...)
    sketch_stripped = '\n'.join([line.split('--')[0] for line in sketch_stripped.split('\n')])

    unit = server.load_sorry(sketch_stripped)[1] # ?idk why [1] is necessary, maybe the `open Real` is a CompilationUnit
    goal_state = unit.goal_state
    # This creates a new goal with the "have" statement
    # unit1 = server.goal_tactic(unit.goal_state, goal_id=0, tactic=TacticHave('Real.log w = 24 * Real.log x', 'hlnw'))
    goal_state=server.goal_tactic(goal_state, goal_id=0, tactic='have : Real.log x ≠ 0 := by aesop')
    goal_state=server.goal_tactic(goal_state, goal_id=0, tactic='exact (div_eq_iff this).mp h1')

    #print(unit)
    i=0
    for goal in goal_state.goals:
        print("Goal " + str(i) + ": " + str(goal))
        i+=1
        print("################")

    # retrieval API query
    results=10
    revision="v4.16.0"
    query=goal_state.goals[0]

    req="https://premise-search.com/api/search?query={q}&results={n}&rev={rev}".format(q=query, n=results, rev=revision)


    response = requests.get(req)

    for el in response.json():
        print(el['name'], " | ", el['formal_type'])
