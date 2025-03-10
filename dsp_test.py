#!/usr/bin/env python3

import subprocess
from pathlib import Path
from pantograph.server import Server
import requests

def get_project_and_lean_path():
    cwd = Path(__file__).parent.resolve() / 'MathlibProject'
    p = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd)
    return cwd, p





if __name__ == '__main__':
    project_path, lean_path = get_project_and_lean_path()
    print(f"$PWD: {project_path}")
    print(f"$LEAN_PATH: {lean_path}")
    server = Server(imports=['Mathlib'], project_path=project_path, lean_path=lean_path)  # initialize server


    with open("examples/sketch.lean", "r") as file:   # load sketch
        sketch = file.read()


    unit = server.load_sorry(sketch)[1] # ?idk why [1] is necessary, maybe the `open Real` is a CompilationUnit
    unit1=server.goal_tactic(unit.goal_state, goal_id=0, tactic='have : Real.log x ≠ 0 := by aesop')
    unit1=server.goal_tactic(unit1, goal_id=0, tactic='exact (div_eq_iff this).mp h1')

    #print(unit)
    i=0
    for goal in unit1.goals:
        print("Goal " + str(i) + ": " + str(goal))
        i+=1
        print("################")

    # retrieval API query
    results=10
    revision="v4.16.0"
    query=unit1.goals[0]

    req="https://premise-search.com/api/search?query={q}&results={n}&rev={rev}".format(q=query, n=results, rev=revision)


    response = requests.get(req)

    for el in response.json():
        print(el['name'], " | ", el['formal_type'])