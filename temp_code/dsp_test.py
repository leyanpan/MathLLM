#!/usr/bin/env python3

import subprocess
from pathlib import Path
from pantograph.server import Server
import requests
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

def get_project_and_lean_path():
    cwd = Path(__file__).parent.resolve() / 'MathlibProject'
    p = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd)
    return cwd, p

def next_tactic(self, state):
    tokenized_state = tokenizer(str(state), return_tensors="pt")

    tactic_candidates_ids = model.generate(
    tokenized_state.input_ids,
    max_length=1024,
    num_beams=3,
    length_penalty=0.0,
    do_sample=False,
    num_return_sequences=3,
    early_stopping=False,
    )
    tactic_candidates = tokenizer.batch_decode(
        tactic_candidates_ids, skip_special_tokens=True
    )
    #print(tactic_candidates[0])
    return tactic_candidates[0]





if __name__ == '__main__':
    project_path, lean_path = get_project_and_lean_path()
    print(f"$PWD: {project_path}")
    print(f"$LEAN_PATH: {lean_path}")
    print("Starting Pantograph server...")
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

    response=""
    try: 
        response = requests.get(req)
    except requests.exceptions.RequestException as e:
        print("Network error:", e)

    print("Premise retrieval results:")

    for el in response.json():
        print(el['name'], " | ", el['formal_type'])



    tokenizer = AutoTokenizer.from_pretrained("kaiyuy/leandojo-lean4-tacgen-byt5-small")
    model = AutoModelForSeq2SeqLM.from_pretrained("kaiyuy/leandojo-lean4-tacgen-byt5-small")


    #example tactic gen:
    print(next_tactic(unit1.goals[0]))

