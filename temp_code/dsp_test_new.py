#!/usr/bin/env python3

import subprocess
from pathlib import Path
from pantograph.server import Server, TacticFailure
import requests
import json
#from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
import re
from google import genai
def get_project_and_lean_path():
    cwd = Path(__file__).parent.resolve() / 'MathlibProject'
    p = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd)
    return cwd, p


client = genai.Client(api_key='AIzaSyA4MJWtYBhMQETBpv85m1oq4iXR-Nr0CF8')
model='gemini-2.5-pro-exp-03-25'

def lean_block_to_tac_list(block):
    tac_list=re.search(r'```\s*lean(.*?)```', block, re.DOTALL)
    return tac_list.group(1).strip().split('\n')


def solve_step(state):
    prompt="""You are a Lean 4 expert. Please provide a tactic or sequence of tactics to close the following goal. Output ONLY the tactic(s) separated by newlines inside a code block.

```
{}
```""".format(state)

    response = client.models.generate_content(
        model=model,
        contents=prompt
    )
    #print(prompt)
    return response.text


def repair_step(tac, error):
    prompt="""You are a Lean 4 expert. I am in the middle of a Lean proof. I am trying to prove a goal, but I am running into an error. In the first block I have the tactic I attempted, and in the following block I have the exact error. Please correct the tactic or provide a sequence of corrected tactics to close the goal, given the error. Output ONLY a singular code block containing the valid sequence of tactics to prove the goal.

```lean
{}
```


ERROR:

```
{}
```""".format(tac, error)
    response = client.models.generate_content(
        model=model,
        contents=prompt
    )
    print(prompt)
    return response.text

if __name__ == '__main__':
    project_path, lean_path = get_project_and_lean_path()
    print(f"$PWD: {project_path}")
    print(f"$LEAN_PATH: {lean_path}")
    print("Starting Pantograph server...")
    server = Server(imports=['Mathlib'], project_path=project_path, lean_path=lean_path)  # initialize server


    with open("sketch.sk", "r") as file:   # load sketch
        sketch = file.read()

    unit = server.load_sorry(sketch)[1] # ?idk why [1] is necessary, maybe the `open Real` is a CompilationUnit

    unit1=unit.goal_state

    while unit1.goals:
        attempt_tac=solve_step(unit1.goals[0])

        tac_list = lean_block_to_tac_list(attempt_tac)

        fail_tac=''
        error_msg=''
        for tac in tac_list:
            try : 
                print("trying", tac, "on goal")
                unit1=server.goal_tactic(unit1, goal_id=0, tactic=tac)
                #print("ID: ", unit1.goals[0].id)
                print("success. num goals:", len(unit1.goals))
            except TacticFailure as e:
                fail_tac=tac
                error_msg = e.args[0]['tacticErrors'][0] # just as seen in vscode
                print(fail_tac, "failed with error", error_msg)
                print('breaking out of solve loop')
                break

        #print(fail_tac)
        #print(error_msg)
        if fail_tac:
            for i in range(3): # try 3 repairs
                if '⊢' not in error_msg: # some Lean errors come with the state and some do not
                    state=unit1.goals[0]
                    error_msg+="\n"+str(state)
                    
                rep = repair_step(fail_tac, error_msg)
                print(rep)
                fix_list=lean_block_to_tac_list(rep)
                print(fix_list)
                try : 
                    for tac in fix_list:
                        print("REPAIR:trying", tac, "on goal")
                        unit1=server.goal_tactic(unit1, goal_id=0, tactic=tac)
                        print("REPAIR: success. num goals:", len(unit1.goals))
                except TacticFailure as e:
                    fail_tac=tac
                    error_msg=e.args[0]['tacticErrors'][0]
                    print(e.args[0]['tacticErrors'][0])



                    

        
