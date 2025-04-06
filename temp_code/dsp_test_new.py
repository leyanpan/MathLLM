#!/usr/bin/env python3

import subprocess
from pathlib import Path
from pantograph.server import Server, TacticFailure
import re
from google import genai
import time 
import prompts
def get_project_and_lean_path():
    cwd = Path(__file__).parent.resolve() / 'MathlibProject'
    p = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd)
    return cwd, p


client = genai.Client(api_key='API-KEY')
model='gemini-2.5-pro-exp-03-25'

def lean_block_to_tac_list(block):
    tac_list=re.search(r'```\s*lean(.*?)```', block, re.DOTALL)
    return tac_list.group(1).strip().split('\n')


def solve_step(state):
    prompt=prompts.STATE_TO_TACTIC_PROMPT.format(state)

    response = client.models.generate_content(
        model=model,
        contents=prompt
    )

    return response.text


def repair_step(tac, error):
    prompt = prompts.STATE_AND_ERROR_TO_TACTIC_PROMPT.format(tac, error)

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
    start_time = time.time()

    server = Server(imports=['Mathlib'], project_path=project_path, lean_path=lean_path, timeout=240)  # initialize server


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
                if e.args[0].get('tacticErrors'):
                    error_msg = e.args[0]['tacticErrors'][0] # just as seen in vscode
                    print(fail_tac, "failed with error", error_msg)
                    print('breaking out of solve loop')
                break

        #print(fail_tac)
        #print(error_msg)
        if fail_tac:
            for i in range(3): # try 3 repairs
                if unit1.goals:
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
                        if e.args[0].get('tacticErrors'):
                            error_msg=e.args[0]['tacticErrors'][0]
                            print(fail_tac, "failed with error", error_msg)
                            print("exiting repair")

    
    print("TOTAL TIME: ", time.time()-start_time)
    with open("confirm", "w") as file:   # load sketch
        sketch = file.write(f"Done! latest tactic: {tac}")

                    

        
