"""Shard C quiet study (UNTRUSTED): shared loaders. Reads the certificate model via tocc/classify.py
and the Lean node lists (resetList, islandList, coneList/rootList) by regex."""
import re, sys
sys.path.insert(0, "/tmp/claude-0/tocc")
import classify
L = "/home/user/asyncfpga3/formal/lean/Formal/Net/CViewPS/"
def reset_list():
    s = open(L + "ResetData.lean").read()
    return {int(a): (int(b), c == "true") for a, b, c in re.findall(r"\((\d+), (\d+), (true|false)\)", s)}
def island_list():
    s = open(L + "IslandData.lean").read()
    return {int(a): (c == "true", [int(x) for x in re.findall(r"\d+", ps)])
            for a, c, ps in re.findall(r"\((\d+), (true|false), \[([\d, ]*)\]\)", s)}
def cone_list():
    s = open(L + "BoundaryResetData.lean").read()
    return {int(a): c == "true" for a, c in re.findall(r"\((\d+), (true|false)\)", s)}
