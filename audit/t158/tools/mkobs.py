import sys
src = open(sys.argv[1]).read()
old = '        lines.append("        join")\n'
assert src.count(old) == 1
new = old + ('        for r in results:\n'
             '            if not r.is_control:\n'
             '                lines.append(f\'        $display("OBS %0d %h", {idx}, {bname(r)}_snk.seen[{idx}]);\')\n')
open(sys.argv[2], "w").write(src.replace(old, new))
