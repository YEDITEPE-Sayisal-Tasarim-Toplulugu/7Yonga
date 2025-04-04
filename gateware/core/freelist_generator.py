

file = open("files.f", "r")
data = file.readline()
file.close()

c = data.split(" ")
d = []
e = [
        "cv32e40p/bhv/insn_trace.sv",
        "cv32e40p/bhv/pipe_freeze_trace.sv"
    ]
for each in c:
    if not each in d and not each in e:
        if "pkg" in each:
            d.insert(3, each)
        else:
            d.append(each)
        
file = open("files2.f", "w")
file.writelines("\n".join(d))
file.close()
