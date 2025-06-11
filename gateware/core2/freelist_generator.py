import argparse

parser = argparse.ArgumentParser(description='Teknofest ~ Verilator Files generator v1.0')
parser.add_argument('--version', action='version', version='Teknofest ~ Verilator Files generator v1.0')
parser.add_argument('--i', dest='in_file', type=str, help='input file')
parser.add_argument('--o', dest='out_file', type=str, help='output file')

args = parser.parse_args()
in_file = args.in_file
out_file = args.out_file

file = open(in_file, "r")
data = file.readline()
file.close()

c = data.split(" ")
d = []
e = []
for each in c:
    if not each in d and not each in e:
        if "pkg" in each:
            d.insert(3, each)
        else:
            d.append(each)

file = open(out_file, "w")
file.writelines("\n".join(d))
file.close()
