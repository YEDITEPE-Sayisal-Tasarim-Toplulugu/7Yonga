import argparse
import os
import re

file_desen = r"^(?!.*[\*\?])(?:.*/)?[^/]+\.[^/]+$"
dir_desen = r"^(.*\/)\*\.(\w+)$"

def listele_dosyalar(dizin, uzanti):
    """
    SADECE belirtilen dizindeki dosyaları listeler, alt klasörlere girmez.
    
    Args:
        dizin (str): Dizin yolu.
        uzanti (str): '.txt', '.py' gibi dosya uzantısı.

    Returns:
        list: Uygun dosyaların tam yol listesi.
    """
    eslesen_dosyalar = []

    for ad in os.listdir(dizin):
        tam_yol = os.path.join(dizin, ad)
        if os.path.isfile(tam_yol) and ad.endswith(uzanti):
            eslesen_dosyalar.append(tam_yol)

    return eslesen_dosyalar

def readDirDirective(l):
    matchRes = re.match(dir_desen, l)
    if matchRes:
        klasor_yolu, uzanti = matchRes.groups()
        return ([klasor_yolu, uzanti])
    else:
        raise Exception("Eşleşme bulunamadı, dir:"+l)


parser = argparse.ArgumentParser(description='Teknofest ~ Verilator Files generator v1.0')
parser.add_argument('--version', action='version', version='Teknofest ~ Verilator Files generator v1.0')
parser.add_argument('--b', dest='base', type=str, help='base dir')
parser.add_argument('--i', dest='in_file', type=str, help='input file')
parser.add_argument('--o', dest='out_file', type=str, help='output file')

args = parser.parse_args()
base_dir = args.base
in_file = args.in_file
out_file = args.out_file

file = open(in_file, "r")
data = file.readlines()
file.close()

file_list=[]
for f in data:
    f=f.replace("\n","")
    f=base_dir+"/"+f
    if bool(re.match(file_desen, f)):
        file_list.append(f)
    else:
        dirInfo=readDirDirective(f)
        file_list += listele_dosyalar(dirInfo[0],dirInfo[1])

d = []
e = []
for each in file_list:
    if not each in d and not each in e:
        d.append(each)

file = open(out_file, "w")
file.writelines("\n".join(d))
file.close()
